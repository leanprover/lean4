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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapForallTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_Linter_isDeprecated(lean_object*, lean_object*);
uint8_t l_Lean_Name_isMetaprogramming(lean_object*);
lean_object* l_Lean_AsyncConstantInfo_toConstantVal(lean_object*);
lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withSuppressedMessages___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
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
static const lean_ctor_object l_Lean_Meta_LibrarySearch_grindDischarger___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*14 + 32, .m_other = 14, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1)),((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(10000) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1048576) << 1) | 1)),((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 0, 1, 0, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 1, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 1, 0, 1, 1)}};
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_LibrarySearch_solveByElim___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_LibrarySearch_solveByElim___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_LibrarySearch_solveByElim___closed__0 = (const lean_object*)&l_Lean_Meta_LibrarySearch_solveByElim___closed__0_value;
static const lean_closure_object l_Lean_Meta_LibrarySearch_solveByElim___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_LibrarySearch_solveByElim___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_LibrarySearch_solveByElim___closed__1 = (const lean_object*)&l_Lean_Meta_LibrarySearch_solveByElim___closed__1_value;
static const lean_closure_object l_Lean_Meta_LibrarySearch_solveByElim___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_LibrarySearch_solveByElim___lam__2___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_3971__boxed_226_; uint8_t v_res_227_; lean_object* v_r_228_; 
v___x_3971__boxed_226_ = lean_unbox(v___x_224_);
v_res_227_ = l_Lean_Meta_LibrarySearch_tryDischarger___lam__1(v___x_3971__boxed_226_, v_x_225_);
lean_dec(v_x_225_);
v_r_228_ = lean_box(v_res_227_);
return v_r_228_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_tryDischarger___closed__11(void){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l_Array_mkArray0(lean_box(0));
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
v_ref_314_ = lean_ctor_get(v_a_268_, 5);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(lean_object* v_msgData_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v___x_372_; lean_object* v_env_373_; lean_object* v___x_374_; lean_object* v_mctx_375_; lean_object* v_lctx_376_; lean_object* v_options_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_372_ = lean_st_ref_get(v___y_370_);
v_env_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc_ref(v_env_373_);
lean_dec(v___x_372_);
v___x_374_ = lean_st_ref_get(v___y_368_);
v_mctx_375_ = lean_ctor_get(v___x_374_, 0);
lean_inc_ref(v_mctx_375_);
lean_dec(v___x_374_);
v_lctx_376_ = lean_ctor_get(v___y_367_, 2);
v_options_377_ = lean_ctor_get(v___y_369_, 2);
lean_inc_ref(v_options_377_);
lean_inc_ref(v_lctx_376_);
v___x_378_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_378_, 0, v_env_373_);
lean_ctor_set(v___x_378_, 1, v_mctx_375_);
lean_ctor_set(v___x_378_, 2, v_lctx_376_);
lean_ctor_set(v___x_378_, 3, v_options_377_);
v___x_379_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
lean_ctor_set(v___x_379_, 1, v_msgData_366_);
v___x_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0___boxed(lean_object* v_msgData_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(v_msgData_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(lean_object* v_msg_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v_ref_394_; lean_object* v___x_395_; lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_404_; 
v_ref_394_ = lean_ctor_get(v___y_391_, 5);
v___x_395_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(v_msg_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
v_a_396_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_404_ == 0)
{
v___x_398_ = v___x_395_;
v_isShared_399_ = v_isSharedCheck_404_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_395_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_404_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_400_; lean_object* v___x_402_; 
lean_inc(v_ref_394_);
v___x_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_400_, 0, v_ref_394_);
lean_ctor_set(v___x_400_, 1, v_a_396_);
if (v_isShared_399_ == 0)
{
lean_ctor_set_tag(v___x_398_, 1);
lean_ctor_set(v___x_398_, 0, v___x_400_);
v___x_402_ = v___x_398_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_400_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg___boxed(lean_object* v_msg_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v_msg_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
return v_res_411_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__0));
v___x_414_ = l_Lean_stringToMessageData(v___x_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__0(lean_object* v_x_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1);
v___x_422_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_421_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__0___boxed(lean_object* v_x_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_Meta_LibrarySearch_solveByElim___lam__0(v_x_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v_x_423_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__1(lean_object* v_x_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
uint8_t v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = 0;
v___x_437_ = lean_box(v___x_436_);
v___x_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__1___boxed(lean_object* v_x_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_Meta_LibrarySearch_solveByElim___lam__1(v_x_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v_x_439_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__2(lean_object* v_x_446_, lean_object* v_x_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_box(0);
v___x_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__2___boxed(lean_object* v_x_455_, lean_object* v_x_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_Meta_LibrarySearch_solveByElim___lam__2(v_x_455_, v_x_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v_x_456_);
lean_dec(v_x_455_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim(lean_object* v_required_470_, uint8_t v_exfalso_471_, lean_object* v_goals_472_, lean_object* v_maxDepth_473_, uint8_t v_grind_474_, uint8_t v_try_x3f_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v___x_481_; uint8_t v_transparency_482_; lean_object* v___f_483_; lean_object* v___f_484_; lean_object* v___f_485_; uint8_t v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; lean_object* v___y_490_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_481_ = l_Lean_Meta_Context_config(v_a_476_);
v_transparency_482_ = lean_ctor_get_uint8(v___x_481_, 9);
lean_dec_ref(v___x_481_);
v___f_483_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__0));
v___f_484_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__1));
v___f_485_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__2));
v___x_486_ = 1;
v___x_487_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_487_, 0, v_maxDepth_473_);
lean_ctor_set(v___x_487_, 1, v___f_485_);
lean_ctor_set(v___x_487_, 2, v___f_484_);
lean_ctor_set(v___x_487_, 3, v___f_483_);
lean_ctor_set_uint8(v___x_487_, sizeof(void*)*4, v___x_486_);
v___x_488_ = 0;
v___x_509_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_grindDischarger___closed__3));
v___x_510_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_510_, 0, v___x_487_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
lean_ctor_set_uint8(v___x_510_, sizeof(void*)*2, v_transparency_482_);
lean_ctor_set_uint8(v___x_510_, sizeof(void*)*2 + 1, v___x_486_);
lean_ctor_set_uint8(v___x_510_, sizeof(void*)*2 + 2, v_exfalso_471_);
v___x_511_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_511_, 0, v___x_510_);
lean_ctor_set_uint8(v___x_511_, sizeof(void*)*1, v___x_486_);
lean_ctor_set_uint8(v___x_511_, sizeof(void*)*1 + 1, v___x_486_);
lean_ctor_set_uint8(v___x_511_, sizeof(void*)*1 + 2, v___x_488_);
lean_ctor_set_uint8(v___x_511_, sizeof(void*)*1 + 3, v___x_488_);
if (v_try_x3f_475_ == 0)
{
if (v_grind_474_ == 0)
{
v___y_490_ = v___x_511_;
goto v___jp_489_;
}
else
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__4));
v___x_513_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v___x_511_, v___x_512_);
v___y_490_ = v___x_513_;
goto v___jp_489_;
}
}
else
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__5));
v___x_515_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v___x_511_, v___x_514_);
v___y_490_ = v___x_515_;
goto v___jp_489_;
}
v___jp_489_:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_491_ = lean_box(0);
v___x_492_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__3));
v___x_493_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v___x_488_, v___x_488_, v___x_491_, v___x_491_, v___x_492_, v_a_476_, v_a_477_, v_a_478_, v_a_479_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v_fst_495_; lean_object* v_snd_496_; uint8_t v___x_497_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_a_494_);
lean_dec_ref_known(v___x_493_, 1);
v_fst_495_ = lean_ctor_get(v_a_494_, 0);
lean_inc(v_fst_495_);
v_snd_496_ = lean_ctor_get(v_a_494_, 1);
lean_inc(v_snd_496_);
lean_dec(v_a_494_);
v___x_497_ = l_List_isEmpty___redArg(v_required_470_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(v___y_490_, v_required_470_);
v___x_499_ = l_Lean_Meta_SolveByElim_solveByElim(v___x_498_, v_fst_495_, v_snd_496_, v_goals_472_, v_a_476_, v_a_477_, v_a_478_, v_a_479_);
return v___x_499_;
}
else
{
lean_object* v___x_500_; 
lean_dec(v_required_470_);
v___x_500_ = l_Lean_Meta_SolveByElim_solveByElim(v___y_490_, v_fst_495_, v_snd_496_, v_goals_472_, v_a_476_, v_a_477_, v_a_478_, v_a_479_);
return v___x_500_;
}
}
else
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
lean_dec_ref(v___y_490_);
lean_dec(v_goals_472_);
lean_dec(v_required_470_);
v_a_501_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_508_ == 0)
{
v___x_503_ = v___x_493_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_493_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_501_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___boxed(lean_object* v_required_516_, lean_object* v_exfalso_517_, lean_object* v_goals_518_, lean_object* v_maxDepth_519_, lean_object* v_grind_520_, lean_object* v_try_x3f_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_){
_start:
{
uint8_t v_exfalso_boxed_527_; uint8_t v_grind_boxed_528_; uint8_t v_try_x3f_boxed_529_; lean_object* v_res_530_; 
v_exfalso_boxed_527_ = lean_unbox(v_exfalso_517_);
v_grind_boxed_528_ = lean_unbox(v_grind_520_);
v_try_x3f_boxed_529_ = lean_unbox(v_try_x3f_521_);
v_res_530_ = l_Lean_Meta_LibrarySearch_solveByElim(v_required_516_, v_exfalso_boxed_527_, v_goals_518_, v_maxDepth_519_, v_grind_boxed_528_, v_try_x3f_boxed_529_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
lean_dec(v_a_525_);
lean_dec_ref(v_a_524_);
lean_dec(v_a_523_);
lean_dec_ref(v_a_522_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0(lean_object* v_00_u03b1_531_, lean_object* v_msg_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v_msg_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___boxed(lean_object* v_00_u03b1_539_, lean_object* v_msg_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0(v_00_u03b1_539_, v_msg_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(uint8_t v_x_547_){
_start:
{
switch(v_x_547_)
{
case 0:
{
lean_object* v___x_548_; 
v___x_548_ = lean_unsigned_to_nat(0u);
return v___x_548_;
}
case 1:
{
lean_object* v___x_549_; 
v___x_549_ = lean_unsigned_to_nat(1u);
return v___x_549_;
}
default: 
{
lean_object* v___x_550_; 
v___x_550_ = lean_unsigned_to_nat(2u);
return v___x_550_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx___boxed(lean_object* v_x_551_){
_start:
{
uint8_t v_x_boxed_552_; lean_object* v_res_553_; 
v_x_boxed_552_ = lean_unbox(v_x_551_);
v_res_553_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(v_x_boxed_552_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___redArg(lean_object* v_k_554_){
_start:
{
lean_inc(v_k_554_);
return v_k_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___redArg___boxed(lean_object* v_k_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___redArg(v_k_555_);
lean_dec(v_k_555_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim(lean_object* v_motive_557_, lean_object* v_ctorIdx_558_, uint8_t v_t_559_, lean_object* v_h_560_, lean_object* v_k_561_){
_start:
{
lean_inc(v_k_561_);
return v_k_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___boxed(lean_object* v_motive_562_, lean_object* v_ctorIdx_563_, lean_object* v_t_564_, lean_object* v_h_565_, lean_object* v_k_566_){
_start:
{
uint8_t v_t_boxed_567_; lean_object* v_res_568_; 
v_t_boxed_567_ = lean_unbox(v_t_564_);
v_res_568_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorElim(v_motive_562_, v_ctorIdx_563_, v_t_boxed_567_, v_h_565_, v_k_566_);
lean_dec(v_k_566_);
lean_dec(v_ctorIdx_563_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim___redArg(lean_object* v_none_569_){
_start:
{
lean_inc(v_none_569_);
return v_none_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim___redArg___boxed(lean_object* v_none_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_Meta_LibrarySearch_DeclMod_none_elim___redArg(v_none_570_);
lean_dec(v_none_570_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim(lean_object* v_motive_572_, uint8_t v_t_573_, lean_object* v_h_574_, lean_object* v_none_575_){
_start:
{
lean_inc(v_none_575_);
return v_none_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim___boxed(lean_object* v_motive_576_, lean_object* v_t_577_, lean_object* v_h_578_, lean_object* v_none_579_){
_start:
{
uint8_t v_t_boxed_580_; lean_object* v_res_581_; 
v_t_boxed_580_ = lean_unbox(v_t_577_);
v_res_581_ = l_Lean_Meta_LibrarySearch_DeclMod_none_elim(v_motive_576_, v_t_boxed_580_, v_h_578_, v_none_579_);
lean_dec(v_none_579_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___redArg(lean_object* v_mp_582_){
_start:
{
lean_inc(v_mp_582_);
return v_mp_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___redArg___boxed(lean_object* v_mp_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___redArg(v_mp_583_);
lean_dec(v_mp_583_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim(lean_object* v_motive_585_, uint8_t v_t_586_, lean_object* v_h_587_, lean_object* v_mp_588_){
_start:
{
lean_inc(v_mp_588_);
return v_mp_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___boxed(lean_object* v_motive_589_, lean_object* v_t_590_, lean_object* v_h_591_, lean_object* v_mp_592_){
_start:
{
uint8_t v_t_boxed_593_; lean_object* v_res_594_; 
v_t_boxed_593_ = lean_unbox(v_t_590_);
v_res_594_ = l_Lean_Meta_LibrarySearch_DeclMod_mp_elim(v_motive_589_, v_t_boxed_593_, v_h_591_, v_mp_592_);
lean_dec(v_mp_592_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___redArg(lean_object* v_mpr_595_){
_start:
{
lean_inc(v_mpr_595_);
return v_mpr_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___redArg___boxed(lean_object* v_mpr_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___redArg(v_mpr_596_);
lean_dec(v_mpr_596_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim(lean_object* v_motive_598_, uint8_t v_t_599_, lean_object* v_h_600_, lean_object* v_mpr_601_){
_start:
{
lean_inc(v_mpr_601_);
return v_mpr_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___boxed(lean_object* v_motive_602_, lean_object* v_t_603_, lean_object* v_h_604_, lean_object* v_mpr_605_){
_start:
{
uint8_t v_t_boxed_606_; lean_object* v_res_607_; 
v_t_boxed_606_ = lean_unbox(v_t_603_);
v_res_607_ = l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim(v_motive_602_, v_t_boxed_606_, v_h_604_, v_mpr_605_);
lean_dec(v_mpr_605_);
return v_res_607_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_DeclMod_ofNat(lean_object* v_n_608_){
_start:
{
lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_609_ = lean_unsigned_to_nat(0u);
v___x_610_ = lean_nat_dec_le(v_n_608_, v___x_609_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_611_ = lean_unsigned_to_nat(1u);
v___x_612_ = lean_nat_dec_le(v_n_608_, v___x_611_);
if (v___x_612_ == 0)
{
uint8_t v___x_613_; 
v___x_613_ = 2;
return v___x_613_;
}
else
{
uint8_t v___x_614_; 
v___x_614_ = 1;
return v___x_614_;
}
}
else
{
uint8_t v___x_615_; 
v___x_615_ = 0;
return v___x_615_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ofNat___boxed(lean_object* v_n_616_){
_start:
{
uint8_t v_res_617_; lean_object* v_r_618_; 
v_res_617_ = l_Lean_Meta_LibrarySearch_DeclMod_ofNat(v_n_616_);
lean_dec(v_n_616_);
v_r_618_ = lean_box(v_res_617_);
return v_r_618_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_instDecidableEqDeclMod(uint8_t v_x_619_, uint8_t v_y_620_){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_621_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(v_x_619_);
v___x_622_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(v_y_620_);
v___x_623_ = lean_nat_dec_eq(v___x_621_, v___x_622_);
lean_dec(v___x_622_);
lean_dec(v___x_621_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_instDecidableEqDeclMod___boxed(lean_object* v_x_624_, lean_object* v_y_625_){
_start:
{
uint8_t v_x_13__boxed_626_; uint8_t v_y_14__boxed_627_; uint8_t v_res_628_; lean_object* v_r_629_; 
v_x_13__boxed_626_ = lean_unbox(v_x_624_);
v_y_14__boxed_627_ = lean_unbox(v_y_625_);
v_res_628_ = l_Lean_Meta_LibrarySearch_instDecidableEqDeclMod(v_x_13__boxed_626_, v_y_14__boxed_627_);
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
lean_object* v___x_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_634_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(v_x_632_);
v___x_635_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(v_y_633_);
v___x_636_ = lean_nat_dec_lt(v___x_634_, v___x_635_);
if (v___x_636_ == 0)
{
uint8_t v___x_637_; 
v___x_637_ = lean_nat_dec_eq(v___x_634_, v___x_635_);
lean_dec(v___x_635_);
lean_dec(v___x_634_);
if (v___x_637_ == 0)
{
uint8_t v___x_638_; 
v___x_638_ = 2;
return v___x_638_;
}
else
{
uint8_t v___x_639_; 
v___x_639_ = 1;
return v___x_639_;
}
}
else
{
uint8_t v___x_640_; 
lean_dec(v___x_635_);
lean_dec(v___x_634_);
v___x_640_ = 0;
return v___x_640_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_instOrdDeclMod_ord___boxed(lean_object* v_x_641_, lean_object* v_y_642_){
_start:
{
uint8_t v_x_30__boxed_643_; uint8_t v_y_31__boxed_644_; uint8_t v_res_645_; lean_object* v_r_646_; 
v_x_30__boxed_643_ = lean_unbox(v_x_641_);
v_y_31__boxed_644_ = lean_unbox(v_y_642_);
v_res_645_ = l_Lean_Meta_LibrarySearch_instOrdDeclMod_ord(v_x_30__boxed_643_, v_y_31__boxed_644_);
v_r_646_ = lean_box(v_res_645_);
return v_r_646_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_LibrarySearch_instHashableDeclMod_hash(uint8_t v_x_649_){
_start:
{
switch(v_x_649_)
{
case 0:
{
uint64_t v___x_650_; 
v___x_650_ = 0ULL;
return v___x_650_;
}
case 1:
{
uint64_t v___x_651_; 
v___x_651_ = 1ULL;
return v___x_651_;
}
default: 
{
uint64_t v___x_652_; 
v___x_652_ = 2ULL;
return v___x_652_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_instHashableDeclMod_hash___boxed(lean_object* v_x_653_){
_start:
{
uint8_t v_x_40__boxed_654_; uint64_t v_res_655_; lean_object* v_r_656_; 
v_x_40__boxed_654_ = lean_unbox(v_x_653_);
v_res_655_ = l_Lean_Meta_LibrarySearch_instHashableDeclMod_hash(v_x_40__boxed_654_);
v_r_656_ = lean_box_uint64(v_res_655_);
return v_r_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0(lean_object* v_k_659_, lean_object* v_b_660_, lean_object* v_c_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v___x_667_; 
lean_inc(v___y_665_);
lean_inc_ref(v___y_664_);
lean_inc(v___y_663_);
lean_inc_ref(v___y_662_);
v___x_667_ = lean_apply_7(v_k_659_, v_b_660_, v_c_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, lean_box(0));
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0___boxed(lean_object* v_k_668_, lean_object* v_b_669_, lean_object* v_c_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0(v_k_668_, v_b_669_, v_c_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(lean_object* v_type_677_, lean_object* v_k_678_, uint8_t v_cleanupAnnotations_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v___f_685_; uint8_t v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___f_685_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_685_, 0, v_k_678_);
v___x_686_ = 0;
v___x_687_ = lean_box(0);
v___x_688_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_686_, v___x_687_, v_type_677_, v___f_685_, v_cleanupAnnotations_679_, v___x_686_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_688_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_688_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
v_a_697_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_688_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_688_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___boxed(lean_object* v_type_705_, lean_object* v_k_706_, lean_object* v_cleanupAnnotations_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_713_; lean_object* v_res_714_; 
v_cleanupAnnotations_boxed_713_ = lean_unbox(v_cleanupAnnotations_707_);
v_res_714_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(v_type_705_, v_k_706_, v_cleanupAnnotations_boxed_713_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0(lean_object* v_00_u03b1_715_, lean_object* v_type_716_, lean_object* v_k_717_, uint8_t v_cleanupAnnotations_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(v_type_716_, v_k_717_, v_cleanupAnnotations_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___boxed(lean_object* v_00_u03b1_725_, lean_object* v_type_726_, lean_object* v_k_727_, lean_object* v_cleanupAnnotations_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_734_; lean_object* v_res_735_; 
v_cleanupAnnotations_boxed_734_ = lean_unbox(v_cleanupAnnotations_728_);
v_res_735_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0(v_00_u03b1_725_, v_type_726_, v_k_727_, v_cleanupAnnotations_boxed_734_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0(lean_object* v_name_742_, lean_object* v_x_743_, lean_object* v_type_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
uint8_t v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_750_ = 0;
v___x_751_ = lean_box(v___x_750_);
lean_inc(v_name_742_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v_name_742_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_type_744_, v___x_752_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_803_; 
v_a_754_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_803_ == 0)
{
v___x_756_ = v___x_753_;
v_isShared_757_ = v_isSharedCheck_803_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_753_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_803_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v_key_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; uint8_t v___x_763_; 
v_key_758_ = lean_ctor_get(v_a_754_, 0);
v___x_759_ = lean_unsigned_to_nat(1u);
v___x_760_ = lean_mk_empty_array_with_capacity(v___x_759_);
lean_inc(v_a_754_);
v___x_761_ = lean_array_push(v___x_760_, v_a_754_);
v___x_762_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__2));
v___x_763_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_758_, v___x_762_);
if (v___x_763_ == 0)
{
lean_object* v___x_765_; 
lean_dec(v_a_754_);
lean_dec(v_name_742_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v___x_761_);
v___x_765_ = v___x_756_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v___x_761_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
else
{
lean_object* v___x_767_; uint8_t v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
lean_del_object(v___x_756_);
v___x_767_ = lean_unsigned_to_nat(0u);
v___x_768_ = 1;
v___x_769_ = lean_box(v___x_768_);
lean_inc(v_name_742_);
v___x_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_770_, 0, v_name_742_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
lean_inc(v_a_754_);
v___x_771_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_a_754_, v___x_767_, v___x_770_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; uint8_t v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_a_772_);
lean_dec_ref_known(v___x_771_, 1);
v___x_773_ = 2;
v___x_774_ = lean_box(v___x_773_);
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v_name_742_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
v___x_776_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_a_754_, v___x_759_, v___x_775_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_786_; 
v_a_777_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_786_ == 0)
{
v___x_779_ = v___x_776_;
v_isShared_780_ = v_isSharedCheck_786_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_776_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_786_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_781_ = lean_array_push(v___x_761_, v_a_772_);
v___x_782_ = lean_array_push(v___x_781_, v_a_777_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v___x_782_);
v___x_784_ = v___x_779_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec(v_a_772_);
lean_dec_ref(v___x_761_);
v_a_787_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_776_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_776_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec_ref(v___x_761_);
lean_dec(v_a_754_);
lean_dec(v_name_742_);
v_a_795_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_771_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_771_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
}
}
else
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec(v_name_742_);
v_a_804_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_753_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_753_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___boxed(lean_object* v_name_812_, lean_object* v_x_813_, lean_object* v_type_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0(v_name_812_, v_x_813_, v_type_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec_ref(v_x_813_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport(lean_object* v_name_823_, lean_object* v_c_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
lean_object* v___x_830_; lean_object* v_env_831_; uint8_t v___x_832_; 
v___x_830_ = lean_st_ref_get(v_a_828_);
v_env_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc_ref(v_env_831_);
lean_dec(v___x_830_);
lean_inc(v_name_823_);
v___x_832_ = l_Lean_Linter_isDeprecated(v_env_831_, v_name_823_);
if (v___x_832_ == 0)
{
uint8_t v___x_833_; 
lean_inc(v_name_823_);
v___x_833_ = l_Lean_Name_isMetaprogramming(v_name_823_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; lean_object* v_type_835_; lean_object* v___f_836_; lean_object* v___x_837_; 
v___x_834_ = l_Lean_AsyncConstantInfo_toConstantVal(v_c_824_);
v_type_835_ = lean_ctor_get(v___x_834_, 2);
lean_inc_ref(v_type_835_);
lean_dec_ref(v___x_834_);
v___f_836_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___boxed), 8, 1);
lean_closure_set(v___f_836_, 0, v_name_823_);
v___x_837_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(v_type_835_, v___f_836_, v___x_833_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
return v___x_837_;
}
else
{
lean_object* v___x_838_; lean_object* v___x_839_; 
lean_dec_ref(v_c_824_);
lean_dec(v_name_823_);
v___x_838_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___closed__0));
v___x_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
return v___x_839_;
}
}
else
{
lean_object* v___x_840_; lean_object* v___x_841_; 
lean_dec_ref(v_c_824_);
lean_dec(v_name_823_);
v___x_840_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___closed__0));
v___x_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
return v___x_841_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___boxed(lean_object* v_name_842_, lean_object* v_c_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport(v_name_842_, v_c_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_);
lean_dec(v_a_847_);
lean_dec_ref(v_a_846_);
lean_dec(v_a_845_);
lean_dec_ref(v_a_844_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_858108106____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_851_ = lean_box(0);
v___x_852_ = lean_st_mk_ref(v___x_851_);
v___x_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_858108106____hygCtx___hyg_2____boxed(lean_object* v_a_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_858108106____hygCtx___hyg_2_();
return v_res_855_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_constantsPerImportTask(void){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = lean_unsigned_to_nat(6500u);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2955776588____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_883_ = lean_box(0);
v___x_884_ = lean_st_mk_ref(v___x_883_);
v___x_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2955776588____hygCtx___hyg_2____boxed(lean_object* v_a_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2955776588____hygCtx___hyg_2_();
return v_res_887_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__1(void){
_start:
{
lean_object* v_droppedRef_889_; lean_object* v___x_890_; 
v_droppedRef_889_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_starLemmasExt;
v___x_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_890_, 0, v_droppedRef_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_libSearchFindDecls(lean_object* v_ty_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_897_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_ext;
v___x_898_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__0));
v___x_899_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_droppedKeys));
v___x_900_ = lean_unsigned_to_nat(6500u);
v___x_901_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__1, &l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__1_once, _init_l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__1);
v___x_902_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v___x_897_, v___x_898_, v___x_899_, v___x_900_, v___x_901_, v_ty_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_libSearchFindDecls___boxed(lean_object* v_ty_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lean_Meta_LibrarySearch_libSearchFindDecls(v_ty_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
lean_dec(v_a_907_);
lean_dec_ref(v_a_906_);
lean_dec(v_a_905_);
lean_dec_ref(v_a_904_);
return v_res_909_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_913_ = lean_box(0);
v___x_914_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_getStarLemmas___closed__1));
v___x_915_ = l_Lean_mkConst(v___x_914_, v___x_913_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_getStarLemmas(lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_){
_start:
{
lean_object* v_ref_923_; lean_object* v___x_924_; 
v_ref_923_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_starLemmasExt;
v___x_924_ = lean_st_ref_get(v_ref_923_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2, &l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2_once, _init_l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2);
v___x_926_ = l_Lean_Meta_LibrarySearch_libSearchFindDecls(v___x_925_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_939_; 
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_939_ == 0)
{
lean_object* v_unused_940_; 
v_unused_940_ = lean_ctor_get(v___x_926_, 0);
lean_dec(v_unused_940_);
v___x_928_ = v___x_926_;
v_isShared_929_ = v_isSharedCheck_939_;
goto v_resetjp_927_;
}
else
{
lean_dec(v___x_926_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_939_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_930_; 
v___x_930_ = lean_st_ref_get(v_ref_923_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v___x_931_; lean_object* v___x_933_; 
v___x_931_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_getStarLemmas___closed__3));
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 0, v___x_931_);
v___x_933_ = v___x_928_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_931_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
else
{
lean_object* v_val_935_; lean_object* v___x_937_; 
v_val_935_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_val_935_);
lean_dec_ref_known(v___x_930_, 1);
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 0, v_val_935_);
v___x_937_ = v___x_928_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_val_935_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
else
{
return v___x_926_;
}
}
else
{
lean_object* v_val_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
v_val_941_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_924_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_val_941_);
lean_dec(v___x_924_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
lean_ctor_set_tag(v___x_943_, 0);
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_val_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_getStarLemmas___boxed(lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v_a_949_, v_a_950_, v_a_951_, v_a_952_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0(uint8_t v___x_955_, lean_object* v___x_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
if (v___x_955_ == 0)
{
lean_object* v___x_962_; 
v___x_962_ = l_Lean_getRemainingHeartbeats___redArg(v___y_959_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_972_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_972_ == 0)
{
v___x_965_ = v___x_962_;
v_isShared_966_ = v_isSharedCheck_972_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_962_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_972_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
uint8_t v___x_967_; lean_object* v___x_968_; lean_object* v___x_970_; 
v___x_967_ = lean_nat_dec_lt(v_a_963_, v___x_956_);
lean_dec(v_a_963_);
v___x_968_ = lean_box(v___x_967_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 0, v___x_968_);
v___x_970_ = v___x_965_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_968_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
v_a_973_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_962_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_962_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
else
{
uint8_t v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_981_ = 0;
v___x_982_ = lean_box(v___x_981_);
v___x_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
return v___x_983_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0___boxed(lean_object* v___x_984_, lean_object* v___x_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
uint8_t v___x_643__boxed_991_; lean_object* v_res_992_; 
v___x_643__boxed_991_ = lean_unbox(v___x_984_);
v_res_992_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0(v___x_643__boxed_991_, v___x_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___x_985_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(lean_object* v_leavePercent_993_, lean_object* v_a_994_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l_Lean_getMaxHeartbeats___redArg(v_a_994_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_998_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
lean_inc(v_a_997_);
lean_dec_ref_known(v___x_996_, 1);
v___x_998_ = l_Lean_getRemainingHeartbeats___redArg(v_a_994_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1013_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1001_ = v___x_998_;
v_isShared_1002_ = v_isSharedCheck_1013_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_998_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1013_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; lean_object* v___x_1008_; lean_object* v___y_1009_; lean_object* v___x_1011_; 
v___x_1003_ = lean_nat_mul(v_a_999_, v_leavePercent_993_);
lean_dec(v_a_999_);
v___x_1004_ = lean_unsigned_to_nat(100u);
v___x_1005_ = lean_nat_div(v___x_1003_, v___x_1004_);
lean_dec(v___x_1003_);
v___x_1006_ = lean_unsigned_to_nat(0u);
v___x_1007_ = lean_nat_dec_eq(v_a_997_, v___x_1006_);
lean_dec(v_a_997_);
v___x_1008_ = lean_box(v___x_1007_);
v___y_1009_ = lean_alloc_closure((void*)(l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___y_1009_, 0, v___x_1008_);
lean_closure_set(v___y_1009_, 1, v___x_1005_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v___y_1009_);
v___x_1011_ = v___x_1001_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___y_1009_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
lean_dec(v_a_997_);
v_a_1014_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_998_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_998_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
v_a_1022_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_996_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_996_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___boxed(lean_object* v_leavePercent_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercent_1030_, v_a_1031_);
lean_dec_ref(v_a_1031_);
lean_dec(v_leavePercent_1030_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck(lean_object* v_leavePercent_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercent_1034_, v_a_1037_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___boxed(lean_object* v_leavePercent_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck(v_leavePercent_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_);
lean_dec(v_a_1045_);
lean_dec_ref(v_a_1044_);
lean_dec(v_a_1043_);
lean_dec_ref(v_a_1042_);
lean_dec(v_leavePercent_1041_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(lean_object* v_upperBound_1048_, lean_object* v_x_1049_, lean_object* v_f_1050_, lean_object* v_y_1051_, lean_object* v_g_1052_, lean_object* v_a_1053_, lean_object* v_b_1054_){
_start:
{
uint8_t v___x_1055_; 
v___x_1055_ = lean_nat_dec_lt(v_a_1053_, v_upperBound_1048_);
if (v___x_1055_ == 0)
{
lean_dec(v_a_1053_);
lean_dec(v_g_1052_);
lean_dec(v_f_1050_);
return v_b_1054_;
}
else
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1056_ = lean_array_fget_borrowed(v_x_1049_, v_a_1053_);
lean_inc(v_f_1050_);
lean_inc(v___x_1056_);
v___x_1057_ = lean_apply_1(v_f_1050_, v___x_1056_);
v___x_1058_ = lean_array_push(v_b_1054_, v___x_1057_);
v___x_1059_ = lean_array_fget_borrowed(v_y_1051_, v_a_1053_);
lean_inc(v_g_1052_);
lean_inc(v___x_1059_);
v___x_1060_ = lean_apply_1(v_g_1052_, v___x_1059_);
v___x_1061_ = lean_array_push(v___x_1058_, v___x_1060_);
v___x_1062_ = lean_unsigned_to_nat(1u);
v___x_1063_ = lean_nat_add(v_a_1053_, v___x_1062_);
lean_dec(v_a_1053_);
v_a_1053_ = v___x_1063_;
v_b_1054_ = v___x_1061_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg___boxed(lean_object* v_upperBound_1065_, lean_object* v_x_1066_, lean_object* v_f_1067_, lean_object* v_y_1068_, lean_object* v_g_1069_, lean_object* v_a_1070_, lean_object* v_b_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(v_upperBound_1065_, v_x_1066_, v_f_1067_, v_y_1068_, v_g_1069_, v_a_1070_, v_b_1071_);
lean_dec_ref(v_y_1068_);
lean_dec_ref(v_x_1066_);
lean_dec(v_upperBound_1065_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(lean_object* v_g_1073_, size_t v_sz_1074_, size_t v_i_1075_, lean_object* v_bs_1076_){
_start:
{
uint8_t v___x_1077_; 
v___x_1077_ = lean_usize_dec_lt(v_i_1075_, v_sz_1074_);
if (v___x_1077_ == 0)
{
lean_dec(v_g_1073_);
return v_bs_1076_;
}
else
{
lean_object* v_v_1078_; lean_object* v___x_1079_; lean_object* v_bs_x27_1080_; lean_object* v___x_1081_; size_t v___x_1082_; size_t v___x_1083_; lean_object* v___x_1084_; 
v_v_1078_ = lean_array_uget(v_bs_1076_, v_i_1075_);
v___x_1079_ = lean_unsigned_to_nat(0u);
v_bs_x27_1080_ = lean_array_uset(v_bs_1076_, v_i_1075_, v___x_1079_);
lean_inc(v_g_1073_);
v___x_1081_ = lean_apply_1(v_g_1073_, v_v_1078_);
v___x_1082_ = ((size_t)1ULL);
v___x_1083_ = lean_usize_add(v_i_1075_, v___x_1082_);
v___x_1084_ = lean_array_uset(v_bs_x27_1080_, v_i_1075_, v___x_1081_);
v_i_1075_ = v___x_1083_;
v_bs_1076_ = v___x_1084_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg___boxed(lean_object* v_g_1086_, lean_object* v_sz_1087_, lean_object* v_i_1088_, lean_object* v_bs_1089_){
_start:
{
size_t v_sz_boxed_1090_; size_t v_i_boxed_1091_; lean_object* v_res_1092_; 
v_sz_boxed_1090_ = lean_unbox_usize(v_sz_1087_);
lean_dec(v_sz_1087_);
v_i_boxed_1091_ = lean_unbox_usize(v_i_1088_);
lean_dec(v_i_1088_);
v_res_1092_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_g_1086_, v_sz_boxed_1090_, v_i_boxed_1091_, v_bs_1089_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith___redArg(lean_object* v_f_1093_, lean_object* v_x_1094_, lean_object* v_g_1095_, lean_object* v_y_1096_){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v_res_1100_; lean_object* v___y_1102_; uint8_t v___x_1116_; 
v___x_1097_ = lean_array_get_size(v_x_1094_);
v___x_1098_ = lean_array_get_size(v_y_1096_);
v___x_1099_ = lean_nat_add(v___x_1097_, v___x_1098_);
v_res_1100_ = lean_mk_empty_array_with_capacity(v___x_1099_);
lean_dec(v___x_1099_);
v___x_1116_ = lean_nat_dec_le(v___x_1097_, v___x_1098_);
if (v___x_1116_ == 0)
{
v___y_1102_ = v___x_1098_;
goto v___jp_1101_;
}
else
{
v___y_1102_ = v___x_1097_;
goto v___jp_1101_;
}
v___jp_1101_:
{
uint8_t v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1103_ = lean_nat_dec_lt(v___y_1102_, v___x_1097_);
v___x_1104_ = lean_unsigned_to_nat(0u);
lean_inc(v_g_1095_);
lean_inc(v_f_1093_);
v___x_1105_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(v___y_1102_, v_x_1094_, v_f_1093_, v_y_1096_, v_g_1095_, v___x_1104_, v_res_1100_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1106_; size_t v_sz_1107_; size_t v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
lean_dec(v_f_1093_);
v___x_1106_ = l_Array_extract___redArg(v_y_1096_, v___y_1102_, v___x_1098_);
v_sz_1107_ = lean_array_size(v___x_1106_);
v___x_1108_ = ((size_t)0ULL);
v___x_1109_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_g_1095_, v_sz_1107_, v___x_1108_, v___x_1106_);
v___x_1110_ = l_Array_append___redArg(v___x_1105_, v___x_1109_);
lean_dec_ref(v___x_1109_);
return v___x_1110_;
}
else
{
lean_object* v___x_1111_; size_t v_sz_1112_; size_t v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
lean_dec(v_g_1095_);
v___x_1111_ = l_Array_extract___redArg(v_x_1094_, v___y_1102_, v___x_1097_);
v_sz_1112_ = lean_array_size(v___x_1111_);
v___x_1113_ = ((size_t)0ULL);
v___x_1114_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_f_1093_, v_sz_1112_, v___x_1113_, v___x_1111_);
v___x_1115_ = l_Array_append___redArg(v___x_1105_, v___x_1114_);
lean_dec_ref(v___x_1114_);
return v___x_1115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith___redArg___boxed(lean_object* v_f_1117_, lean_object* v_x_1118_, lean_object* v_g_1119_, lean_object* v_y_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Lean_Meta_LibrarySearch_interleaveWith___redArg(v_f_1117_, v_x_1118_, v_g_1119_, v_y_1120_);
lean_dec_ref(v_y_1120_);
lean_dec_ref(v_x_1118_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith(lean_object* v_00_u03b1_1122_, lean_object* v_00_u03b2_1123_, lean_object* v_00_u03b3_1124_, lean_object* v_f_1125_, lean_object* v_x_1126_, lean_object* v_g_1127_, lean_object* v_y_1128_){
_start:
{
lean_object* v___x_1129_; 
v___x_1129_ = l_Lean_Meta_LibrarySearch_interleaveWith___redArg(v_f_1125_, v_x_1126_, v_g_1127_, v_y_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith___boxed(lean_object* v_00_u03b1_1130_, lean_object* v_00_u03b2_1131_, lean_object* v_00_u03b3_1132_, lean_object* v_f_1133_, lean_object* v_x_1134_, lean_object* v_g_1135_, lean_object* v_y_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Lean_Meta_LibrarySearch_interleaveWith(v_00_u03b1_1130_, v_00_u03b2_1131_, v_00_u03b3_1132_, v_f_1133_, v_x_1134_, v_g_1135_, v_y_1136_);
lean_dec_ref(v_y_1136_);
lean_dec_ref(v_x_1134_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0(lean_object* v_00_u03b2_1138_, lean_object* v_00_u03b3_1139_, lean_object* v_g_1140_, size_t v_sz_1141_, size_t v_i_1142_, lean_object* v_bs_1143_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_g_1140_, v_sz_1141_, v_i_1142_, v_bs_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___boxed(lean_object* v_00_u03b2_1145_, lean_object* v_00_u03b3_1146_, lean_object* v_g_1147_, lean_object* v_sz_1148_, lean_object* v_i_1149_, lean_object* v_bs_1150_){
_start:
{
size_t v_sz_boxed_1151_; size_t v_i_boxed_1152_; lean_object* v_res_1153_; 
v_sz_boxed_1151_ = lean_unbox_usize(v_sz_1148_);
lean_dec(v_sz_1148_);
v_i_boxed_1152_ = lean_unbox_usize(v_i_1149_);
lean_dec(v_i_1149_);
v_res_1153_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0(v_00_u03b2_1145_, v_00_u03b3_1146_, v_g_1147_, v_sz_boxed_1151_, v_i_boxed_1152_, v_bs_1150_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1(lean_object* v_00_u03b3_1154_, lean_object* v_upperBound_1155_, lean_object* v_00_u03b1_1156_, lean_object* v_x_1157_, lean_object* v_f_1158_, lean_object* v_00_u03b2_1159_, lean_object* v_y_1160_, lean_object* v_g_1161_, lean_object* v_inst_1162_, lean_object* v_R_1163_, lean_object* v_a_1164_, lean_object* v_b_1165_, lean_object* v_c_1166_){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(v_upperBound_1155_, v_x_1157_, v_f_1158_, v_y_1160_, v_g_1161_, v_a_1164_, v_b_1165_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___boxed(lean_object* v_00_u03b3_1168_, lean_object* v_upperBound_1169_, lean_object* v_00_u03b1_1170_, lean_object* v_x_1171_, lean_object* v_f_1172_, lean_object* v_00_u03b2_1173_, lean_object* v_y_1174_, lean_object* v_g_1175_, lean_object* v_inst_1176_, lean_object* v_R_1177_, lean_object* v_a_1178_, lean_object* v_b_1179_, lean_object* v_c_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1(v_00_u03b3_1168_, v_upperBound_1169_, v_00_u03b1_1170_, v_x_1171_, v_f_1172_, v_00_u03b2_1173_, v_y_1174_, v_g_1175_, v_inst_1176_, v_R_1177_, v_a_1178_, v_b_1179_, v_c_1180_);
lean_dec_ref(v_y_1174_);
lean_dec_ref(v_x_1171_);
lean_dec(v_upperBound_1169_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_));
v___x_1190_ = l_Lean_registerInternalExceptionId(v___x_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2____boxed(lean_object* v_a_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_();
return v_res_1192_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0(void){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1193_ = lean_box(0);
v___x_1194_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_abortSpeculationId;
v___x_1195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
lean_ctor_set(v___x_1195_, 1, v___x_1193_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___redArg(lean_object* v_inst_1196_){
_start:
{
lean_object* v_throw_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v_throw_1197_ = lean_ctor_get(v_inst_1196_, 0);
lean_inc(v_throw_1197_);
lean_dec_ref(v_inst_1196_);
v___x_1198_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0, &l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0_once, _init_l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0);
v___x_1199_ = lean_apply_2(v_throw_1197_, lean_box(0), v___x_1198_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation(lean_object* v_m_1200_, lean_object* v_00_u03b1_1201_, lean_object* v_inst_1202_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Lean_Meta_LibrarySearch_abortSpeculation___redArg(v_inst_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_isAbortSpeculation(lean_object* v_x_1204_){
_start:
{
if (lean_obj_tag(v_x_1204_) == 1)
{
lean_object* v_id_1205_; lean_object* v___x_1206_; uint8_t v___x_1207_; 
v_id_1205_ = lean_ctor_get(v_x_1204_, 0);
v___x_1206_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_abortSpeculationId;
v___x_1207_ = l_Lean_instBEqInternalExceptionId_beq(v_id_1205_, v___x_1206_);
return v___x_1207_;
}
else
{
uint8_t v___x_1208_; 
v___x_1208_ = 0;
return v___x_1208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_isAbortSpeculation___boxed(lean_object* v_x_1209_){
_start:
{
uint8_t v_res_1210_; lean_object* v_r_1211_; 
v_res_1210_ = l_Lean_Meta_LibrarySearch_isAbortSpeculation(v_x_1209_);
lean_dec_ref(v_x_1209_);
v_r_1211_ = lean_box(v_res_1210_);
return v_r_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(lean_object* v_x_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Lean_Meta_saveState___redArg(v___y_1214_, v___y_1216_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; lean_object* v___x_1220_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
lean_inc(v_a_1219_);
lean_dec_ref_known(v___x_1218_, 1);
lean_inc(v___y_1216_);
lean_inc_ref(v___y_1215_);
lean_inc(v___y_1214_);
lean_inc_ref(v___y_1213_);
v___x_1220_ = lean_apply_5(v_x_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, lean_box(0));
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1229_; 
lean_dec(v_a_1219_);
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1223_ = v___x_1220_;
v_isShared_1224_ = v_isSharedCheck_1229_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1220_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1229_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1225_; lean_object* v___x_1227_; 
v___x_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1225_, 0, v_a_1221_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 0, v___x_1225_);
v___x_1227_ = v___x_1223_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1225_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
else
{
lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1259_; 
v_a_1230_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1232_ = v___x_1220_;
v_isShared_1233_ = v_isSharedCheck_1259_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_1220_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1259_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
uint8_t v___y_1235_; uint8_t v___x_1257_; 
v___x_1257_ = l_Lean_Exception_isInterrupt(v_a_1230_);
if (v___x_1257_ == 0)
{
uint8_t v___x_1258_; 
lean_inc(v_a_1230_);
v___x_1258_ = l_Lean_Exception_isRuntime(v_a_1230_);
v___y_1235_ = v___x_1258_;
goto v___jp_1234_;
}
else
{
v___y_1235_ = v___x_1257_;
goto v___jp_1234_;
}
v___jp_1234_:
{
if (v___y_1235_ == 0)
{
lean_object* v___x_1236_; 
lean_del_object(v___x_1232_);
lean_dec(v_a_1230_);
v___x_1236_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1219_, v___y_1214_, v___y_1216_);
lean_dec(v_a_1219_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1244_; 
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1244_ == 0)
{
lean_object* v_unused_1245_; 
v_unused_1245_ = lean_ctor_get(v___x_1236_, 0);
lean_dec(v_unused_1245_);
v___x_1238_ = v___x_1236_;
v_isShared_1239_ = v_isSharedCheck_1244_;
goto v_resetjp_1237_;
}
else
{
lean_dec(v___x_1236_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1244_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1240_; lean_object* v___x_1242_; 
v___x_1240_ = lean_box(0);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v___x_1240_);
v___x_1242_ = v___x_1238_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___x_1240_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
v_a_1246_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v___x_1236_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1236_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
else
{
lean_object* v___x_1255_; 
lean_dec(v_a_1219_);
if (v_isShared_1233_ == 0)
{
v___x_1255_ = v___x_1232_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1230_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
}
}
else
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1267_; 
lean_dec_ref(v_x_1212_);
v_a_1260_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1262_ = v___x_1218_;
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1218_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1263_ == 0)
{
v___x_1265_ = v___x_1262_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_a_1260_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg___boxed(lean_object* v_x_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(v_x_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0(lean_object* v_00_u03b1_1275_, lean_object* v_x_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(v_x_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___boxed(lean_object* v_00_u03b1_1283_, lean_object* v_x_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0(v_00_u03b1_1283_, v_x_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(lean_object* v_e_1291_, lean_object* v___y_1292_){
_start:
{
uint8_t v___x_1294_; 
v___x_1294_ = l_Lean_Expr_hasMVar(v_e_1291_);
if (v___x_1294_ == 0)
{
lean_object* v___x_1295_; 
v___x_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1295_, 0, v_e_1291_);
return v___x_1295_;
}
else
{
lean_object* v___x_1296_; lean_object* v_mctx_1297_; lean_object* v___x_1298_; lean_object* v_fst_1299_; lean_object* v_snd_1300_; lean_object* v___x_1301_; lean_object* v_cache_1302_; lean_object* v_zetaDeltaFVarIds_1303_; lean_object* v_postponed_1304_; lean_object* v_diag_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1314_; 
v___x_1296_ = lean_st_ref_get(v___y_1292_);
v_mctx_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc_ref(v_mctx_1297_);
lean_dec(v___x_1296_);
v___x_1298_ = l_Lean_instantiateMVarsCore(v_mctx_1297_, v_e_1291_);
v_fst_1299_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_fst_1299_);
v_snd_1300_ = lean_ctor_get(v___x_1298_, 1);
lean_inc(v_snd_1300_);
lean_dec_ref(v___x_1298_);
v___x_1301_ = lean_st_ref_take(v___y_1292_);
v_cache_1302_ = lean_ctor_get(v___x_1301_, 1);
v_zetaDeltaFVarIds_1303_ = lean_ctor_get(v___x_1301_, 2);
v_postponed_1304_ = lean_ctor_get(v___x_1301_, 3);
v_diag_1305_ = lean_ctor_get(v___x_1301_, 4);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1314_ == 0)
{
lean_object* v_unused_1315_; 
v_unused_1315_ = lean_ctor_get(v___x_1301_, 0);
lean_dec(v_unused_1315_);
v___x_1307_ = v___x_1301_;
v_isShared_1308_ = v_isSharedCheck_1314_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_diag_1305_);
lean_inc(v_postponed_1304_);
lean_inc(v_zetaDeltaFVarIds_1303_);
lean_inc(v_cache_1302_);
lean_dec(v___x_1301_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1314_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 0, v_snd_1300_);
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_snd_1300_);
lean_ctor_set(v_reuseFailAlloc_1313_, 1, v_cache_1302_);
lean_ctor_set(v_reuseFailAlloc_1313_, 2, v_zetaDeltaFVarIds_1303_);
lean_ctor_set(v_reuseFailAlloc_1313_, 3, v_postponed_1304_);
lean_ctor_set(v_reuseFailAlloc_1313_, 4, v_diag_1305_);
v___x_1310_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = lean_st_ref_set(v___y_1292_, v___x_1310_);
v___x_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1312_, 0, v_fst_1299_);
return v___x_1312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg___boxed(lean_object* v_e_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(v_e_1316_, v___y_1317_);
lean_dec(v___y_1317_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1(lean_object* v_e_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v___x_1326_; 
v___x_1326_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(v_e_1320_, v___y_1322_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___boxed(lean_object* v_e_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1(v_e_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0(lean_object* v___x_1334_, lean_object* v_x_1335_){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1334_);
lean_ctor_set(v___x_1336_, 1, v_x_1335_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(lean_object* v___x_1337_, size_t v_sz_1338_, size_t v_i_1339_, lean_object* v_bs_1340_){
_start:
{
uint8_t v___x_1341_; 
v___x_1341_ = lean_usize_dec_lt(v_i_1339_, v_sz_1338_);
if (v___x_1341_ == 0)
{
lean_dec_ref(v___x_1337_);
return v_bs_1340_;
}
else
{
lean_object* v_v_1342_; lean_object* v___x_1343_; lean_object* v_bs_x27_1344_; lean_object* v___x_1345_; size_t v___x_1346_; size_t v___x_1347_; lean_object* v___x_1348_; 
v_v_1342_ = lean_array_uget(v_bs_1340_, v_i_1339_);
v___x_1343_ = lean_unsigned_to_nat(0u);
v_bs_x27_1344_ = lean_array_uset(v_bs_1340_, v_i_1339_, v___x_1343_);
lean_inc_ref(v___x_1337_);
v___x_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1337_);
lean_ctor_set(v___x_1345_, 1, v_v_1342_);
v___x_1346_ = ((size_t)1ULL);
v___x_1347_ = lean_usize_add(v_i_1339_, v___x_1346_);
v___x_1348_ = lean_array_uset(v_bs_x27_1344_, v_i_1339_, v___x_1345_);
v_i_1339_ = v___x_1347_;
v_bs_1340_ = v___x_1348_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2___boxed(lean_object* v___x_1350_, lean_object* v_sz_1351_, lean_object* v_i_1352_, lean_object* v_bs_1353_){
_start:
{
size_t v_sz_boxed_1354_; size_t v_i_boxed_1355_; lean_object* v_res_1356_; 
v_sz_boxed_1354_ = lean_unbox_usize(v_sz_1351_);
lean_dec(v_sz_1351_);
v_i_boxed_1355_ = lean_unbox_usize(v_i_1352_);
lean_dec(v_i_1352_);
v_res_1356_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(v___x_1350_, v_sz_boxed_1354_, v_i_boxed_1355_, v_bs_1353_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearchSymm(lean_object* v_searchFn_1357_, lean_object* v_goal_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_){
_start:
{
lean_object* v___x_1364_; 
lean_inc(v_goal_1358_);
v___x_1364_ = l_Lean_MVarId_getType(v_goal_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v___x_1366_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_a_1365_);
lean_dec_ref_known(v___x_1364_, 1);
lean_inc_ref(v_searchFn_1357_);
lean_inc(v_a_1362_);
lean_inc_ref(v_a_1361_);
lean_inc(v_a_1360_);
lean_inc_ref(v_a_1359_);
v___x_1366_ = lean_apply_6(v_searchFn_1357_, v_a_1365_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, lean_box(0));
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_a_1367_; lean_object* v___x_1368_; lean_object* v_mctx_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_a_1367_);
lean_dec_ref_known(v___x_1366_, 1);
v___x_1368_ = lean_st_ref_get(v_a_1360_);
v_mctx_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc_ref_n(v_mctx_1369_, 2);
lean_dec(v___x_1368_);
lean_inc(v_goal_1358_);
v___x_1370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1370_, 0, v_goal_1358_);
lean_ctor_set(v___x_1370_, 1, v_mctx_1369_);
v___x_1371_ = lean_alloc_closure((void*)(l_Lean_MVarId_applySymm___boxed), 6, 1);
lean_closure_set(v___x_1371_, 0, v_goal_1358_);
v___x_1372_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(v___x_1371_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1433_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1375_ = v___x_1372_;
v_isShared_1376_ = v_isSharedCheck_1433_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1372_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1433_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
if (lean_obj_tag(v_a_1373_) == 1)
{
lean_object* v_val_1377_; lean_object* v___x_1378_; 
lean_del_object(v___x_1375_);
v_val_1377_ = lean_ctor_get(v_a_1373_, 0);
lean_inc_n(v_val_1377_, 2);
lean_dec_ref_known(v_a_1373_, 1);
v___x_1378_ = l_Lean_MVarId_getType(v_val_1377_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; lean_object* v___x_1380_; lean_object* v_a_1381_; lean_object* v___x_1382_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_a_1379_);
lean_dec_ref_known(v___x_1378_, 1);
v___x_1380_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(v_a_1379_, v_a_1360_);
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_a_1381_);
lean_dec_ref(v___x_1380_);
lean_inc(v_a_1362_);
lean_inc_ref(v_a_1361_);
lean_inc(v_a_1360_);
lean_inc_ref(v_a_1359_);
v___x_1382_ = lean_apply_6(v_searchFn_1357_, v_a_1381_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, lean_box(0));
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1410_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1385_ = v___x_1382_;
v_isShared_1386_ = v_isSharedCheck_1410_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1382_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1410_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v_cache_1389_; lean_object* v_zetaDeltaFVarIds_1390_; lean_object* v_postponed_1391_; lean_object* v_diag_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1408_; 
v___x_1387_ = lean_st_ref_get(v_a_1360_);
v___x_1388_ = lean_st_ref_take(v_a_1360_);
v_cache_1389_ = lean_ctor_get(v___x_1388_, 1);
v_zetaDeltaFVarIds_1390_ = lean_ctor_get(v___x_1388_, 2);
v_postponed_1391_ = lean_ctor_get(v___x_1388_, 3);
v_diag_1392_ = lean_ctor_get(v___x_1388_, 4);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1408_ == 0)
{
lean_object* v_unused_1409_; 
v_unused_1409_ = lean_ctor_get(v___x_1388_, 0);
lean_dec(v_unused_1409_);
v___x_1394_ = v___x_1388_;
v_isShared_1395_ = v_isSharedCheck_1408_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_diag_1392_);
lean_inc(v_postponed_1391_);
lean_inc(v_zetaDeltaFVarIds_1390_);
lean_inc(v_cache_1389_);
lean_dec(v___x_1388_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1408_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1397_; 
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 0, v_mctx_1369_);
v___x_1397_ = v___x_1394_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_mctx_1369_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v_cache_1389_);
lean_ctor_set(v_reuseFailAlloc_1407_, 2, v_zetaDeltaFVarIds_1390_);
lean_ctor_set(v_reuseFailAlloc_1407_, 3, v_postponed_1391_);
lean_ctor_set(v_reuseFailAlloc_1407_, 4, v_diag_1392_);
v___x_1397_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
lean_object* v___x_1398_; lean_object* v_mctx_1399_; lean_object* v___f_1400_; lean_object* v___x_1401_; lean_object* v___f_1402_; lean_object* v___x_1403_; lean_object* v___x_1405_; 
v___x_1398_ = lean_st_ref_set(v_a_1360_, v___x_1397_);
v_mctx_1399_ = lean_ctor_get(v___x_1387_, 0);
lean_inc_ref(v_mctx_1399_);
lean_dec(v___x_1387_);
v___f_1400_ = lean_alloc_closure((void*)(l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0), 2, 1);
lean_closure_set(v___f_1400_, 0, v___x_1370_);
v___x_1401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1401_, 0, v_val_1377_);
lean_ctor_set(v___x_1401_, 1, v_mctx_1399_);
v___f_1402_ = lean_alloc_closure((void*)(l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0), 2, 1);
lean_closure_set(v___f_1402_, 0, v___x_1401_);
v___x_1403_ = l_Lean_Meta_LibrarySearch_interleaveWith___redArg(v___f_1400_, v_a_1367_, v___f_1402_, v_a_1383_);
lean_dec(v_a_1383_);
lean_dec(v_a_1367_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1403_);
v___x_1405_ = v___x_1385_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1403_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
}
else
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1418_; 
lean_dec(v_val_1377_);
lean_dec_ref_known(v___x_1370_, 2);
lean_dec_ref(v_mctx_1369_);
lean_dec(v_a_1367_);
v_a_1411_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1413_ = v___x_1382_;
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1382_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
lean_dec(v_val_1377_);
lean_dec_ref_known(v___x_1370_, 2);
lean_dec_ref(v_mctx_1369_);
lean_dec(v_a_1367_);
lean_dec_ref(v_searchFn_1357_);
v_a_1419_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1378_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1378_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1419_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
else
{
size_t v_sz_1427_; size_t v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1431_; 
lean_dec(v_a_1373_);
lean_dec_ref(v_mctx_1369_);
lean_dec_ref(v_searchFn_1357_);
v_sz_1427_ = lean_array_size(v_a_1367_);
v___x_1428_ = ((size_t)0ULL);
v___x_1429_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(v___x_1370_, v_sz_1427_, v___x_1428_, v_a_1367_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v___x_1429_);
v___x_1431_ = v___x_1375_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1429_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
lean_dec_ref_known(v___x_1370_, 2);
lean_dec_ref(v_mctx_1369_);
lean_dec(v_a_1367_);
lean_dec_ref(v_searchFn_1357_);
v_a_1434_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___x_1372_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1372_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_dec(v_goal_1358_);
lean_dec_ref(v_searchFn_1357_);
v_a_1442_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1366_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1366_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_dec(v_goal_1358_);
lean_dec_ref(v_searchFn_1357_);
v_a_1450_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1364_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1364_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearchSymm___boxed(lean_object* v_searchFn_1458_, lean_object* v_goal_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v_searchFn_1458_, v_goal_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
lean_dec(v_a_1463_);
lean_dec_ref(v_a_1462_);
lean_dec(v_a_1461_);
lean_dec_ref(v_a_1460_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0(lean_object* v_e_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1476_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___closed__1));
v___x_1477_ = lean_unsigned_to_nat(1u);
v___x_1478_ = lean_mk_empty_array_with_capacity(v___x_1477_);
v___x_1479_ = lean_array_push(v___x_1478_, v_e_1470_);
v___x_1480_ = l_Lean_Meta_mkAppM(v___x_1476_, v___x_1479_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___boxed(lean_object* v_e_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0(v_e_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1(lean_object* v_e_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1498_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___closed__1));
v___x_1499_ = lean_unsigned_to_nat(1u);
v___x_1500_ = lean_mk_empty_array_with_capacity(v___x_1499_);
v___x_1501_ = lean_array_push(v___x_1500_, v_e_1492_);
v___x_1502_ = l_Lean_Meta_mkAppM(v___x_1498_, v___x_1501_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___boxed(lean_object* v_e_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1(v_e_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(lean_object* v_lem_1512_, uint8_t v_mod_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_){
_start:
{
lean_object* v___x_1519_; 
v___x_1519_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_lem_1512_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
if (lean_obj_tag(v___x_1519_) == 0)
{
switch(v_mod_1513_)
{
case 0:
{
return v___x_1519_;
}
case 1:
{
lean_object* v_a_1520_; lean_object* v___f_1521_; lean_object* v___x_1522_; 
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_a_1520_);
lean_dec_ref_known(v___x_1519_, 1);
v___f_1521_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__0));
v___x_1522_ = l_Lean_Meta_mapForallTelescope(v___f_1521_, v_a_1520_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
return v___x_1522_;
}
default: 
{
lean_object* v_a_1523_; lean_object* v___f_1524_; lean_object* v___x_1525_; 
v_a_1523_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_a_1523_);
lean_dec_ref_known(v___x_1519_, 1);
v___f_1524_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__1));
v___x_1525_ = l_Lean_Meta_mapForallTelescope(v___f_1524_, v_a_1523_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
return v___x_1525_;
}
}
}
else
{
return v___x_1519_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___boxed(lean_object* v_lem_1526_, lean_object* v_mod_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_){
_start:
{
uint8_t v_mod_boxed_1533_; lean_object* v_res_1534_; 
v_mod_boxed_1533_ = lean_unbox(v_mod_1527_);
v_res_1534_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_lem_1526_, v_mod_boxed_1533_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_);
lean_dec(v_a_1531_);
lean_dec_ref(v_a_1530_);
lean_dec(v_a_1529_);
lean_dec_ref(v_a_1528_);
return v_res_1534_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar(lean_object* v_e_1535_){
_start:
{
switch(lean_obj_tag(v_e_1535_))
{
case 0:
{
uint8_t v___x_1536_; 
v___x_1536_ = 1;
return v___x_1536_;
}
case 1:
{
uint8_t v___x_1537_; 
v___x_1537_ = 1;
return v___x_1537_;
}
case 2:
{
uint8_t v___x_1538_; 
v___x_1538_ = 1;
return v___x_1538_;
}
default: 
{
uint8_t v___x_1539_; 
v___x_1539_ = 0;
return v___x_1539_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar___boxed(lean_object* v_e_1540_){
_start:
{
uint8_t v_res_1541_; lean_object* v_r_1542_; 
v_res_1541_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar(v_e_1540_);
lean_dec_ref(v_e_1540_);
v_r_1542_ = lean_box(v_res_1541_);
return v_r_1542_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1543_ = lean_unsigned_to_nat(32u);
v___x_1544_ = lean_mk_empty_array_with_capacity(v___x_1543_);
v___x_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1544_);
return v___x_1545_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1546_ = ((size_t)5ULL);
v___x_1547_ = lean_unsigned_to_nat(0u);
v___x_1548_ = lean_unsigned_to_nat(32u);
v___x_1549_ = lean_mk_empty_array_with_capacity(v___x_1548_);
v___x_1550_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0);
v___x_1551_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
lean_ctor_set(v___x_1551_, 1, v___x_1549_);
lean_ctor_set(v___x_1551_, 2, v___x_1547_);
lean_ctor_set(v___x_1551_, 3, v___x_1547_);
lean_ctor_set_usize(v___x_1551_, 4, v___x_1546_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(lean_object* v___y_1552_){
_start:
{
lean_object* v___x_1554_; lean_object* v_traceState_1555_; lean_object* v_traces_1556_; lean_object* v___x_1557_; lean_object* v_traceState_1558_; lean_object* v_env_1559_; lean_object* v_nextMacroScope_1560_; lean_object* v_ngen_1561_; lean_object* v_auxDeclNGen_1562_; lean_object* v_cache_1563_; lean_object* v_messages_1564_; lean_object* v_infoState_1565_; lean_object* v_snapshotTasks_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1585_; 
v___x_1554_ = lean_st_ref_get(v___y_1552_);
v_traceState_1555_ = lean_ctor_get(v___x_1554_, 4);
lean_inc_ref(v_traceState_1555_);
lean_dec(v___x_1554_);
v_traces_1556_ = lean_ctor_get(v_traceState_1555_, 0);
lean_inc_ref(v_traces_1556_);
lean_dec_ref(v_traceState_1555_);
v___x_1557_ = lean_st_ref_take(v___y_1552_);
v_traceState_1558_ = lean_ctor_get(v___x_1557_, 4);
v_env_1559_ = lean_ctor_get(v___x_1557_, 0);
v_nextMacroScope_1560_ = lean_ctor_get(v___x_1557_, 1);
v_ngen_1561_ = lean_ctor_get(v___x_1557_, 2);
v_auxDeclNGen_1562_ = lean_ctor_get(v___x_1557_, 3);
v_cache_1563_ = lean_ctor_get(v___x_1557_, 5);
v_messages_1564_ = lean_ctor_get(v___x_1557_, 6);
v_infoState_1565_ = lean_ctor_get(v___x_1557_, 7);
v_snapshotTasks_1566_ = lean_ctor_get(v___x_1557_, 8);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1568_ = v___x_1557_;
v_isShared_1569_ = v_isSharedCheck_1585_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_snapshotTasks_1566_);
lean_inc(v_infoState_1565_);
lean_inc(v_messages_1564_);
lean_inc(v_cache_1563_);
lean_inc(v_traceState_1558_);
lean_inc(v_auxDeclNGen_1562_);
lean_inc(v_ngen_1561_);
lean_inc(v_nextMacroScope_1560_);
lean_inc(v_env_1559_);
lean_dec(v___x_1557_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1585_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
uint64_t v_tid_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1583_; 
v_tid_1570_ = lean_ctor_get_uint64(v_traceState_1558_, sizeof(void*)*1);
v_isSharedCheck_1583_ = !lean_is_exclusive(v_traceState_1558_);
if (v_isSharedCheck_1583_ == 0)
{
lean_object* v_unused_1584_; 
v_unused_1584_ = lean_ctor_get(v_traceState_1558_, 0);
lean_dec(v_unused_1584_);
v___x_1572_ = v_traceState_1558_;
v_isShared_1573_ = v_isSharedCheck_1583_;
goto v_resetjp_1571_;
}
else
{
lean_dec(v_traceState_1558_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1583_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1574_; lean_object* v___x_1576_; 
v___x_1574_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1);
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 0, v___x_1574_);
v___x_1576_ = v___x_1572_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1574_);
lean_ctor_set_uint64(v_reuseFailAlloc_1582_, sizeof(void*)*1, v_tid_1570_);
v___x_1576_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
lean_object* v___x_1578_; 
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 4, v___x_1576_);
v___x_1578_ = v___x_1568_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_env_1559_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v_nextMacroScope_1560_);
lean_ctor_set(v_reuseFailAlloc_1581_, 2, v_ngen_1561_);
lean_ctor_set(v_reuseFailAlloc_1581_, 3, v_auxDeclNGen_1562_);
lean_ctor_set(v_reuseFailAlloc_1581_, 4, v___x_1576_);
lean_ctor_set(v_reuseFailAlloc_1581_, 5, v_cache_1563_);
lean_ctor_set(v_reuseFailAlloc_1581_, 6, v_messages_1564_);
lean_ctor_set(v_reuseFailAlloc_1581_, 7, v_infoState_1565_);
lean_ctor_set(v_reuseFailAlloc_1581_, 8, v_snapshotTasks_1566_);
v___x_1578_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = lean_st_ref_set(v___y_1552_, v___x_1578_);
v___x_1580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1580_, 0, v_traces_1556_);
return v___x_1580_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___boxed(lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v___y_1586_);
lean_dec(v___y_1586_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0(lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v___y_1592_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___boxed(lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0(v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
return v_res_1600_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(lean_object* v_opts_1601_, lean_object* v_opt_1602_){
_start:
{
lean_object* v_name_1603_; lean_object* v_defValue_1604_; lean_object* v_map_1605_; lean_object* v___x_1606_; 
v_name_1603_ = lean_ctor_get(v_opt_1602_, 0);
v_defValue_1604_ = lean_ctor_get(v_opt_1602_, 1);
v_map_1605_ = lean_ctor_get(v_opts_1601_, 0);
v___x_1606_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1605_, v_name_1603_);
if (lean_obj_tag(v___x_1606_) == 0)
{
uint8_t v___x_1607_; 
v___x_1607_ = lean_unbox(v_defValue_1604_);
return v___x_1607_;
}
else
{
lean_object* v_val_1608_; 
v_val_1608_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_val_1608_);
lean_dec_ref_known(v___x_1606_, 1);
if (lean_obj_tag(v_val_1608_) == 1)
{
uint8_t v_v_1609_; 
v_v_1609_ = lean_ctor_get_uint8(v_val_1608_, 0);
lean_dec_ref_known(v_val_1608_, 0);
return v_v_1609_;
}
else
{
uint8_t v___x_1610_; 
lean_dec(v_val_1608_);
v___x_1610_ = lean_unbox(v_defValue_1604_);
return v___x_1610_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1___boxed(lean_object* v_opts_1611_, lean_object* v_opt_1612_){
_start:
{
uint8_t v_res_1613_; lean_object* v_r_1614_; 
v_res_1613_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_1611_, v_opt_1612_);
lean_dec_ref(v_opt_1612_);
lean_dec_ref(v_opts_1611_);
v_r_1614_ = lean_box(v_res_1613_);
return v_r_1614_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__0));
v___x_1617_ = l_Lean_stringToMessageData(v___x_1616_);
return v___x_1617_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__2));
v___x_1620_ = l_Lean_stringToMessageData(v___x_1619_);
return v___x_1620_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1624_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__5));
v___x_1625_ = l_Lean_MessageData_ofFormat(v___x_1624_);
return v___x_1625_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__8));
v___x_1630_ = l_Lean_MessageData_ofFormat(v___x_1629_);
return v___x_1630_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12(void){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__11));
v___x_1635_ = l_Lean_MessageData_ofFormat(v___x_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0(lean_object* v_fst_1636_, uint8_t v_snd_1637_, lean_object* v_x_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___y_1648_; 
v___x_1644_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1);
v___x_1645_ = l_Lean_MessageData_ofName(v_fst_1636_);
v___x_1646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1644_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
switch(v_snd_1637_)
{
case 0:
{
lean_object* v___x_1653_; 
v___x_1653_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6);
v___y_1648_ = v___x_1653_;
goto v___jp_1647_;
}
case 1:
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9);
v___y_1648_ = v___x_1654_;
goto v___jp_1647_;
}
default: 
{
lean_object* v___x_1655_; 
v___x_1655_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12);
v___y_1648_ = v___x_1655_;
goto v___jp_1647_;
}
}
v___jp_1647_:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
lean_inc_ref(v___y_1648_);
v___x_1649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1646_);
lean_ctor_set(v___x_1649_, 1, v___y_1648_);
v___x_1650_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3);
v___x_1651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1649_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
v___x_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
return v___x_1652_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___boxed(lean_object* v_fst_1656_, lean_object* v_snd_1657_, lean_object* v_x_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
uint8_t v_snd_11696__boxed_1664_; lean_object* v_res_1665_; 
v_snd_11696__boxed_1664_ = lean_unbox(v_snd_1657_);
v_res_1665_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0(v_fst_1656_, v_snd_11696__boxed_1664_, v_x_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec_ref(v_x_1658_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(lean_object* v_opts_1666_, lean_object* v_opt_1667_){
_start:
{
lean_object* v_name_1668_; lean_object* v_defValue_1669_; lean_object* v_map_1670_; lean_object* v___x_1671_; 
v_name_1668_ = lean_ctor_get(v_opt_1667_, 0);
v_defValue_1669_ = lean_ctor_get(v_opt_1667_, 1);
v_map_1670_ = lean_ctor_get(v_opts_1666_, 0);
v___x_1671_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1670_, v_name_1668_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_inc(v_defValue_1669_);
return v_defValue_1669_;
}
else
{
lean_object* v_val_1672_; 
v_val_1672_ = lean_ctor_get(v___x_1671_, 0);
lean_inc(v_val_1672_);
lean_dec_ref_known(v___x_1671_, 1);
if (lean_obj_tag(v_val_1672_) == 3)
{
lean_object* v_v_1673_; 
v_v_1673_ = lean_ctor_get(v_val_1672_, 0);
lean_inc(v_v_1673_);
lean_dec_ref_known(v_val_1672_, 1);
return v_v_1673_;
}
else
{
lean_dec(v_val_1672_);
lean_inc(v_defValue_1669_);
return v_defValue_1669_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5___boxed(lean_object* v_opts_1674_, lean_object* v_opt_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_1674_, v_opt_1675_);
lean_dec_ref(v_opt_1675_);
lean_dec_ref(v_opts_1674_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(lean_object* v_x_1677_){
_start:
{
if (lean_obj_tag(v_x_1677_) == 0)
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
v_a_1679_ = lean_ctor_get(v_x_1677_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v_x_1677_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v_x_1677_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v_x_1677_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
lean_ctor_set_tag(v___x_1681_, 1);
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
v_a_1687_ = lean_ctor_get(v_x_1677_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v_x_1677_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v_x_1677_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v_x_1677_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
lean_ctor_set_tag(v___x_1689_, 0);
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1687_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg___boxed(lean_object* v_x_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_x_1695_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3(size_t v_sz_1698_, size_t v_i_1699_, lean_object* v_bs_1700_){
_start:
{
uint8_t v___x_1701_; 
v___x_1701_ = lean_usize_dec_lt(v_i_1699_, v_sz_1698_);
if (v___x_1701_ == 0)
{
return v_bs_1700_;
}
else
{
lean_object* v_v_1702_; lean_object* v_msg_1703_; lean_object* v___x_1704_; lean_object* v_bs_x27_1705_; size_t v___x_1706_; size_t v___x_1707_; lean_object* v___x_1708_; 
v_v_1702_ = lean_array_uget_borrowed(v_bs_1700_, v_i_1699_);
v_msg_1703_ = lean_ctor_get(v_v_1702_, 1);
lean_inc_ref(v_msg_1703_);
v___x_1704_ = lean_unsigned_to_nat(0u);
v_bs_x27_1705_ = lean_array_uset(v_bs_1700_, v_i_1699_, v___x_1704_);
v___x_1706_ = ((size_t)1ULL);
v___x_1707_ = lean_usize_add(v_i_1699_, v___x_1706_);
v___x_1708_ = lean_array_uset(v_bs_x27_1705_, v_i_1699_, v_msg_1703_);
v_i_1699_ = v___x_1707_;
v_bs_1700_ = v___x_1708_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_1710_, lean_object* v_i_1711_, lean_object* v_bs_1712_){
_start:
{
size_t v_sz_boxed_1713_; size_t v_i_boxed_1714_; lean_object* v_res_1715_; 
v_sz_boxed_1713_ = lean_unbox_usize(v_sz_1710_);
lean_dec(v_sz_1710_);
v_i_boxed_1714_ = lean_unbox_usize(v_i_1711_);
lean_dec(v_i_1711_);
v_res_1715_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3(v_sz_boxed_1713_, v_i_boxed_1714_, v_bs_1712_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(lean_object* v_oldTraces_1716_, lean_object* v_data_1717_, lean_object* v_ref_1718_, lean_object* v_msg_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v_fileName_1725_; lean_object* v_fileMap_1726_; lean_object* v_options_1727_; lean_object* v_currRecDepth_1728_; lean_object* v_maxRecDepth_1729_; lean_object* v_ref_1730_; lean_object* v_currNamespace_1731_; lean_object* v_openDecls_1732_; lean_object* v_initHeartbeats_1733_; lean_object* v_maxHeartbeats_1734_; lean_object* v_quotContext_1735_; lean_object* v_currMacroScope_1736_; uint8_t v_diag_1737_; lean_object* v_cancelTk_x3f_1738_; uint8_t v_suppressElabErrors_1739_; lean_object* v_inheritedTraceOptions_1740_; lean_object* v___x_1741_; lean_object* v_traceState_1742_; lean_object* v_traces_1743_; lean_object* v_ref_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; size_t v_sz_1747_; size_t v___x_1748_; lean_object* v___x_1749_; lean_object* v_msg_1750_; lean_object* v___x_1751_; lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1789_; 
v_fileName_1725_ = lean_ctor_get(v___y_1722_, 0);
v_fileMap_1726_ = lean_ctor_get(v___y_1722_, 1);
v_options_1727_ = lean_ctor_get(v___y_1722_, 2);
v_currRecDepth_1728_ = lean_ctor_get(v___y_1722_, 3);
v_maxRecDepth_1729_ = lean_ctor_get(v___y_1722_, 4);
v_ref_1730_ = lean_ctor_get(v___y_1722_, 5);
v_currNamespace_1731_ = lean_ctor_get(v___y_1722_, 6);
v_openDecls_1732_ = lean_ctor_get(v___y_1722_, 7);
v_initHeartbeats_1733_ = lean_ctor_get(v___y_1722_, 8);
v_maxHeartbeats_1734_ = lean_ctor_get(v___y_1722_, 9);
v_quotContext_1735_ = lean_ctor_get(v___y_1722_, 10);
v_currMacroScope_1736_ = lean_ctor_get(v___y_1722_, 11);
v_diag_1737_ = lean_ctor_get_uint8(v___y_1722_, sizeof(void*)*14);
v_cancelTk_x3f_1738_ = lean_ctor_get(v___y_1722_, 12);
v_suppressElabErrors_1739_ = lean_ctor_get_uint8(v___y_1722_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1740_ = lean_ctor_get(v___y_1722_, 13);
v___x_1741_ = lean_st_ref_get(v___y_1723_);
v_traceState_1742_ = lean_ctor_get(v___x_1741_, 4);
lean_inc_ref(v_traceState_1742_);
lean_dec(v___x_1741_);
v_traces_1743_ = lean_ctor_get(v_traceState_1742_, 0);
lean_inc_ref(v_traces_1743_);
lean_dec_ref(v_traceState_1742_);
v_ref_1744_ = l_Lean_replaceRef(v_ref_1718_, v_ref_1730_);
lean_inc_ref(v_inheritedTraceOptions_1740_);
lean_inc(v_cancelTk_x3f_1738_);
lean_inc(v_currMacroScope_1736_);
lean_inc(v_quotContext_1735_);
lean_inc(v_maxHeartbeats_1734_);
lean_inc(v_initHeartbeats_1733_);
lean_inc(v_openDecls_1732_);
lean_inc(v_currNamespace_1731_);
lean_inc(v_maxRecDepth_1729_);
lean_inc(v_currRecDepth_1728_);
lean_inc_ref(v_options_1727_);
lean_inc_ref(v_fileMap_1726_);
lean_inc_ref(v_fileName_1725_);
v___x_1745_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1745_, 0, v_fileName_1725_);
lean_ctor_set(v___x_1745_, 1, v_fileMap_1726_);
lean_ctor_set(v___x_1745_, 2, v_options_1727_);
lean_ctor_set(v___x_1745_, 3, v_currRecDepth_1728_);
lean_ctor_set(v___x_1745_, 4, v_maxRecDepth_1729_);
lean_ctor_set(v___x_1745_, 5, v_ref_1744_);
lean_ctor_set(v___x_1745_, 6, v_currNamespace_1731_);
lean_ctor_set(v___x_1745_, 7, v_openDecls_1732_);
lean_ctor_set(v___x_1745_, 8, v_initHeartbeats_1733_);
lean_ctor_set(v___x_1745_, 9, v_maxHeartbeats_1734_);
lean_ctor_set(v___x_1745_, 10, v_quotContext_1735_);
lean_ctor_set(v___x_1745_, 11, v_currMacroScope_1736_);
lean_ctor_set(v___x_1745_, 12, v_cancelTk_x3f_1738_);
lean_ctor_set(v___x_1745_, 13, v_inheritedTraceOptions_1740_);
lean_ctor_set_uint8(v___x_1745_, sizeof(void*)*14, v_diag_1737_);
lean_ctor_set_uint8(v___x_1745_, sizeof(void*)*14 + 1, v_suppressElabErrors_1739_);
v___x_1746_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1743_);
lean_dec_ref(v_traces_1743_);
v_sz_1747_ = lean_array_size(v___x_1746_);
v___x_1748_ = ((size_t)0ULL);
v___x_1749_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3(v_sz_1747_, v___x_1748_, v___x_1746_);
v_msg_1750_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1750_, 0, v_data_1717_);
lean_ctor_set(v_msg_1750_, 1, v_msg_1719_);
lean_ctor_set(v_msg_1750_, 2, v___x_1749_);
v___x_1751_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(v_msg_1750_, v___y_1720_, v___y_1721_, v___x_1745_, v___y_1723_);
lean_dec_ref_known(v___x_1745_, 14);
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1754_ = v___x_1751_;
v_isShared_1755_ = v_isSharedCheck_1789_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1751_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1789_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1756_; lean_object* v_traceState_1757_; lean_object* v_env_1758_; lean_object* v_nextMacroScope_1759_; lean_object* v_ngen_1760_; lean_object* v_auxDeclNGen_1761_; lean_object* v_cache_1762_; lean_object* v_messages_1763_; lean_object* v_infoState_1764_; lean_object* v_snapshotTasks_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1788_; 
v___x_1756_ = lean_st_ref_take(v___y_1723_);
v_traceState_1757_ = lean_ctor_get(v___x_1756_, 4);
v_env_1758_ = lean_ctor_get(v___x_1756_, 0);
v_nextMacroScope_1759_ = lean_ctor_get(v___x_1756_, 1);
v_ngen_1760_ = lean_ctor_get(v___x_1756_, 2);
v_auxDeclNGen_1761_ = lean_ctor_get(v___x_1756_, 3);
v_cache_1762_ = lean_ctor_get(v___x_1756_, 5);
v_messages_1763_ = lean_ctor_get(v___x_1756_, 6);
v_infoState_1764_ = lean_ctor_get(v___x_1756_, 7);
v_snapshotTasks_1765_ = lean_ctor_get(v___x_1756_, 8);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1767_ = v___x_1756_;
v_isShared_1768_ = v_isSharedCheck_1788_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_snapshotTasks_1765_);
lean_inc(v_infoState_1764_);
lean_inc(v_messages_1763_);
lean_inc(v_cache_1762_);
lean_inc(v_traceState_1757_);
lean_inc(v_auxDeclNGen_1761_);
lean_inc(v_ngen_1760_);
lean_inc(v_nextMacroScope_1759_);
lean_inc(v_env_1758_);
lean_dec(v___x_1756_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1788_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
uint64_t v_tid_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1786_; 
v_tid_1769_ = lean_ctor_get_uint64(v_traceState_1757_, sizeof(void*)*1);
v_isSharedCheck_1786_ = !lean_is_exclusive(v_traceState_1757_);
if (v_isSharedCheck_1786_ == 0)
{
lean_object* v_unused_1787_; 
v_unused_1787_ = lean_ctor_get(v_traceState_1757_, 0);
lean_dec(v_unused_1787_);
v___x_1771_ = v_traceState_1757_;
v_isShared_1772_ = v_isSharedCheck_1786_;
goto v_resetjp_1770_;
}
else
{
lean_dec(v_traceState_1757_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1786_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1776_; 
v___x_1773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1773_, 0, v_ref_1718_);
lean_ctor_set(v___x_1773_, 1, v_a_1752_);
v___x_1774_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1716_, v___x_1773_);
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 0, v___x_1774_);
v___x_1776_ = v___x_1771_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1774_);
lean_ctor_set_uint64(v_reuseFailAlloc_1785_, sizeof(void*)*1, v_tid_1769_);
v___x_1776_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
lean_object* v___x_1778_; 
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 4, v___x_1776_);
v___x_1778_ = v___x_1767_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_env_1758_);
lean_ctor_set(v_reuseFailAlloc_1784_, 1, v_nextMacroScope_1759_);
lean_ctor_set(v_reuseFailAlloc_1784_, 2, v_ngen_1760_);
lean_ctor_set(v_reuseFailAlloc_1784_, 3, v_auxDeclNGen_1761_);
lean_ctor_set(v_reuseFailAlloc_1784_, 4, v___x_1776_);
lean_ctor_set(v_reuseFailAlloc_1784_, 5, v_cache_1762_);
lean_ctor_set(v_reuseFailAlloc_1784_, 6, v_messages_1763_);
lean_ctor_set(v_reuseFailAlloc_1784_, 7, v_infoState_1764_);
lean_ctor_set(v_reuseFailAlloc_1784_, 8, v_snapshotTasks_1765_);
v___x_1778_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1782_; 
v___x_1779_ = lean_st_ref_set(v___y_1723_, v___x_1778_);
v___x_1780_ = lean_box(0);
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 0, v___x_1780_);
v___x_1782_ = v___x_1754_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1780_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2___boxed(lean_object* v_oldTraces_1790_, lean_object* v_data_1791_, lean_object* v_ref_1792_, lean_object* v_msg_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(v_oldTraces_1790_, v_data_1791_, v_ref_1792_, v_msg_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
return v_res_1799_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(lean_object* v_e_1800_){
_start:
{
if (lean_obj_tag(v_e_1800_) == 0)
{
uint8_t v___x_1801_; 
v___x_1801_ = 2;
return v___x_1801_;
}
else
{
uint8_t v___x_1802_; 
v___x_1802_ = 0;
return v___x_1802_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4___boxed(lean_object* v_e_1803_){
_start:
{
uint8_t v_res_1804_; lean_object* v_r_1805_; 
v_res_1804_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(v_e_1803_);
lean_dec_ref(v_e_1803_);
v_r_1805_ = lean_box(v_res_1804_);
return v_r_1805_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1806_; double v___x_1807_; 
v___x_1806_ = lean_unsigned_to_nat(0u);
v___x_1807_ = lean_float_of_nat(v___x_1806_);
return v___x_1807_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__1));
v___x_1810_ = l_Lean_stringToMessageData(v___x_1809_);
return v___x_1810_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1811_; double v___x_1812_; 
v___x_1811_ = lean_unsigned_to_nat(1000u);
v___x_1812_ = lean_float_of_nat(v___x_1811_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(lean_object* v_cls_1813_, uint8_t v_collapsed_1814_, lean_object* v_tag_1815_, lean_object* v_opts_1816_, uint8_t v_clsEnabled_1817_, lean_object* v_oldTraces_1818_, lean_object* v_msg_1819_, lean_object* v_resStartStop_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v_fst_1826_; lean_object* v_snd_1827_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v_data_1831_; lean_object* v_fst_1842_; lean_object* v_snd_1843_; lean_object* v___x_1844_; uint8_t v___x_1845_; lean_object* v___y_1847_; lean_object* v_a_1848_; uint8_t v___y_1863_; double v___y_1894_; 
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
v___x_1845_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_1816_, v___x_1844_);
if (v___x_1845_ == 0)
{
v___y_1863_ = v___x_1845_;
goto v___jp_1862_;
}
else
{
lean_object* v___x_1899_; uint8_t v___x_1900_; 
v___x_1899_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1900_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_1816_, v___x_1899_);
if (v___x_1900_ == 0)
{
lean_object* v___x_1901_; lean_object* v___x_1902_; double v___x_1903_; double v___x_1904_; double v___x_1905_; 
v___x_1901_ = l_Lean_trace_profiler_threshold;
v___x_1902_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_1816_, v___x_1901_);
v___x_1903_ = lean_float_of_nat(v___x_1902_);
v___x_1904_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3);
v___x_1905_ = lean_float_div(v___x_1903_, v___x_1904_);
v___y_1894_ = v___x_1905_;
goto v___jp_1893_;
}
else
{
lean_object* v___x_1906_; lean_object* v___x_1907_; double v___x_1908_; 
v___x_1906_ = l_Lean_trace_profiler_threshold;
v___x_1907_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_1816_, v___x_1906_);
v___x_1908_ = lean_float_of_nat(v___x_1907_);
v___y_1894_ = v___x_1908_;
goto v___jp_1893_;
}
}
v___jp_1828_:
{
lean_object* v___x_1832_; 
lean_inc(v___y_1829_);
v___x_1832_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(v_oldTraces_1818_, v_data_1831_, v___y_1829_, v___y_1830_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v___x_1833_; 
lean_dec_ref_known(v___x_1832_, 1);
v___x_1833_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_1826_);
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
v_result_1849_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(v_fst_1826_);
v___x_1850_ = lean_box(v_result_1849_);
v___x_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
v___x_1852_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0);
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
v_ref_1858_ = lean_ctor_get(v___y_1823_, 5);
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
v___x_1861_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2);
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
lean_object* v___x_1864_; lean_object* v_traceState_1865_; lean_object* v_env_1866_; lean_object* v_nextMacroScope_1867_; lean_object* v_ngen_1868_; lean_object* v_auxDeclNGen_1869_; lean_object* v_cache_1870_; lean_object* v_messages_1871_; lean_object* v_infoState_1872_; lean_object* v_snapshotTasks_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1892_; 
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
v_messages_1871_ = lean_ctor_get(v___x_1864_, 6);
v_infoState_1872_ = lean_ctor_get(v___x_1864_, 7);
v_snapshotTasks_1873_ = lean_ctor_get(v___x_1864_, 8);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1875_ = v___x_1864_;
v_isShared_1876_ = v_isSharedCheck_1892_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_snapshotTasks_1873_);
lean_inc(v_infoState_1872_);
lean_inc(v_messages_1871_);
lean_inc(v_cache_1870_);
lean_inc(v_traceState_1865_);
lean_inc(v_auxDeclNGen_1869_);
lean_inc(v_ngen_1868_);
lean_inc(v_nextMacroScope_1867_);
lean_inc(v_env_1866_);
lean_dec(v___x_1864_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1892_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
uint64_t v_tid_1877_; lean_object* v_traces_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1891_; 
v_tid_1877_ = lean_ctor_get_uint64(v_traceState_1865_, sizeof(void*)*1);
v_traces_1878_ = lean_ctor_get(v_traceState_1865_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v_traceState_1865_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1880_ = v_traceState_1865_;
v_isShared_1881_ = v_isSharedCheck_1891_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_traces_1878_);
lean_dec(v_traceState_1865_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1891_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; lean_object* v___x_1884_; 
v___x_1882_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1818_, v_traces_1878_);
lean_dec_ref(v_traces_1878_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 0, v___x_1882_);
v___x_1884_ = v___x_1880_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v___x_1882_);
lean_ctor_set_uint64(v_reuseFailAlloc_1890_, sizeof(void*)*1, v_tid_1877_);
v___x_1884_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
lean_object* v___x_1886_; 
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 4, v___x_1884_);
v___x_1886_ = v___x_1875_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_env_1866_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v_nextMacroScope_1867_);
lean_ctor_set(v_reuseFailAlloc_1889_, 2, v_ngen_1868_);
lean_ctor_set(v_reuseFailAlloc_1889_, 3, v_auxDeclNGen_1869_);
lean_ctor_set(v_reuseFailAlloc_1889_, 4, v___x_1884_);
lean_ctor_set(v_reuseFailAlloc_1889_, 5, v_cache_1870_);
lean_ctor_set(v_reuseFailAlloc_1889_, 6, v_messages_1871_);
lean_ctor_set(v_reuseFailAlloc_1889_, 7, v_infoState_1872_);
lean_ctor_set(v_reuseFailAlloc_1889_, 8, v_snapshotTasks_1873_);
v___x_1886_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = lean_st_ref_set(v___y_1824_, v___x_1886_);
v___x_1888_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_1826_);
return v___x_1888_;
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
v___jp_1893_:
{
double v___x_1895_; double v___x_1896_; double v___x_1897_; uint8_t v___x_1898_; 
v___x_1895_ = lean_unbox_float(v_snd_1843_);
v___x_1896_ = lean_unbox_float(v_fst_1842_);
v___x_1897_ = lean_float_sub(v___x_1895_, v___x_1896_);
v___x_1898_ = lean_float_decLt(v___y_1894_, v___x_1897_);
v___y_1863_ = v___x_1898_;
goto v___jp_1862_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___boxed(lean_object* v_cls_1909_, lean_object* v_collapsed_1910_, lean_object* v_tag_1911_, lean_object* v_opts_1912_, lean_object* v_clsEnabled_1913_, lean_object* v_oldTraces_1914_, lean_object* v_msg_1915_, lean_object* v_resStartStop_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
uint8_t v_collapsed_boxed_1922_; uint8_t v_clsEnabled_boxed_1923_; lean_object* v_res_1924_; 
v_collapsed_boxed_1922_ = lean_unbox(v_collapsed_1910_);
v_clsEnabled_boxed_1923_ = lean_unbox(v_clsEnabled_1913_);
v_res_1924_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v_cls_1909_, v_collapsed_boxed_1922_, v_tag_1911_, v_opts_1912_, v_clsEnabled_boxed_1923_, v_oldTraces_1914_, v_msg_1915_, v_resStartStop_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
lean_dec_ref(v_opts_1912_);
return v_res_1924_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2(void){
_start:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1928_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_1929_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__1));
v___x_1930_ = l_Lean_Name_append(v___x_1929_, v___x_1928_);
return v___x_1930_;
}
}
static double _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3(void){
_start:
{
lean_object* v___x_1931_; double v___x_1932_; 
v___x_1931_ = lean_unsigned_to_nat(1000000000u);
v___x_1932_ = lean_float_of_nat(v___x_1931_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(lean_object* v_cfg_1933_, lean_object* v_act_1934_, lean_object* v_allowFailure_1935_, lean_object* v_cand_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_){
_start:
{
lean_object* v_fst_1942_; lean_object* v_snd_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_2229_; 
v_fst_1942_ = lean_ctor_get(v_cand_1936_, 0);
v_snd_1943_ = lean_ctor_get(v_cand_1936_, 1);
v_isSharedCheck_2229_ = !lean_is_exclusive(v_cand_1936_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_1945_ = v_cand_1936_;
v_isShared_1946_ = v_isSharedCheck_2229_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_snd_1943_);
lean_inc(v_fst_1942_);
lean_dec(v_cand_1936_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_2229_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v_options_1947_; uint8_t v_hasTrace_1948_; 
v_options_1947_ = lean_ctor_get(v_a_1939_, 2);
v_hasTrace_1948_ = lean_ctor_get_uint8(v_options_1947_, sizeof(void*)*1);
if (v_hasTrace_1948_ == 0)
{
lean_object* v_fst_1949_; lean_object* v_snd_1950_; lean_object* v_fst_1951_; lean_object* v_snd_1952_; lean_object* v___x_1953_; lean_object* v_cache_1954_; lean_object* v_zetaDeltaFVarIds_1955_; lean_object* v_postponed_1956_; lean_object* v_diag_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_2005_; 
lean_del_object(v___x_1945_);
v_fst_1949_ = lean_ctor_get(v_fst_1942_, 0);
lean_inc(v_fst_1949_);
v_snd_1950_ = lean_ctor_get(v_fst_1942_, 1);
lean_inc(v_snd_1950_);
lean_dec(v_fst_1942_);
v_fst_1951_ = lean_ctor_get(v_snd_1943_, 0);
lean_inc(v_fst_1951_);
v_snd_1952_ = lean_ctor_get(v_snd_1943_, 1);
lean_inc(v_snd_1952_);
lean_dec(v_snd_1943_);
v___x_1953_ = lean_st_ref_take(v_a_1938_);
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
v___x_1963_ = lean_st_ref_set(v_a_1938_, v___x_1962_);
v___x_1964_ = lean_unbox(v_snd_1952_);
lean_dec(v_snd_1952_);
v___x_1965_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_1951_, v___x_1964_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_a_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_a_1966_);
lean_dec_ref_known(v___x_1965_, 1);
v___x_1967_ = lean_box(0);
lean_inc(v_fst_1949_);
v___x_1968_ = l_Lean_MVarId_apply(v_fst_1949_, v_a_1966_, v_cfg_1933_, v___x_1967_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v___x_1970_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc_n(v_a_1969_, 2);
lean_dec_ref_known(v___x_1968_, 1);
lean_inc(v_a_1940_);
lean_inc_ref(v_a_1939_);
lean_inc(v_a_1938_);
lean_inc_ref(v_a_1937_);
v___x_1970_ = lean_apply_6(v_act_1934_, v_a_1969_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, lean_box(0));
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_dec(v_a_1969_);
lean_dec(v_fst_1949_);
lean_dec_ref(v_allowFailure_1935_);
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
lean_inc(v_a_1940_);
lean_inc_ref(v_a_1939_);
lean_inc(v_a_1938_);
lean_inc_ref(v_a_1937_);
v___x_1974_ = lean_apply_6(v_allowFailure_1935_, v_fst_1949_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, lean_box(0));
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
v___x_1980_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1);
v___x_1981_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_1980_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
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
lean_dec_ref(v_allowFailure_1935_);
return v___x_1970_;
}
}
}
}
else
{
lean_dec(v_fst_1949_);
lean_dec_ref(v_allowFailure_1935_);
lean_dec_ref(v_act_1934_);
return v___x_1968_;
}
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
lean_dec(v_fst_1949_);
lean_dec_ref(v_allowFailure_1935_);
lean_dec_ref(v_act_1934_);
lean_dec_ref(v_cfg_1933_);
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
v_fst_2007_ = lean_ctor_get(v_fst_1942_, 0);
v_snd_2008_ = lean_ctor_get(v_fst_1942_, 1);
v_isSharedCheck_2228_ = !lean_is_exclusive(v_fst_1942_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2010_ = v_fst_1942_;
v_isShared_2011_ = v_isSharedCheck_2228_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_snd_2008_);
lean_inc(v_fst_2007_);
lean_dec(v_fst_1942_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2228_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v_fst_2012_; lean_object* v_snd_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2227_; 
v_fst_2012_ = lean_ctor_get(v_snd_1943_, 0);
v_snd_2013_ = lean_ctor_get(v_snd_1943_, 1);
v_isSharedCheck_2227_ = !lean_is_exclusive(v_snd_1943_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2015_ = v_snd_1943_;
v_isShared_2016_ = v_isSharedCheck_2227_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_snd_2013_);
lean_inc(v_fst_2012_);
lean_dec(v_snd_1943_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2227_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v_inheritedTraceOptions_2017_; lean_object* v___f_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; uint8_t v___x_2022_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v_a_2026_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v_a_2045_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v_a_2050_; lean_object* v___y_2053_; lean_object* v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2059_; lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v___y_2062_; uint8_t v___y_2063_; lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v_a_2073_; lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v_a_2087_; lean_object* v___y_2090_; lean_object* v___y_2091_; lean_object* v_a_2092_; lean_object* v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___y_2101_; lean_object* v___y_2102_; lean_object* v___y_2103_; lean_object* v___y_2104_; uint8_t v___y_2105_; 
v_inheritedTraceOptions_2017_ = lean_ctor_get(v_a_1939_, 13);
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
lean_del_object(v___x_1945_);
v___x_2173_ = lean_st_ref_take(v_a_1938_);
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
v___x_2183_ = lean_st_ref_set(v_a_1938_, v___x_2182_);
v___x_2184_ = lean_unbox(v_snd_2013_);
lean_dec(v_snd_2013_);
v___x_2185_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_2012_, v___x_2184_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_a_2186_);
lean_dec_ref_known(v___x_2185_, 1);
v___x_2187_ = lean_box(0);
lean_inc(v_fst_2007_);
v___x_2188_ = l_Lean_MVarId_apply(v_fst_2007_, v_a_2186_, v_cfg_1933_, v___x_2187_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v_a_2189_; lean_object* v___x_2190_; 
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
lean_inc_n(v_a_2189_, 2);
lean_dec_ref_known(v___x_2188_, 1);
lean_inc(v_a_1940_);
lean_inc_ref(v_a_1939_);
lean_inc(v_a_1938_);
lean_inc_ref(v_a_1937_);
v___x_2190_ = lean_apply_6(v_act_1934_, v_a_2189_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, lean_box(0));
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_dec(v_a_2189_);
lean_dec(v_fst_2007_);
lean_dec_ref(v_allowFailure_1935_);
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
lean_inc(v_a_1940_);
lean_inc_ref(v_a_1939_);
lean_inc(v_a_1938_);
lean_inc_ref(v_a_1937_);
v___x_2194_ = lean_apply_6(v_allowFailure_1935_, v_fst_2007_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, lean_box(0));
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
v___x_2200_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1);
v___x_2201_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2200_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
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
lean_dec_ref(v_allowFailure_1935_);
return v___x_2190_;
}
}
}
}
else
{
lean_dec(v_fst_2007_);
lean_dec_ref(v_allowFailure_1935_);
lean_dec_ref(v_act_1934_);
return v___x_2188_;
}
}
else
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
lean_dec(v_fst_2007_);
lean_dec_ref(v_allowFailure_1935_);
lean_dec_ref(v_act_1934_);
lean_dec_ref(v_cfg_1933_);
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
v___x_2039_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v___x_2019_, v_hasTrace_1948_, v___x_2020_, v_options_1947_, v___x_2022_, v___y_2024_, v___f_2018_, v___x_2038_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
return v___x_2039_;
}
}
}
v___jp_2042_:
{
lean_object* v___x_2046_; 
v___x_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2046_, 0, v_a_2045_);
v___y_2024_ = v___y_2044_;
v___y_2025_ = v___y_2043_;
v_a_2026_ = v___x_2046_;
goto v___jp_2023_;
}
v___jp_2047_:
{
lean_object* v___x_2051_; 
v___x_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2051_, 0, v_a_2050_);
v___y_2024_ = v___y_2049_;
v___y_2025_ = v___y_2048_;
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
v___y_2043_ = v___y_2054_;
v___y_2044_ = v___y_2053_;
v_a_2045_ = v_a_2056_;
goto v___jp_2042_;
}
else
{
lean_object* v_a_2057_; 
v_a_2057_ = lean_ctor_get(v___y_2055_, 0);
lean_inc(v_a_2057_);
lean_dec_ref_known(v___y_2055_, 1);
v___y_2048_ = v___y_2054_;
v___y_2049_ = v___y_2053_;
v_a_2050_ = v_a_2057_;
goto v___jp_2047_;
}
}
v___jp_2058_:
{
if (v___y_2063_ == 0)
{
lean_object* v___x_2064_; 
lean_dec_ref(v___y_2062_);
lean_inc(v_a_1940_);
lean_inc_ref(v_a_1939_);
lean_inc(v_a_1938_);
lean_inc_ref(v_a_1937_);
v___x_2064_ = lean_apply_6(v_allowFailure_1935_, v_fst_2007_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, lean_box(0));
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
v___x_2067_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1);
v___x_2068_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2067_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
v___y_2053_ = v___y_2060_;
v___y_2054_ = v___y_2059_;
v___y_2055_ = v___x_2068_;
goto v___jp_2052_;
}
else
{
v___y_2043_ = v___y_2059_;
v___y_2044_ = v___y_2060_;
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
v___y_2048_ = v___y_2059_;
v___y_2049_ = v___y_2060_;
v_a_2050_ = v_a_2069_;
goto v___jp_2047_;
}
}
else
{
lean_dec(v___y_2061_);
lean_dec(v_fst_2007_);
lean_dec_ref(v_allowFailure_1935_);
v___y_2048_ = v___y_2059_;
v___y_2049_ = v___y_2060_;
v_a_2050_ = v___y_2062_;
goto v___jp_2047_;
}
}
v___jp_2070_:
{
lean_object* v___x_2074_; double v___x_2075_; double v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2080_; 
v___x_2074_ = lean_io_get_num_heartbeats();
v___x_2075_ = lean_float_of_nat(v___y_2072_);
v___x_2076_ = lean_float_of_nat(v___x_2074_);
v___x_2077_ = lean_box_float(v___x_2075_);
v___x_2078_ = lean_box_float(v___x_2076_);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 1, v___x_2078_);
lean_ctor_set(v___x_1945_, 0, v___x_2077_);
v___x_2080_ = v___x_1945_;
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
v___x_2082_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v___x_2019_, v_hasTrace_1948_, v___x_2020_, v_options_1947_, v___x_2022_, v___y_2071_, v___f_2018_, v___x_2081_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
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
lean_dec_ref(v___y_2102_);
lean_inc(v_a_1940_);
lean_inc_ref(v_a_1939_);
lean_inc(v_a_1938_);
lean_inc_ref(v_a_1937_);
v___x_2106_ = lean_apply_6(v_allowFailure_1935_, v_fst_2007_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, lean_box(0));
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
v___x_2109_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1);
v___x_2110_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2109_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
v___y_2095_ = v___y_2101_;
v___y_2096_ = v___y_2104_;
v___y_2097_ = v___x_2110_;
goto v___jp_2094_;
}
else
{
v___y_2085_ = v___y_2101_;
v___y_2086_ = v___y_2104_;
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
v___y_2091_ = v___y_2104_;
v_a_2092_ = v_a_2111_;
goto v___jp_2089_;
}
}
else
{
lean_dec(v___y_2103_);
lean_dec(v_fst_2007_);
lean_dec_ref(v_allowFailure_1935_);
v___y_2090_ = v___y_2101_;
v___y_2091_ = v___y_2104_;
v_a_2092_ = v___y_2102_;
goto v___jp_2089_;
}
}
v___jp_2112_:
{
lean_object* v___x_2113_; lean_object* v_a_2114_; lean_object* v___x_2115_; uint8_t v___x_2116_; 
v___x_2113_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v_a_1940_);
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_a_2114_);
lean_dec_ref(v___x_2113_);
v___x_2115_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2116_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_1947_, v___x_2115_);
if (v___x_2116_ == 0)
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v_cache_2119_; lean_object* v_zetaDeltaFVarIds_2120_; lean_object* v_postponed_2121_; lean_object* v_diag_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2142_; 
lean_del_object(v___x_1945_);
v___x_2117_ = lean_io_mono_nanos_now();
v___x_2118_ = lean_st_ref_take(v_a_1938_);
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
v___x_2128_ = lean_st_ref_set(v_a_1938_, v___x_2127_);
v___x_2129_ = lean_unbox(v_snd_2013_);
lean_dec(v_snd_2013_);
v___x_2130_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_2012_, v___x_2129_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2130_, 1);
v___x_2132_ = lean_box(0);
lean_inc(v_fst_2007_);
v___x_2133_ = l_Lean_MVarId_apply(v_fst_2007_, v_a_2131_, v_cfg_1933_, v___x_2132_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2135_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
lean_inc_n(v_a_2134_, 2);
lean_dec_ref_known(v___x_2133_, 1);
lean_inc(v_a_1940_);
lean_inc_ref(v_a_1939_);
lean_inc(v_a_1938_);
lean_inc_ref(v_a_1937_);
v___x_2135_ = lean_apply_6(v_act_1934_, v_a_2134_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, lean_box(0));
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; 
lean_dec(v_a_2134_);
lean_dec(v_fst_2007_);
lean_dec_ref(v_allowFailure_1935_);
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2136_);
lean_dec_ref_known(v___x_2135_, 1);
v___y_2043_ = v___x_2117_;
v___y_2044_ = v_a_2114_;
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
v___y_2059_ = v___x_2117_;
v___y_2060_ = v_a_2114_;
v___y_2061_ = v_a_2134_;
v___y_2062_ = v_a_2137_;
v___y_2063_ = v___x_2139_;
goto v___jp_2058_;
}
else
{
v___y_2059_ = v___x_2117_;
v___y_2060_ = v_a_2114_;
v___y_2061_ = v_a_2134_;
v___y_2062_ = v_a_2137_;
v___y_2063_ = v___x_2138_;
goto v___jp_2058_;
}
}
}
else
{
lean_dec(v_fst_2007_);
lean_dec_ref(v_allowFailure_1935_);
lean_dec_ref(v_act_1934_);
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
lean_dec_ref(v_allowFailure_1935_);
lean_dec_ref(v_act_1934_);
lean_dec_ref(v_cfg_1933_);
v_a_2140_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___x_2130_, 1);
v___y_2048_ = v___x_2117_;
v___y_2049_ = v_a_2114_;
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
v___x_2145_ = lean_st_ref_take(v_a_1938_);
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
v___x_2155_ = lean_st_ref_set(v_a_1938_, v___x_2154_);
v___x_2156_ = lean_unbox(v_snd_2013_);
lean_dec(v_snd_2013_);
v___x_2157_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_2012_, v___x_2156_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v_a_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
lean_inc(v_a_2158_);
lean_dec_ref_known(v___x_2157_, 1);
v___x_2159_ = lean_box(0);
lean_inc(v_fst_2007_);
v___x_2160_ = l_Lean_MVarId_apply(v_fst_2007_, v_a_2158_, v_cfg_1933_, v___x_2159_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; lean_object* v___x_2162_; 
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc_n(v_a_2161_, 2);
lean_dec_ref_known(v___x_2160_, 1);
lean_inc(v_a_1940_);
lean_inc_ref(v_a_1939_);
lean_inc(v_a_1938_);
lean_inc_ref(v_a_1937_);
v___x_2162_ = lean_apply_6(v_act_1934_, v_a_2161_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, lean_box(0));
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v_a_2163_; 
lean_dec(v_a_2161_);
lean_dec(v_fst_2007_);
lean_dec_ref(v_allowFailure_1935_);
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_a_2163_);
lean_dec_ref_known(v___x_2162_, 1);
v___y_2085_ = v_a_2114_;
v___y_2086_ = v___x_2144_;
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
v___y_2101_ = v_a_2114_;
v___y_2102_ = v_a_2164_;
v___y_2103_ = v_a_2161_;
v___y_2104_ = v___x_2144_;
v___y_2105_ = v___x_2166_;
goto v___jp_2100_;
}
else
{
v___y_2101_ = v_a_2114_;
v___y_2102_ = v_a_2164_;
v___y_2103_ = v_a_2161_;
v___y_2104_ = v___x_2144_;
v___y_2105_ = v___x_2165_;
goto v___jp_2100_;
}
}
}
else
{
lean_dec(v_fst_2007_);
lean_dec_ref(v_allowFailure_1935_);
lean_dec_ref(v_act_1934_);
v___y_2095_ = v_a_2114_;
v___y_2096_ = v___x_2144_;
v___y_2097_ = v___x_2160_;
goto v___jp_2094_;
}
}
else
{
lean_object* v_a_2167_; 
lean_dec(v_fst_2007_);
lean_dec_ref(v_allowFailure_1935_);
lean_dec_ref(v_act_1934_);
lean_dec_ref(v_cfg_1933_);
v_a_2167_ = lean_ctor_get(v___x_2157_, 0);
lean_inc(v_a_2167_);
lean_dec_ref_known(v___x_2157_, 1);
v___y_2090_ = v_a_2114_;
v___y_2091_ = v___x_2144_;
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
lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2289_ = lean_st_ref_get(v___y_2266_);
v___x_2290_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2259_, v___y_2266_, v___y_2268_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v_mctx_2291_; lean_object* v___x_2293_; 
lean_dec_ref_known(v___x_2290_, 1);
v_mctx_2291_ = lean_ctor_get(v___x_2289_, 0);
lean_inc_ref(v_mctx_2291_);
lean_dec(v___x_2289_);
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 1, v_mctx_2291_);
lean_ctor_set(v___x_2279_, 0, v_a_2284_);
v___x_2293_ = v___x_2279_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2284_);
lean_ctor_set(v_reuseFailAlloc_2296_, 1, v_mctx_2291_);
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
lean_dec(v___x_2289_);
lean_dec(v_a_2284_);
lean_del_object(v___x_2279_);
lean_dec(v_snd_2277_);
lean_dec_ref(v_act_2258_);
v_a_2297_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2299_ = v___x_2290_;
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2290_);
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
lean_dec_ref(v_a_2353_);
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
lean_dec(v_a_2382_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1(lean_object* v_leavePercentHeartbeats_2574_, lean_object* v_goal_2575_, lean_object* v___x_2576_, lean_object* v_tactic_2577_, lean_object* v_allowFailure_2578_, uint8_t v_collectAll_2579_, uint8_t v_includeStar_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v___x_2589_; 
v___x_2589_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercentHeartbeats_2574_, v___y_2583_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_a_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_a_2590_);
lean_dec_ref_known(v___x_2589_, 1);
v___x_2591_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___closed__0));
lean_inc(v_goal_2575_);
v___x_2592_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v___x_2591_, v_goal_2575_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; lean_object* v___f_2594_; lean_object* v___x_2595_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
lean_inc(v_a_2593_);
lean_dec_ref_known(v___x_2592_, 1);
v___f_2594_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2594_, 0, v_a_2590_);
lean_closure_set(v___f_2594_, 1, v___x_2576_);
lean_closure_set(v___f_2594_, 2, v_tactic_2577_);
lean_closure_set(v___f_2594_, 3, v_allowFailure_2578_);
lean_inc_ref(v___f_2594_);
v___x_2595_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2594_, v_a_2593_, v_collectAll_2579_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
lean_dec(v_a_2593_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_a_2596_);
if (lean_obj_tag(v_a_2596_) == 0)
{
lean_dec_ref_known(v___x_2595_, 1);
lean_dec_ref(v___f_2594_);
lean_dec(v_goal_2575_);
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
lean_dec_ref_known(v_a_2596_, 1);
lean_dec_ref(v___f_2594_);
lean_dec(v_goal_2575_);
return v___x_2595_;
}
}
}
v___jp_2598_:
{
if (v_includeStar_2580_ == 0)
{
lean_dec_ref_known(v_a_2596_, 1);
lean_dec_ref(v___f_2594_);
lean_dec(v_goal_2575_);
return v___x_2595_;
}
else
{
lean_object* v___x_2599_; 
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
v___x_2611_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2575_, v_mctx_2608_, v_sz_2609_, v___x_2610_, v_a_2600_);
v___x_2612_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2594_, v___x_2611_, v_collectAll_2579_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
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
lean_dec_ref(v___f_2594_);
lean_dec(v_goal_2575_);
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
lean_dec_ref(v___f_2594_);
lean_dec(v_goal_2575_);
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
lean_dec_ref_known(v_a_2596_, 1);
lean_dec_ref(v___f_2594_);
lean_dec(v_goal_2575_);
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
lean_dec_ref(v___f_2594_);
lean_dec(v_goal_2575_);
return v___x_2595_;
}
}
else
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
lean_dec(v_a_2590_);
lean_dec_ref(v_allowFailure_2578_);
lean_dec_ref(v_tactic_2577_);
lean_dec_ref(v___x_2576_);
lean_dec(v_goal_2575_);
v_a_2652_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2592_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2592_);
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
lean_dec_ref(v_allowFailure_2578_);
lean_dec_ref(v_tactic_2577_);
lean_dec_ref(v___x_2576_);
lean_dec(v_goal_2575_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed(lean_object* v_leavePercentHeartbeats_2668_, lean_object* v_goal_2669_, lean_object* v___x_2670_, lean_object* v_tactic_2671_, lean_object* v_allowFailure_2672_, lean_object* v_collectAll_2673_, lean_object* v_includeStar_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
uint8_t v_collectAll_boxed_2680_; uint8_t v_includeStar_boxed_2681_; lean_object* v_res_2682_; 
v_collectAll_boxed_2680_ = lean_unbox(v_collectAll_2673_);
v_includeStar_boxed_2681_ = lean_unbox(v_includeStar_2674_);
v_res_2682_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1(v_leavePercentHeartbeats_2668_, v_goal_2669_, v___x_2670_, v_tactic_2671_, v_allowFailure_2672_, v_collectAll_boxed_2680_, v_includeStar_boxed_2681_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4(lean_object* v_leavePercentHeartbeats_2716_, lean_object* v_goal_2717_, lean_object* v___x_2718_, lean_object* v_tactic_2719_, lean_object* v_allowFailure_2720_, uint8_t v_collectAll_2721_, uint8_t v_includeStar_2722_, uint8_t v___x_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v___x_2732_; 
v___x_2732_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercentHeartbeats_2716_, v___y_2726_);
if (lean_obj_tag(v___x_2732_) == 0)
{
lean_object* v_a_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
lean_inc(v_a_2733_);
lean_dec_ref_known(v___x_2732_, 1);
v___x_2734_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___closed__0));
lean_inc(v_goal_2717_);
v___x_2735_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v___x_2734_, v_goal_2717_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v_a_2736_; lean_object* v___f_2737_; lean_object* v___x_2738_; 
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_a_2736_);
lean_dec_ref_known(v___x_2735_, 1);
v___f_2737_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2737_, 0, v_a_2733_);
lean_closure_set(v___f_2737_, 1, v___x_2718_);
lean_closure_set(v___f_2737_, 2, v_tactic_2719_);
lean_closure_set(v___f_2737_, 3, v_allowFailure_2720_);
lean_inc_ref(v___f_2737_);
v___x_2738_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2737_, v_a_2736_, v_collectAll_2721_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
lean_dec(v_a_2736_);
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v_a_2739_; 
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
lean_inc(v_a_2739_);
if (lean_obj_tag(v_a_2739_) == 0)
{
lean_dec_ref_known(v___x_2738_, 1);
lean_dec_ref(v___f_2737_);
lean_dec(v_goal_2717_);
goto v___jp_2729_;
}
else
{
lean_object* v_val_2740_; uint8_t v___y_2786_; lean_object* v___x_2790_; lean_object* v___x_2791_; uint8_t v___x_2792_; 
v_val_2740_ = lean_ctor_get(v_a_2739_, 0);
v___x_2790_ = lean_unsigned_to_nat(0u);
v___x_2791_ = lean_array_get_size(v_val_2740_);
v___x_2792_ = lean_nat_dec_lt(v___x_2790_, v___x_2791_);
if (v___x_2792_ == 0)
{
v___y_2786_ = v___x_2723_;
goto v___jp_2785_;
}
else
{
if (v___x_2792_ == 0)
{
v___y_2786_ = v___x_2723_;
goto v___jp_2785_;
}
else
{
size_t v___x_2793_; size_t v___x_2794_; uint8_t v___x_2795_; 
v___x_2793_ = ((size_t)0ULL);
v___x_2794_ = lean_usize_of_nat(v___x_2791_);
v___x_2795_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_val_2740_, v___x_2793_, v___x_2794_);
v___y_2786_ = v___x_2795_;
goto v___jp_2785_;
}
}
v___jp_2741_:
{
if (v_includeStar_2722_ == 0)
{
lean_dec_ref_known(v_a_2739_, 1);
lean_dec_ref(v___f_2737_);
lean_dec(v_goal_2717_);
return v___x_2738_;
}
else
{
lean_object* v___x_2742_; 
lean_dec_ref_known(v___x_2738_, 1);
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
v___x_2754_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2717_, v_mctx_2751_, v_sz_2752_, v___x_2753_, v_a_2743_);
v___x_2755_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2737_, v___x_2754_, v_collectAll_2721_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
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
lean_dec_ref(v___f_2737_);
lean_dec(v_goal_2717_);
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
lean_dec_ref(v___f_2737_);
lean_dec(v_goal_2717_);
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
}
v___jp_2785_:
{
if (v___y_2786_ == 0)
{
if (v_collectAll_2721_ == 0)
{
lean_object* v___x_2787_; lean_object* v___x_2788_; uint8_t v___x_2789_; 
v___x_2787_ = lean_array_get_size(v_val_2740_);
v___x_2788_ = lean_unsigned_to_nat(0u);
v___x_2789_ = lean_nat_dec_eq(v___x_2787_, v___x_2788_);
if (v___x_2789_ == 0)
{
lean_dec_ref_known(v_a_2739_, 1);
lean_dec_ref(v___f_2737_);
lean_dec(v_goal_2717_);
return v___x_2738_;
}
else
{
goto v___jp_2741_;
}
}
else
{
goto v___jp_2741_;
}
}
else
{
lean_dec_ref_known(v_a_2739_, 1);
lean_dec_ref(v___f_2737_);
lean_dec(v_goal_2717_);
return v___x_2738_;
}
}
}
}
else
{
lean_dec_ref(v___f_2737_);
lean_dec(v_goal_2717_);
return v___x_2738_;
}
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
lean_dec(v_a_2733_);
lean_dec_ref(v_allowFailure_2720_);
lean_dec_ref(v_tactic_2719_);
lean_dec_ref(v___x_2718_);
lean_dec(v_goal_2717_);
v_a_2796_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2735_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2735_);
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
lean_dec_ref(v_allowFailure_2720_);
lean_dec_ref(v_tactic_2719_);
lean_dec_ref(v___x_2718_);
lean_dec(v_goal_2717_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4___boxed(lean_object* v_leavePercentHeartbeats_2812_, lean_object* v_goal_2813_, lean_object* v___x_2814_, lean_object* v_tactic_2815_, lean_object* v_allowFailure_2816_, lean_object* v_collectAll_2817_, lean_object* v_includeStar_2818_, lean_object* v___x_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
uint8_t v_collectAll_boxed_2825_; uint8_t v_includeStar_boxed_2826_; uint8_t v___x_15813__boxed_2827_; lean_object* v_res_2828_; 
v_collectAll_boxed_2825_ = lean_unbox(v_collectAll_2817_);
v_includeStar_boxed_2826_ = lean_unbox(v_includeStar_2818_);
v___x_15813__boxed_2827_ = lean_unbox(v___x_2819_);
v_res_2828_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4(v_leavePercentHeartbeats_2812_, v_goal_2813_, v___x_2814_, v_tactic_2815_, v_allowFailure_2816_, v_collectAll_boxed_2825_, v_includeStar_boxed_2826_, v___x_15813__boxed_2827_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v_leavePercentHeartbeats_2812_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__5(lean_object* v_leavePercentHeartbeats_2829_, lean_object* v_goal_2830_, lean_object* v___x_2831_, lean_object* v_tactic_2832_, lean_object* v_allowFailure_2833_, uint8_t v_collectAll_2834_, uint8_t v_includeStar_2835_, uint8_t v___x_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_){
_start:
{
lean_object* v___x_2845_; 
v___x_2845_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercentHeartbeats_2829_, v___y_2839_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_object* v_a_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; 
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
lean_inc(v_a_2846_);
lean_dec_ref_known(v___x_2845_, 1);
v___x_2847_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___closed__0));
lean_inc(v_goal_2830_);
v___x_2848_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v___x_2847_, v_goal_2830_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v_a_2849_; lean_object* v___f_2850_; lean_object* v___x_2851_; 
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
lean_inc(v_a_2849_);
lean_dec_ref_known(v___x_2848_, 1);
v___f_2850_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2850_, 0, v_a_2846_);
lean_closure_set(v___f_2850_, 1, v___x_2831_);
lean_closure_set(v___f_2850_, 2, v_tactic_2832_);
lean_closure_set(v___f_2850_, 3, v_allowFailure_2833_);
lean_inc_ref(v___f_2850_);
v___x_2851_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2850_, v_a_2849_, v_collectAll_2834_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_);
lean_dec(v_a_2849_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_object* v_a_2852_; 
v_a_2852_ = lean_ctor_get(v___x_2851_, 0);
lean_inc(v_a_2852_);
if (lean_obj_tag(v_a_2852_) == 0)
{
lean_dec_ref_known(v___x_2851_, 1);
lean_dec_ref(v___f_2850_);
lean_dec(v_goal_2830_);
goto v___jp_2842_;
}
else
{
lean_object* v_val_2853_; lean_object* v___x_2903_; lean_object* v___x_2904_; uint8_t v___x_2905_; 
v_val_2853_ = lean_ctor_get(v_a_2852_, 0);
v___x_2903_ = lean_unsigned_to_nat(0u);
v___x_2904_ = lean_array_get_size(v_val_2853_);
v___x_2905_ = lean_nat_dec_lt(v___x_2903_, v___x_2904_);
if (v___x_2905_ == 0)
{
goto v___jp_2899_;
}
else
{
if (v___x_2905_ == 0)
{
goto v___jp_2899_;
}
else
{
size_t v___x_2906_; size_t v___x_2907_; uint8_t v___x_2908_; 
v___x_2906_ = ((size_t)0ULL);
v___x_2907_ = lean_usize_of_nat(v___x_2904_);
v___x_2908_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_val_2853_, v___x_2906_, v___x_2907_);
if (v___x_2908_ == 0)
{
goto v___jp_2899_;
}
else
{
if (v___x_2836_ == 0)
{
goto v___jp_2898_;
}
else
{
lean_dec_ref_known(v_a_2852_, 1);
lean_dec_ref(v___f_2850_);
lean_dec(v_goal_2830_);
return v___x_2851_;
}
}
}
}
v___jp_2854_:
{
lean_object* v___x_2855_; 
v___x_2855_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2889_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2858_ = v___x_2855_;
v_isShared_2859_ = v_isSharedCheck_2889_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_a_2856_);
lean_dec(v___x_2855_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2889_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; uint8_t v___x_2862_; 
v___x_2860_ = lean_array_get_size(v_a_2856_);
v___x_2861_ = lean_unsigned_to_nat(0u);
v___x_2862_ = lean_nat_dec_eq(v___x_2860_, v___x_2861_);
if (v___x_2862_ == 0)
{
lean_object* v___x_2863_; lean_object* v_mctx_2864_; size_t v_sz_2865_; size_t v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
lean_inc(v_val_2853_);
lean_del_object(v___x_2858_);
lean_dec_ref_known(v_a_2852_, 1);
v___x_2863_ = lean_st_ref_get(v___y_2838_);
v_mctx_2864_ = lean_ctor_get(v___x_2863_, 0);
lean_inc_ref(v_mctx_2864_);
lean_dec(v___x_2863_);
v_sz_2865_ = lean_array_size(v_a_2856_);
v___x_2866_ = ((size_t)0ULL);
v___x_2867_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2830_, v_mctx_2864_, v_sz_2865_, v___x_2866_, v_a_2856_);
v___x_2868_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2850_, v___x_2867_, v_collectAll_2834_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_);
lean_dec_ref(v___x_2867_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2885_; 
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2871_ = v___x_2868_;
v_isShared_2872_ = v_isSharedCheck_2885_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2868_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2885_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
if (lean_obj_tag(v_a_2869_) == 0)
{
lean_del_object(v___x_2871_);
lean_dec(v_val_2853_);
goto v___jp_2842_;
}
else
{
lean_object* v_val_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2884_; 
v_val_2873_ = lean_ctor_get(v_a_2869_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v_a_2869_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2875_ = v_a_2869_;
v_isShared_2876_ = v_isSharedCheck_2884_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_val_2873_);
lean_dec(v_a_2869_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2884_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2877_; lean_object* v___x_2879_; 
v___x_2877_ = l_Array_append___redArg(v_val_2853_, v_val_2873_);
lean_dec(v_val_2873_);
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 0, v___x_2877_);
v___x_2879_ = v___x_2875_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v___x_2877_);
v___x_2879_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
lean_object* v___x_2881_; 
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 0, v___x_2879_);
v___x_2881_ = v___x_2871_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2879_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
}
}
}
else
{
lean_dec(v_val_2853_);
return v___x_2868_;
}
}
else
{
lean_object* v___x_2887_; 
lean_dec(v_a_2856_);
lean_dec_ref(v___f_2850_);
lean_dec(v_goal_2830_);
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 0, v_a_2852_);
v___x_2887_ = v___x_2858_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_a_2852_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
}
}
else
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2897_; 
lean_dec_ref_known(v_a_2852_, 1);
lean_dec_ref(v___f_2850_);
lean_dec(v_goal_2830_);
v_a_2890_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2892_ = v___x_2855_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2855_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2895_; 
if (v_isShared_2893_ == 0)
{
v___x_2895_ = v___x_2892_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2890_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
}
v___jp_2898_:
{
if (v_includeStar_2835_ == 0)
{
if (v___x_2836_ == 0)
{
lean_dec_ref_known(v___x_2851_, 1);
goto v___jp_2854_;
}
else
{
lean_dec_ref_known(v_a_2852_, 1);
lean_dec_ref(v___f_2850_);
lean_dec(v_goal_2830_);
return v___x_2851_;
}
}
else
{
lean_dec_ref_known(v___x_2851_, 1);
goto v___jp_2854_;
}
}
v___jp_2899_:
{
if (v_collectAll_2834_ == 0)
{
if (v___x_2836_ == 0)
{
goto v___jp_2898_;
}
else
{
lean_object* v___x_2900_; lean_object* v___x_2901_; uint8_t v___x_2902_; 
v___x_2900_ = lean_array_get_size(v_val_2853_);
v___x_2901_ = lean_unsigned_to_nat(0u);
v___x_2902_ = lean_nat_dec_eq(v___x_2900_, v___x_2901_);
if (v___x_2902_ == 0)
{
lean_dec_ref_known(v_a_2852_, 1);
lean_dec_ref(v___f_2850_);
lean_dec(v_goal_2830_);
return v___x_2851_;
}
else
{
goto v___jp_2898_;
}
}
}
else
{
goto v___jp_2898_;
}
}
}
}
else
{
lean_dec_ref(v___f_2850_);
lean_dec(v_goal_2830_);
return v___x_2851_;
}
}
else
{
lean_object* v_a_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2916_; 
lean_dec(v_a_2846_);
lean_dec_ref(v_allowFailure_2833_);
lean_dec_ref(v_tactic_2832_);
lean_dec_ref(v___x_2831_);
lean_dec(v_goal_2830_);
v_a_2909_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2911_ = v___x_2848_;
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_a_2909_);
lean_dec(v___x_2848_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2914_; 
if (v_isShared_2912_ == 0)
{
v___x_2914_ = v___x_2911_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_a_2909_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
}
else
{
lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
lean_dec_ref(v_allowFailure_2833_);
lean_dec_ref(v_tactic_2832_);
lean_dec_ref(v___x_2831_);
lean_dec(v_goal_2830_);
v_a_2917_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2919_ = v___x_2845_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v___x_2845_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2917_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
v___jp_2842_:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2843_ = lean_box(0);
v___x_2844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2843_);
return v___x_2844_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__5___boxed(lean_object* v_leavePercentHeartbeats_2925_, lean_object* v_goal_2926_, lean_object* v___x_2927_, lean_object* v_tactic_2928_, lean_object* v_allowFailure_2929_, lean_object* v_collectAll_2930_, lean_object* v_includeStar_2931_, lean_object* v___x_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
uint8_t v_collectAll_boxed_2938_; uint8_t v_includeStar_boxed_2939_; uint8_t v___x_16002__boxed_2940_; lean_object* v_res_2941_; 
v_collectAll_boxed_2938_ = lean_unbox(v_collectAll_2930_);
v_includeStar_boxed_2939_ = lean_unbox(v_includeStar_2931_);
v___x_16002__boxed_2940_ = lean_unbox(v___x_2932_);
v_res_2941_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__5(v_leavePercentHeartbeats_2925_, v_goal_2926_, v___x_2927_, v_tactic_2928_, v_allowFailure_2929_, v_collectAll_boxed_2938_, v_includeStar_boxed_2939_, v___x_16002__boxed_2940_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v_leavePercentHeartbeats_2925_);
return v_res_2941_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(lean_object* v_e_2942_){
_start:
{
if (lean_obj_tag(v_e_2942_) == 0)
{
uint8_t v___x_2943_; 
v___x_2943_ = 2;
return v___x_2943_;
}
else
{
lean_object* v_a_2944_; 
v_a_2944_ = lean_ctor_get(v_e_2942_, 0);
if (lean_obj_tag(v_a_2944_) == 0)
{
uint8_t v___x_2945_; 
v___x_2945_ = 1;
return v___x_2945_;
}
else
{
uint8_t v___x_2946_; 
v___x_2946_ = 0;
return v___x_2946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4___boxed(lean_object* v_e_2947_){
_start:
{
uint8_t v_res_2948_; lean_object* v_r_2949_; 
v_res_2948_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(v_e_2947_);
lean_dec_ref(v_e_2947_);
v_r_2949_ = lean_box(v_res_2948_);
return v_r_2949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(lean_object* v_cls_2950_, uint8_t v_collapsed_2951_, lean_object* v_tag_2952_, lean_object* v_opts_2953_, uint8_t v_clsEnabled_2954_, lean_object* v_oldTraces_2955_, lean_object* v_msg_2956_, lean_object* v_resStartStop_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v_fst_2963_; lean_object* v_snd_2964_; lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v_data_2968_; lean_object* v_fst_2979_; lean_object* v_snd_2980_; lean_object* v___x_2981_; uint8_t v___x_2982_; lean_object* v___y_2984_; lean_object* v_a_2985_; uint8_t v___y_3000_; double v___y_3031_; 
v_fst_2963_ = lean_ctor_get(v_resStartStop_2957_, 0);
lean_inc(v_fst_2963_);
v_snd_2964_ = lean_ctor_get(v_resStartStop_2957_, 1);
lean_inc(v_snd_2964_);
lean_dec_ref(v_resStartStop_2957_);
v_fst_2979_ = lean_ctor_get(v_snd_2964_, 0);
lean_inc(v_fst_2979_);
v_snd_2980_ = lean_ctor_get(v_snd_2964_, 1);
lean_inc(v_snd_2980_);
lean_dec(v_snd_2964_);
v___x_2981_ = l_Lean_trace_profiler;
v___x_2982_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_2953_, v___x_2981_);
if (v___x_2982_ == 0)
{
v___y_3000_ = v___x_2982_;
goto v___jp_2999_;
}
else
{
lean_object* v___x_3036_; uint8_t v___x_3037_; 
v___x_3036_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3037_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_2953_, v___x_3036_);
if (v___x_3037_ == 0)
{
lean_object* v___x_3038_; lean_object* v___x_3039_; double v___x_3040_; double v___x_3041_; double v___x_3042_; 
v___x_3038_ = l_Lean_trace_profiler_threshold;
v___x_3039_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_2953_, v___x_3038_);
v___x_3040_ = lean_float_of_nat(v___x_3039_);
v___x_3041_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3);
v___x_3042_ = lean_float_div(v___x_3040_, v___x_3041_);
v___y_3031_ = v___x_3042_;
goto v___jp_3030_;
}
else
{
lean_object* v___x_3043_; lean_object* v___x_3044_; double v___x_3045_; 
v___x_3043_ = l_Lean_trace_profiler_threshold;
v___x_3044_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_2953_, v___x_3043_);
v___x_3045_ = lean_float_of_nat(v___x_3044_);
v___y_3031_ = v___x_3045_;
goto v___jp_3030_;
}
}
v___jp_2965_:
{
lean_object* v___x_2969_; 
lean_inc(v___y_2966_);
v___x_2969_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(v_oldTraces_2955_, v_data_2968_, v___y_2966_, v___y_2967_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v___x_2970_; 
lean_dec_ref_known(v___x_2969_, 1);
v___x_2970_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_2963_);
return v___x_2970_;
}
else
{
lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2978_; 
lean_dec(v_fst_2963_);
v_a_2971_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2973_ = v___x_2969_;
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2969_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2976_; 
if (v_isShared_2974_ == 0)
{
v___x_2976_ = v___x_2973_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_a_2971_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
}
}
v___jp_2983_:
{
uint8_t v_result_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; double v___x_2989_; lean_object* v_data_2990_; 
v_result_2986_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(v_fst_2963_);
v___x_2987_ = lean_box(v_result_2986_);
v___x_2988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2987_);
v___x_2989_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0);
lean_inc_ref(v_tag_2952_);
lean_inc_ref(v___x_2988_);
lean_inc(v_cls_2950_);
v_data_2990_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2990_, 0, v_cls_2950_);
lean_ctor_set(v_data_2990_, 1, v___x_2988_);
lean_ctor_set(v_data_2990_, 2, v_tag_2952_);
lean_ctor_set_float(v_data_2990_, sizeof(void*)*3, v___x_2989_);
lean_ctor_set_float(v_data_2990_, sizeof(void*)*3 + 8, v___x_2989_);
lean_ctor_set_uint8(v_data_2990_, sizeof(void*)*3 + 16, v_collapsed_2951_);
if (v___x_2982_ == 0)
{
lean_dec_ref_known(v___x_2988_, 1);
lean_dec(v_snd_2980_);
lean_dec(v_fst_2979_);
lean_dec_ref(v_tag_2952_);
lean_dec(v_cls_2950_);
v___y_2966_ = v___y_2984_;
v___y_2967_ = v_a_2985_;
v_data_2968_ = v_data_2990_;
goto v___jp_2965_;
}
else
{
lean_object* v_data_2991_; double v___x_2992_; double v___x_2993_; 
lean_dec_ref_known(v_data_2990_, 3);
v_data_2991_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2991_, 0, v_cls_2950_);
lean_ctor_set(v_data_2991_, 1, v___x_2988_);
lean_ctor_set(v_data_2991_, 2, v_tag_2952_);
v___x_2992_ = lean_unbox_float(v_fst_2979_);
lean_dec(v_fst_2979_);
lean_ctor_set_float(v_data_2991_, sizeof(void*)*3, v___x_2992_);
v___x_2993_ = lean_unbox_float(v_snd_2980_);
lean_dec(v_snd_2980_);
lean_ctor_set_float(v_data_2991_, sizeof(void*)*3 + 8, v___x_2993_);
lean_ctor_set_uint8(v_data_2991_, sizeof(void*)*3 + 16, v_collapsed_2951_);
v___y_2966_ = v___y_2984_;
v___y_2967_ = v_a_2985_;
v_data_2968_ = v_data_2991_;
goto v___jp_2965_;
}
}
v___jp_2994_:
{
lean_object* v_ref_2995_; lean_object* v___x_2996_; 
v_ref_2995_ = lean_ctor_get(v___y_2960_, 5);
lean_inc(v___y_2961_);
lean_inc_ref(v___y_2960_);
lean_inc(v___y_2959_);
lean_inc_ref(v___y_2958_);
lean_inc(v_fst_2963_);
v___x_2996_ = lean_apply_6(v_msg_2956_, v_fst_2963_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, lean_box(0));
if (lean_obj_tag(v___x_2996_) == 0)
{
lean_object* v_a_2997_; 
v_a_2997_ = lean_ctor_get(v___x_2996_, 0);
lean_inc(v_a_2997_);
lean_dec_ref_known(v___x_2996_, 1);
v___y_2984_ = v_ref_2995_;
v_a_2985_ = v_a_2997_;
goto v___jp_2983_;
}
else
{
lean_object* v___x_2998_; 
lean_dec_ref_known(v___x_2996_, 1);
v___x_2998_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2);
v___y_2984_ = v_ref_2995_;
v_a_2985_ = v___x_2998_;
goto v___jp_2983_;
}
}
v___jp_2999_:
{
if (v_clsEnabled_2954_ == 0)
{
if (v___y_3000_ == 0)
{
lean_object* v___x_3001_; lean_object* v_traceState_3002_; lean_object* v_env_3003_; lean_object* v_nextMacroScope_3004_; lean_object* v_ngen_3005_; lean_object* v_auxDeclNGen_3006_; lean_object* v_cache_3007_; lean_object* v_messages_3008_; lean_object* v_infoState_3009_; lean_object* v_snapshotTasks_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3029_; 
lean_dec(v_snd_2980_);
lean_dec(v_fst_2979_);
lean_dec_ref(v_msg_2956_);
lean_dec_ref(v_tag_2952_);
lean_dec(v_cls_2950_);
v___x_3001_ = lean_st_ref_take(v___y_2961_);
v_traceState_3002_ = lean_ctor_get(v___x_3001_, 4);
v_env_3003_ = lean_ctor_get(v___x_3001_, 0);
v_nextMacroScope_3004_ = lean_ctor_get(v___x_3001_, 1);
v_ngen_3005_ = lean_ctor_get(v___x_3001_, 2);
v_auxDeclNGen_3006_ = lean_ctor_get(v___x_3001_, 3);
v_cache_3007_ = lean_ctor_get(v___x_3001_, 5);
v_messages_3008_ = lean_ctor_get(v___x_3001_, 6);
v_infoState_3009_ = lean_ctor_get(v___x_3001_, 7);
v_snapshotTasks_3010_ = lean_ctor_get(v___x_3001_, 8);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3012_ = v___x_3001_;
v_isShared_3013_ = v_isSharedCheck_3029_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_snapshotTasks_3010_);
lean_inc(v_infoState_3009_);
lean_inc(v_messages_3008_);
lean_inc(v_cache_3007_);
lean_inc(v_traceState_3002_);
lean_inc(v_auxDeclNGen_3006_);
lean_inc(v_ngen_3005_);
lean_inc(v_nextMacroScope_3004_);
lean_inc(v_env_3003_);
lean_dec(v___x_3001_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3029_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
uint64_t v_tid_3014_; lean_object* v_traces_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3028_; 
v_tid_3014_ = lean_ctor_get_uint64(v_traceState_3002_, sizeof(void*)*1);
v_traces_3015_ = lean_ctor_get(v_traceState_3002_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v_traceState_3002_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3017_ = v_traceState_3002_;
v_isShared_3018_ = v_isSharedCheck_3028_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_traces_3015_);
lean_dec(v_traceState_3002_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3028_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3019_; lean_object* v___x_3021_; 
v___x_3019_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2955_, v_traces_3015_);
lean_dec_ref(v_traces_3015_);
if (v_isShared_3018_ == 0)
{
lean_ctor_set(v___x_3017_, 0, v___x_3019_);
v___x_3021_ = v___x_3017_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v___x_3019_);
lean_ctor_set_uint64(v_reuseFailAlloc_3027_, sizeof(void*)*1, v_tid_3014_);
v___x_3021_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
lean_object* v___x_3023_; 
if (v_isShared_3013_ == 0)
{
lean_ctor_set(v___x_3012_, 4, v___x_3021_);
v___x_3023_ = v___x_3012_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_env_3003_);
lean_ctor_set(v_reuseFailAlloc_3026_, 1, v_nextMacroScope_3004_);
lean_ctor_set(v_reuseFailAlloc_3026_, 2, v_ngen_3005_);
lean_ctor_set(v_reuseFailAlloc_3026_, 3, v_auxDeclNGen_3006_);
lean_ctor_set(v_reuseFailAlloc_3026_, 4, v___x_3021_);
lean_ctor_set(v_reuseFailAlloc_3026_, 5, v_cache_3007_);
lean_ctor_set(v_reuseFailAlloc_3026_, 6, v_messages_3008_);
lean_ctor_set(v_reuseFailAlloc_3026_, 7, v_infoState_3009_);
lean_ctor_set(v_reuseFailAlloc_3026_, 8, v_snapshotTasks_3010_);
v___x_3023_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3024_ = lean_st_ref_set(v___y_2961_, v___x_3023_);
v___x_3025_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_2963_);
return v___x_3025_;
}
}
}
}
}
else
{
goto v___jp_2994_;
}
}
else
{
goto v___jp_2994_;
}
}
v___jp_3030_:
{
double v___x_3032_; double v___x_3033_; double v___x_3034_; uint8_t v___x_3035_; 
v___x_3032_ = lean_unbox_float(v_snd_2980_);
v___x_3033_ = lean_unbox_float(v_fst_2979_);
v___x_3034_ = lean_float_sub(v___x_3032_, v___x_3033_);
v___x_3035_ = lean_float_decLt(v___y_3031_, v___x_3034_);
v___y_3000_ = v___x_3035_;
goto v___jp_2999_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4___boxed(lean_object* v_cls_3046_, lean_object* v_collapsed_3047_, lean_object* v_tag_3048_, lean_object* v_opts_3049_, lean_object* v_clsEnabled_3050_, lean_object* v_oldTraces_3051_, lean_object* v_msg_3052_, lean_object* v_resStartStop_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_){
_start:
{
uint8_t v_collapsed_boxed_3059_; uint8_t v_clsEnabled_boxed_3060_; lean_object* v_res_3061_; 
v_collapsed_boxed_3059_ = lean_unbox(v_collapsed_3047_);
v_clsEnabled_boxed_3060_ = lean_unbox(v_clsEnabled_3050_);
v_res_3061_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v_cls_3046_, v_collapsed_boxed_3059_, v_tag_3048_, v_opts_3049_, v_clsEnabled_boxed_3060_, v_oldTraces_3051_, v_msg_3052_, v_resStartStop_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec(v___y_3055_);
lean_dec_ref(v___y_3054_);
lean_dec_ref(v_opts_3049_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(lean_object* v_goal_3065_, lean_object* v_tactic_3066_, lean_object* v_allowFailure_3067_, lean_object* v_leavePercentHeartbeats_3068_, uint8_t v_includeStar_3069_, uint8_t v_collectAll_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_){
_start:
{
lean_object* v_options_3076_; lean_object* v_inheritedTraceOptions_3077_; uint8_t v_hasTrace_3078_; lean_object* v___x_3079_; 
v_options_3076_ = lean_ctor_get(v_a_3073_, 2);
v_inheritedTraceOptions_3077_ = lean_ctor_get(v_a_3073_, 13);
v_hasTrace_3078_ = lean_ctor_get_uint8(v_options_3076_, sizeof(void*)*1);
v___x_3079_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
if (v_hasTrace_3078_ == 0)
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___f_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3080_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___closed__0));
v___x_3081_ = lean_box(v_collectAll_3070_);
v___x_3082_ = lean_box(v_includeStar_3069_);
v___f_3083_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed), 12, 7);
lean_closure_set(v___f_3083_, 0, v_leavePercentHeartbeats_3068_);
lean_closure_set(v___f_3083_, 1, v_goal_3065_);
lean_closure_set(v___f_3083_, 2, v___x_3080_);
lean_closure_set(v___f_3083_, 3, v_tactic_3066_);
lean_closure_set(v___f_3083_, 4, v_allowFailure_3067_);
lean_closure_set(v___f_3083_, 5, v___x_3081_);
lean_closure_set(v___f_3083_, 6, v___x_3082_);
v___x_3084_ = lean_box(0);
v___x_3085_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_3079_, v_options_3076_, v___f_3083_, v___x_3084_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_);
return v___x_3085_;
}
else
{
lean_object* v___f_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; uint8_t v___x_3090_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v_a_3094_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v_a_3109_; 
lean_inc(v_goal_3065_);
v___f_3086_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2___boxed), 7, 1);
lean_closure_set(v___f_3086_, 0, v_goal_3065_);
v___x_3087_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_3088_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__4));
v___x_3089_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2);
v___x_3090_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3077_, v_options_3076_, v___x_3089_);
if (v___x_3090_ == 0)
{
lean_object* v___x_3173_; uint8_t v___x_3174_; 
v___x_3173_ = l_Lean_trace_profiler;
v___x_3174_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_3076_, v___x_3173_);
if (v___x_3174_ == 0)
{
uint8_t v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___f_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
lean_dec_ref(v___f_3086_);
v___x_3175_ = 0;
v___x_3176_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3176_, 0, v___x_3175_);
lean_ctor_set_uint8(v___x_3176_, 1, v_hasTrace_3078_);
lean_ctor_set_uint8(v___x_3176_, 2, v_hasTrace_3078_);
lean_ctor_set_uint8(v___x_3176_, 3, v_hasTrace_3078_);
v___x_3177_ = lean_box(v_collectAll_3070_);
v___x_3178_ = lean_box(v_includeStar_3069_);
v___x_3179_ = lean_box(v___x_3174_);
v___f_3180_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4___boxed), 13, 8);
lean_closure_set(v___f_3180_, 0, v_leavePercentHeartbeats_3068_);
lean_closure_set(v___f_3180_, 1, v_goal_3065_);
lean_closure_set(v___f_3180_, 2, v___x_3176_);
lean_closure_set(v___f_3180_, 3, v_tactic_3066_);
lean_closure_set(v___f_3180_, 4, v_allowFailure_3067_);
lean_closure_set(v___f_3180_, 5, v___x_3177_);
lean_closure_set(v___f_3180_, 6, v___x_3178_);
lean_closure_set(v___f_3180_, 7, v___x_3179_);
v___x_3181_ = lean_box(0);
v___x_3182_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_3079_, v_options_3076_, v___f_3180_, v___x_3181_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_);
return v___x_3182_;
}
else
{
goto v___jp_3118_;
}
}
else
{
goto v___jp_3118_;
}
v___jp_3091_:
{
lean_object* v___x_3095_; double v___x_3096_; double v___x_3097_; double v___x_3098_; double v___x_3099_; double v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3095_ = lean_io_mono_nanos_now();
v___x_3096_ = lean_float_of_nat(v___y_3092_);
v___x_3097_ = lean_float_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3);
v___x_3098_ = lean_float_div(v___x_3096_, v___x_3097_);
v___x_3099_ = lean_float_of_nat(v___x_3095_);
v___x_3100_ = lean_float_div(v___x_3099_, v___x_3097_);
v___x_3101_ = lean_box_float(v___x_3098_);
v___x_3102_ = lean_box_float(v___x_3100_);
v___x_3103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3101_);
lean_ctor_set(v___x_3103_, 1, v___x_3102_);
v___x_3104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3104_, 0, v_a_3094_);
lean_ctor_set(v___x_3104_, 1, v___x_3103_);
v___x_3105_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v___x_3087_, v_hasTrace_3078_, v___x_3088_, v_options_3076_, v___x_3090_, v___y_3093_, v___f_3086_, v___x_3104_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_);
return v___x_3105_;
}
v___jp_3106_:
{
lean_object* v___x_3110_; double v___x_3111_; double v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3110_ = lean_io_get_num_heartbeats();
v___x_3111_ = lean_float_of_nat(v___y_3107_);
v___x_3112_ = lean_float_of_nat(v___x_3110_);
v___x_3113_ = lean_box_float(v___x_3111_);
v___x_3114_ = lean_box_float(v___x_3112_);
v___x_3115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3113_);
lean_ctor_set(v___x_3115_, 1, v___x_3114_);
v___x_3116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3116_, 0, v_a_3109_);
lean_ctor_set(v___x_3116_, 1, v___x_3115_);
v___x_3117_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v___x_3087_, v_hasTrace_3078_, v___x_3088_, v_options_3076_, v___x_3090_, v___y_3108_, v___f_3086_, v___x_3116_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_);
return v___x_3117_;
}
v___jp_3118_:
{
lean_object* v___x_3119_; lean_object* v_a_3120_; lean_object* v___x_3121_; uint8_t v___x_3122_; 
v___x_3119_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v_a_3074_);
v_a_3120_ = lean_ctor_get(v___x_3119_, 0);
lean_inc(v_a_3120_);
lean_dec_ref(v___x_3119_);
v___x_3121_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3122_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_3076_, v___x_3121_);
if (v___x_3122_ == 0)
{
lean_object* v___x_3123_; uint8_t v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___f_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3123_ = lean_io_mono_nanos_now();
v___x_3124_ = 0;
v___x_3125_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3125_, 0, v___x_3124_);
lean_ctor_set_uint8(v___x_3125_, 1, v_hasTrace_3078_);
lean_ctor_set_uint8(v___x_3125_, 2, v_hasTrace_3078_);
lean_ctor_set_uint8(v___x_3125_, 3, v_hasTrace_3078_);
v___x_3126_ = lean_box(v_collectAll_3070_);
v___x_3127_ = lean_box(v_includeStar_3069_);
v___x_3128_ = lean_box(v___x_3122_);
v___f_3129_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4___boxed), 13, 8);
lean_closure_set(v___f_3129_, 0, v_leavePercentHeartbeats_3068_);
lean_closure_set(v___f_3129_, 1, v_goal_3065_);
lean_closure_set(v___f_3129_, 2, v___x_3125_);
lean_closure_set(v___f_3129_, 3, v_tactic_3066_);
lean_closure_set(v___f_3129_, 4, v_allowFailure_3067_);
lean_closure_set(v___f_3129_, 5, v___x_3126_);
lean_closure_set(v___f_3129_, 6, v___x_3127_);
lean_closure_set(v___f_3129_, 7, v___x_3128_);
v___x_3130_ = lean_box(0);
v___x_3131_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_3079_, v_options_3076_, v___f_3129_, v___x_3130_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_);
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3139_; 
v_a_3132_ = lean_ctor_get(v___x_3131_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3134_ = v___x_3131_;
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3131_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3137_; 
if (v_isShared_3135_ == 0)
{
lean_ctor_set_tag(v___x_3134_, 1);
v___x_3137_ = v___x_3134_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_a_3132_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
v___y_3092_ = v___x_3123_;
v___y_3093_ = v_a_3120_;
v_a_3094_ = v___x_3137_;
goto v___jp_3091_;
}
}
}
else
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
v_a_3140_ = lean_ctor_get(v___x_3131_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_3131_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3131_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
lean_ctor_set_tag(v___x_3142_, 0);
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3140_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
v___y_3092_ = v___x_3123_;
v___y_3093_ = v_a_3120_;
v_a_3094_ = v___x_3145_;
goto v___jp_3091_;
}
}
}
}
else
{
lean_object* v___x_3148_; uint8_t v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___f_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
v___x_3148_ = lean_io_get_num_heartbeats();
v___x_3149_ = 0;
v___x_3150_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3150_, 0, v___x_3149_);
lean_ctor_set_uint8(v___x_3150_, 1, v___x_3122_);
lean_ctor_set_uint8(v___x_3150_, 2, v___x_3122_);
lean_ctor_set_uint8(v___x_3150_, 3, v___x_3122_);
v___x_3151_ = lean_box(v_collectAll_3070_);
v___x_3152_ = lean_box(v_includeStar_3069_);
v___x_3153_ = lean_box(v___x_3122_);
v___f_3154_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__5___boxed), 13, 8);
lean_closure_set(v___f_3154_, 0, v_leavePercentHeartbeats_3068_);
lean_closure_set(v___f_3154_, 1, v_goal_3065_);
lean_closure_set(v___f_3154_, 2, v___x_3150_);
lean_closure_set(v___f_3154_, 3, v_tactic_3066_);
lean_closure_set(v___f_3154_, 4, v_allowFailure_3067_);
lean_closure_set(v___f_3154_, 5, v___x_3151_);
lean_closure_set(v___f_3154_, 6, v___x_3152_);
lean_closure_set(v___f_3154_, 7, v___x_3153_);
v___x_3155_ = lean_box(0);
v___x_3156_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_3079_, v_options_3076_, v___f_3154_, v___x_3155_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_);
if (lean_obj_tag(v___x_3156_) == 0)
{
lean_object* v_a_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3164_; 
v_a_3157_ = lean_ctor_get(v___x_3156_, 0);
v_isSharedCheck_3164_ = !lean_is_exclusive(v___x_3156_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3159_ = v___x_3156_;
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_a_3157_);
lean_dec(v___x_3156_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v___x_3162_; 
if (v_isShared_3160_ == 0)
{
lean_ctor_set_tag(v___x_3159_, 1);
v___x_3162_ = v___x_3159_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v_a_3157_);
v___x_3162_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
v___y_3107_ = v___x_3148_;
v___y_3108_ = v_a_3120_;
v_a_3109_ = v___x_3162_;
goto v___jp_3106_;
}
}
}
else
{
lean_object* v_a_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3172_; 
v_a_3165_ = lean_ctor_get(v___x_3156_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_3156_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3167_ = v___x_3156_;
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_a_3165_);
lean_dec(v___x_3156_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3170_; 
if (v_isShared_3168_ == 0)
{
lean_ctor_set_tag(v___x_3167_, 0);
v___x_3170_ = v___x_3167_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_a_3165_);
v___x_3170_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
v___y_3107_ = v___x_3148_;
v___y_3108_ = v_a_3120_;
v_a_3109_ = v___x_3170_;
goto v___jp_3106_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___boxed(lean_object* v_goal_3183_, lean_object* v_tactic_3184_, lean_object* v_allowFailure_3185_, lean_object* v_leavePercentHeartbeats_3186_, lean_object* v_includeStar_3187_, lean_object* v_collectAll_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_){
_start:
{
uint8_t v_includeStar_boxed_3194_; uint8_t v_collectAll_boxed_3195_; lean_object* v_res_3196_; 
v_includeStar_boxed_3194_ = lean_unbox(v_includeStar_3187_);
v_collectAll_boxed_3195_ = lean_unbox(v_collectAll_3188_);
v_res_3196_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(v_goal_3183_, v_tactic_3184_, v_allowFailure_3185_, v_leavePercentHeartbeats_3186_, v_includeStar_boxed_3194_, v_collectAll_boxed_3195_, v_a_3189_, v_a_3190_, v_a_3191_, v_a_3192_);
lean_dec(v_a_3192_);
lean_dec_ref(v_a_3191_);
lean_dec(v_a_3190_);
lean_dec_ref(v_a_3189_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearch(lean_object* v_goal_3197_, lean_object* v_tactic_3198_, lean_object* v_allowFailure_3199_, lean_object* v_leavePercentHeartbeats_3200_, uint8_t v_includeStar_3201_, uint8_t v_collectAll_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_){
_start:
{
lean_object* v___x_3208_; 
v___x_3208_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(v_goal_3197_, v_tactic_3198_, v_allowFailure_3199_, v_leavePercentHeartbeats_3200_, v_includeStar_3201_, v_collectAll_3202_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearch___boxed(lean_object* v_goal_3209_, lean_object* v_tactic_3210_, lean_object* v_allowFailure_3211_, lean_object* v_leavePercentHeartbeats_3212_, lean_object* v_includeStar_3213_, lean_object* v_collectAll_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_){
_start:
{
uint8_t v_includeStar_boxed_3220_; uint8_t v_collectAll_boxed_3221_; lean_object* v_res_3222_; 
v_includeStar_boxed_3220_ = lean_unbox(v_includeStar_3213_);
v_collectAll_boxed_3221_ = lean_unbox(v_collectAll_3214_);
v_res_3222_ = l_Lean_Meta_LibrarySearch_librarySearch(v_goal_3209_, v_tactic_3210_, v_allowFailure_3211_, v_leavePercentHeartbeats_3212_, v_includeStar_boxed_3220_, v_collectAll_boxed_3221_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_);
lean_dec(v_a_3218_);
lean_dec_ref(v_a_3217_);
lean_dec(v_a_3216_);
lean_dec_ref(v_a_3215_);
return v_res_3222_;
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
