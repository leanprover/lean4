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
static const lean_ctor_object l_Lean_Meta_LibrarySearch_grindDischarger___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*13 + 32, .m_other = 13, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1)),((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1048576) << 1) | 1)),((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 0, 1, 0, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 1, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 1, 0, 1, 1)}};
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
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_grindDischarger(lean_object* v_mvarId_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_){
_start:
{
lean_object* v___y_149_; uint8_t v___y_150_; lean_object* v_a_155_; lean_object* v___y_159_; lean_object* v___x_169_; 
lean_inc(v_mvarId_142_);
v___x_169_ = l_Lean_MVarId_getType(v_mvarId_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v_a_170_; lean_object* v___x_171_; 
v_a_170_ = lean_ctor_get(v___x_169_, 0);
lean_inc_n(v_a_170_, 2);
lean_dec_ref_known(v___x_169_, 1);
v___x_171_ = l_Lean_Meta_getLevel(v_a_170_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
if (lean_obj_tag(v___x_171_) == 0)
{
lean_object* v_a_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_a_172_ = lean_ctor_get(v___x_171_, 0);
lean_inc(v_a_172_);
lean_dec_ref_known(v___x_171_, 1);
v___x_173_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_grindDischarger___closed__2));
v___x_174_ = lean_box(0);
v___x_175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_175_, 0, v_a_172_);
lean_ctor_set(v___x_175_, 1, v___x_174_);
v___x_176_ = l_Lean_Expr_const___override(v___x_173_, v___x_175_);
v___x_177_ = l_Lean_Expr_app___override(v___x_176_, v_a_170_);
v___x_178_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_grindDischarger___closed__3));
v___x_179_ = lean_box(0);
v___x_180_ = l_Lean_MVarId_apply(v_mvarId_142_, v___x_177_, v___x_178_, v___x_179_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v_a_181_; 
v_a_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_a_181_);
lean_dec_ref_known(v___x_180_, 1);
if (lean_obj_tag(v_a_181_) == 1)
{
lean_object* v_tail_182_; 
v_tail_182_ = lean_ctor_get(v_a_181_, 1);
if (lean_obj_tag(v_tail_182_) == 0)
{
lean_object* v_head_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
lean_inc(v_tail_182_);
v_head_183_ = lean_ctor_get(v_a_181_, 0);
lean_inc(v_head_183_);
lean_dec_ref_known(v_a_181_, 2);
v___x_184_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_grindDischarger___closed__4));
v___x_185_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_184_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_207_; 
v_a_186_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_207_ == 0)
{
v___x_188_ = v___x_185_;
v_isShared_189_ = v_isSharedCheck_207_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_185_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_207_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lean_Meta_Grind_main(v_head_183_, v_a_186_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
if (lean_obj_tag(v___x_190_) == 0)
{
lean_object* v_a_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_205_; 
v_a_191_ = lean_ctor_get(v___x_190_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_190_);
if (v_isSharedCheck_205_ == 0)
{
v___x_193_ = v___x_190_;
v_isShared_194_ = v_isSharedCheck_205_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_a_191_);
lean_dec(v___x_190_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_205_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
uint8_t v___x_195_; 
v___x_195_ = l_Lean_Meta_Grind_Result_hasFailed(v_a_191_);
lean_dec(v_a_191_);
if (v___x_195_ == 0)
{
lean_object* v___x_197_; 
if (v_isShared_189_ == 0)
{
lean_ctor_set_tag(v___x_188_, 1);
lean_ctor_set(v___x_188_, 0, v_tail_182_);
v___x_197_ = v___x_188_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_tail_182_);
v___x_197_ = v_reuseFailAlloc_201_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_199_; 
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 0, v___x_197_);
v___x_199_ = v___x_193_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_197_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
else
{
lean_object* v___x_203_; 
lean_del_object(v___x_188_);
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 0, v___x_179_);
v___x_203_ = v___x_193_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_179_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
else
{
lean_object* v_a_206_; 
lean_del_object(v___x_188_);
v_a_206_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_a_206_);
lean_dec_ref_known(v___x_190_, 1);
v_a_155_ = v_a_206_;
goto v___jp_154_;
}
}
}
else
{
lean_object* v_a_208_; 
lean_dec(v_head_183_);
v_a_208_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_a_208_);
lean_dec_ref_known(v___x_185_, 1);
v_a_155_ = v_a_208_;
goto v___jp_154_;
}
}
else
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_Meta_LibrarySearch_grindDischarger___lam__0(v_a_181_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
lean_dec_ref_known(v_a_181_, 2);
v___y_159_ = v___x_209_;
goto v___jp_158_;
}
}
else
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_Meta_LibrarySearch_grindDischarger___lam__0(v_a_181_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
lean_dec(v_a_181_);
v___y_159_ = v___x_210_;
goto v___jp_158_;
}
}
else
{
lean_object* v_a_211_; 
v_a_211_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_a_211_);
lean_dec_ref_known(v___x_180_, 1);
v_a_155_ = v_a_211_;
goto v___jp_154_;
}
}
else
{
lean_object* v_a_212_; 
lean_dec(v_a_170_);
lean_dec(v_mvarId_142_);
v_a_212_ = lean_ctor_get(v___x_171_, 0);
lean_inc(v_a_212_);
lean_dec_ref_known(v___x_171_, 1);
v_a_155_ = v_a_212_;
goto v___jp_154_;
}
}
else
{
lean_object* v_a_213_; 
lean_dec(v_mvarId_142_);
v_a_213_ = lean_ctor_get(v___x_169_, 0);
lean_inc(v_a_213_);
lean_dec_ref_known(v___x_169_, 1);
v_a_155_ = v_a_213_;
goto v___jp_154_;
}
v___jp_148_:
{
if (v___y_150_ == 0)
{
lean_object* v___x_151_; lean_object* v___x_152_; 
lean_dec_ref(v___y_149_);
v___x_151_ = lean_box(0);
v___x_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
return v___x_152_;
}
else
{
lean_object* v___x_153_; 
v___x_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_153_, 0, v___y_149_);
return v___x_153_;
}
}
v___jp_154_:
{
uint8_t v___x_156_; 
v___x_156_ = l_Lean_Exception_isInterrupt(v_a_155_);
if (v___x_156_ == 0)
{
uint8_t v___x_157_; 
lean_inc_ref(v_a_155_);
v___x_157_ = l_Lean_Exception_isRuntime(v_a_155_);
v___y_149_ = v_a_155_;
v___y_150_ = v___x_157_;
goto v___jp_148_;
}
else
{
v___y_149_ = v_a_155_;
v___y_150_ = v___x_156_;
goto v___jp_148_;
}
}
v___jp_158_:
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_168_; 
v_a_160_ = lean_ctor_get(v___y_159_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___y_159_);
if (v_isSharedCheck_168_ == 0)
{
v___x_162_ = v___y_159_;
v_isShared_163_ = v_isSharedCheck_168_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___y_159_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_168_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v_a_164_; lean_object* v___x_166_; 
v_a_164_ = lean_ctor_get(v_a_160_, 0);
lean_inc(v_a_164_);
lean_dec(v_a_160_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 0, v_a_164_);
v___x_166_ = v___x_162_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_a_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_grindDischarger___boxed(lean_object* v_mvarId_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_Meta_LibrarySearch_grindDischarger(v_mvarId_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_);
lean_dec(v_a_218_);
lean_dec_ref(v_a_217_);
lean_dec(v_a_216_);
lean_dec_ref(v_a_215_);
return v_res_220_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_tryDischarger___lam__1(uint8_t v___x_221_, lean_object* v_x_222_){
_start:
{
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryDischarger___lam__1___boxed(lean_object* v___x_223_, lean_object* v_x_224_){
_start:
{
uint8_t v___x_3971__boxed_225_; uint8_t v_res_226_; lean_object* v_r_227_; 
v___x_3971__boxed_225_ = lean_unbox(v___x_223_);
v_res_226_ = l_Lean_Meta_LibrarySearch_tryDischarger___lam__1(v___x_3971__boxed_225_, v_x_224_);
lean_dec(v_x_224_);
v_r_227_ = lean_box(v_res_226_);
return v_r_227_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_tryDischarger___closed__11(void){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_Array_mkArray0(lean_box(0));
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryDischarger(lean_object* v_mvarId_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_){
_start:
{
lean_object* v___y_271_; uint8_t v___y_272_; lean_object* v_a_277_; lean_object* v___y_281_; lean_object* v___x_291_; 
lean_inc(v_mvarId_264_);
v___x_291_ = l_Lean_MVarId_getType(v_mvarId_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v_a_292_; lean_object* v___x_293_; 
v_a_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc_n(v_a_292_, 2);
lean_dec_ref_known(v___x_291_, 1);
v___x_293_ = l_Lean_Meta_getLevel(v_a_292_, v_a_265_, v_a_266_, v_a_267_, v_a_268_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_a_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v_a_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_a_294_);
lean_dec_ref_known(v___x_293_, 1);
v___x_295_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryDischarger___closed__1));
v___x_296_ = lean_box(0);
v___x_297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_297_, 0, v_a_294_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
v___x_298_ = l_Lean_Expr_const___override(v___x_295_, v___x_297_);
v___x_299_ = l_Lean_Expr_app___override(v___x_298_, v_a_292_);
v___x_300_ = 0;
v___x_301_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_grindDischarger___closed__3));
v___x_302_ = lean_box(0);
v___x_303_ = l_Lean_MVarId_apply(v_mvarId_264_, v___x_299_, v___x_301_, v___x_302_, v_a_265_, v_a_266_, v_a_267_, v_a_268_);
if (lean_obj_tag(v___x_303_) == 0)
{
lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_354_; 
v_a_304_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_354_ == 0)
{
v___x_306_ = v___x_303_;
v_isShared_307_ = v_isSharedCheck_354_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_dec(v___x_303_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_354_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
if (lean_obj_tag(v_a_304_) == 1)
{
lean_object* v_tail_308_; 
v_tail_308_ = lean_ctor_get(v_a_304_, 1);
if (lean_obj_tag(v_tail_308_) == 0)
{
lean_object* v_head_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_350_; 
lean_inc(v_tail_308_);
v_head_309_ = lean_ctor_get(v_a_304_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v_a_304_);
if (v_isSharedCheck_350_ == 0)
{
lean_object* v_unused_351_; 
v_unused_351_ = lean_ctor_get(v_a_304_, 1);
lean_dec(v_unused_351_);
v___x_311_ = v_a_304_;
v_isShared_312_ = v_isSharedCheck_350_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_head_309_);
lean_dec(v_a_304_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_350_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v_ref_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_318_; 
v_ref_313_ = lean_ctor_get(v_a_267_, 5);
v___x_314_ = l_Lean_SourceInfo_fromRef(v_ref_313_, v___x_300_);
v___x_315_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryDischarger___closed__5));
v___x_316_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryDischarger___closed__6));
lean_inc(v___x_314_);
if (v_isShared_312_ == 0)
{
lean_ctor_set_tag(v___x_311_, 2);
lean_ctor_set(v___x_311_, 1, v___x_316_);
lean_ctor_set(v___x_311_, 0, v___x_314_);
v___x_318_ = v___x_311_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_314_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v___x_316_);
v___x_318_ = v_reuseFailAlloc_349_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_319_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryDischarger___closed__8));
v___x_320_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryDischarger___closed__10));
v___x_321_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_tryDischarger___closed__11, &l_Lean_Meta_LibrarySearch_tryDischarger___closed__11_once, _init_l_Lean_Meta_LibrarySearch_tryDischarger___closed__11);
lean_inc_n(v___x_314_, 2);
v___x_322_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_322_, 0, v___x_314_);
lean_ctor_set(v___x_322_, 1, v___x_320_);
lean_ctor_set(v___x_322_, 2, v___x_321_);
v___x_323_ = l_Lean_Syntax_node1(v___x_314_, v___x_319_, v___x_322_);
v___x_324_ = l_Lean_Syntax_node2(v___x_314_, v___x_315_, v___x_318_, v___x_323_);
v___x_325_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_325_, 0, v___x_324_);
v___x_326_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSuppressedMessages___boxed), 11, 2);
lean_closure_set(v___x_326_, 0, lean_box(0));
lean_closure_set(v___x_326_, 1, v___x_325_);
v___x_327_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_run___boxed), 9, 2);
lean_closure_set(v___x_327_, 0, v_head_309_);
lean_closure_set(v___x_327_, 1, v___x_326_);
v___x_328_ = lean_box(1);
v___x_329_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryDischarger___closed__13));
v___x_330_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_330_, 0, v___x_296_);
lean_ctor_set(v___x_330_, 1, v___x_328_);
lean_ctor_set(v___x_330_, 2, v_tail_308_);
lean_ctor_set(v___x_330_, 3, v___x_296_);
lean_ctor_set(v___x_330_, 4, v___x_296_);
lean_ctor_set(v___x_330_, 5, v___x_328_);
lean_ctor_set(v___x_330_, 6, v___x_296_);
v___x_331_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_327_, v___x_329_, v___x_330_, v_a_265_, v_a_266_, v_a_267_, v_a_268_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_347_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_347_ == 0)
{
v___x_334_ = v___x_331_;
v_isShared_335_ = v_isSharedCheck_347_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_331_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_347_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v_fst_336_; uint8_t v___x_337_; 
v_fst_336_ = lean_ctor_get(v_a_332_, 0);
lean_inc(v_fst_336_);
lean_dec(v_a_332_);
v___x_337_ = l_List_isEmpty___redArg(v_fst_336_);
lean_dec(v_fst_336_);
if (v___x_337_ == 0)
{
lean_object* v___x_339_; 
lean_del_object(v___x_306_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_302_);
v___x_339_ = v___x_334_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_302_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
else
{
lean_object* v___x_342_; 
if (v_isShared_307_ == 0)
{
lean_ctor_set_tag(v___x_306_, 1);
lean_ctor_set(v___x_306_, 0, v_tail_308_);
v___x_342_ = v___x_306_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_tail_308_);
v___x_342_ = v_reuseFailAlloc_346_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_object* v___x_344_; 
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_342_);
v___x_344_ = v___x_334_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_342_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
}
else
{
lean_object* v_a_348_; 
lean_del_object(v___x_306_);
v_a_348_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_348_);
lean_dec_ref_known(v___x_331_, 1);
v_a_277_ = v_a_348_;
goto v___jp_276_;
}
}
}
}
else
{
lean_object* v___x_352_; 
lean_del_object(v___x_306_);
v___x_352_ = l_Lean_Meta_LibrarySearch_grindDischarger___lam__0(v_a_304_, v_a_265_, v_a_266_, v_a_267_, v_a_268_);
lean_dec_ref_known(v_a_304_, 2);
v___y_281_ = v___x_352_;
goto v___jp_280_;
}
}
else
{
lean_object* v___x_353_; 
lean_del_object(v___x_306_);
v___x_353_ = l_Lean_Meta_LibrarySearch_grindDischarger___lam__0(v_a_304_, v_a_265_, v_a_266_, v_a_267_, v_a_268_);
lean_dec(v_a_304_);
v___y_281_ = v___x_353_;
goto v___jp_280_;
}
}
}
else
{
lean_object* v_a_355_; 
v_a_355_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_a_355_);
lean_dec_ref_known(v___x_303_, 1);
v_a_277_ = v_a_355_;
goto v___jp_276_;
}
}
else
{
lean_object* v_a_356_; 
lean_dec(v_a_292_);
lean_dec(v_mvarId_264_);
v_a_356_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_a_356_);
lean_dec_ref_known(v___x_293_, 1);
v_a_277_ = v_a_356_;
goto v___jp_276_;
}
}
else
{
lean_object* v_a_357_; 
lean_dec(v_mvarId_264_);
v_a_357_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_a_357_);
lean_dec_ref_known(v___x_291_, 1);
v_a_277_ = v_a_357_;
goto v___jp_276_;
}
v___jp_270_:
{
if (v___y_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; 
lean_dec_ref(v___y_271_);
v___x_273_ = lean_box(0);
v___x_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
return v___x_274_;
}
else
{
lean_object* v___x_275_; 
v___x_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_275_, 0, v___y_271_);
return v___x_275_;
}
}
v___jp_276_:
{
uint8_t v___x_278_; 
v___x_278_ = l_Lean_Exception_isInterrupt(v_a_277_);
if (v___x_278_ == 0)
{
uint8_t v___x_279_; 
lean_inc_ref(v_a_277_);
v___x_279_ = l_Lean_Exception_isRuntime(v_a_277_);
v___y_271_ = v_a_277_;
v___y_272_ = v___x_279_;
goto v___jp_270_;
}
else
{
v___y_271_ = v_a_277_;
v___y_272_ = v___x_278_;
goto v___jp_270_;
}
}
v___jp_280_:
{
lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_290_; 
v_a_282_ = lean_ctor_get(v___y_281_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___y_281_);
if (v_isSharedCheck_290_ == 0)
{
v___x_284_ = v___y_281_;
v_isShared_285_ = v_isSharedCheck_290_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___y_281_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_290_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v_a_286_; lean_object* v___x_288_; 
v_a_286_ = lean_ctor_get(v_a_282_, 0);
lean_inc(v_a_286_);
lean_dec(v_a_282_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 0, v_a_286_);
v___x_288_ = v___x_284_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_a_286_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryDischarger___boxed(lean_object* v_mvarId_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_Meta_LibrarySearch_tryDischarger(v_mvarId_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
lean_dec(v_a_360_);
lean_dec_ref(v_a_359_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(lean_object* v_msgData_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v___x_371_; lean_object* v_env_372_; lean_object* v___x_373_; lean_object* v_mctx_374_; lean_object* v_lctx_375_; lean_object* v_options_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_371_ = lean_st_ref_get(v___y_369_);
v_env_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc_ref(v_env_372_);
lean_dec(v___x_371_);
v___x_373_ = lean_st_ref_get(v___y_367_);
v_mctx_374_ = lean_ctor_get(v___x_373_, 0);
lean_inc_ref(v_mctx_374_);
lean_dec(v___x_373_);
v_lctx_375_ = lean_ctor_get(v___y_366_, 2);
v_options_376_ = lean_ctor_get(v___y_368_, 2);
lean_inc_ref(v_options_376_);
lean_inc_ref(v_lctx_375_);
v___x_377_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_377_, 0, v_env_372_);
lean_ctor_set(v___x_377_, 1, v_mctx_374_);
lean_ctor_set(v___x_377_, 2, v_lctx_375_);
lean_ctor_set(v___x_377_, 3, v_options_376_);
v___x_378_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
lean_ctor_set(v___x_378_, 1, v_msgData_365_);
v___x_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0___boxed(lean_object* v_msgData_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(v_msgData_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(lean_object* v_msg_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v_ref_393_; lean_object* v___x_394_; lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_403_; 
v_ref_393_ = lean_ctor_get(v___y_390_, 5);
v___x_394_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(v_msg_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
v_a_395_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_403_ == 0)
{
v___x_397_ = v___x_394_;
v_isShared_398_ = v_isSharedCheck_403_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_394_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_403_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v___x_401_; 
lean_inc(v_ref_393_);
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v_ref_393_);
lean_ctor_set(v___x_399_, 1, v_a_395_);
if (v_isShared_398_ == 0)
{
lean_ctor_set_tag(v___x_397_, 1);
lean_ctor_set(v___x_397_, 0, v___x_399_);
v___x_401_ = v___x_397_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_399_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg___boxed(lean_object* v_msg_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v_msg_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
return v_res_410_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__0));
v___x_413_ = l_Lean_stringToMessageData(v___x_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__0(lean_object* v_x_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1);
v___x_421_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_420_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__0___boxed(lean_object* v_x_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_Meta_LibrarySearch_solveByElim___lam__0(v_x_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v_x_422_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__1(lean_object* v_x_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
uint8_t v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_435_ = 0;
v___x_436_ = lean_box(v___x_435_);
v___x_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__1___boxed(lean_object* v_x_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_Meta_LibrarySearch_solveByElim___lam__1(v_x_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v_x_438_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__2(lean_object* v_x_445_, lean_object* v_x_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = lean_box(0);
v___x_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__2___boxed(lean_object* v_x_454_, lean_object* v_x_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_Meta_LibrarySearch_solveByElim___lam__2(v_x_454_, v_x_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v_x_455_);
lean_dec(v_x_454_);
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
lean_ctor_set(v___x_486_, 1, v___f_484_);
lean_ctor_set(v___x_486_, 2, v___f_483_);
lean_ctor_set(v___x_486_, 3, v___f_482_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(uint8_t v_x_546_){
_start:
{
switch(v_x_546_)
{
case 0:
{
lean_object* v___x_547_; 
v___x_547_ = lean_unsigned_to_nat(0u);
return v___x_547_;
}
case 1:
{
lean_object* v___x_548_; 
v___x_548_ = lean_unsigned_to_nat(1u);
return v___x_548_;
}
default: 
{
lean_object* v___x_549_; 
v___x_549_ = lean_unsigned_to_nat(2u);
return v___x_549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx___boxed(lean_object* v_x_550_){
_start:
{
uint8_t v_x_boxed_551_; lean_object* v_res_552_; 
v_x_boxed_551_ = lean_unbox(v_x_550_);
v_res_552_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(v_x_boxed_551_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_toCtorIdx(uint8_t v_x_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(v_x_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_toCtorIdx___boxed(lean_object* v_x_555_){
_start:
{
uint8_t v_x_4__boxed_556_; lean_object* v_res_557_; 
v_x_4__boxed_556_ = lean_unbox(v_x_555_);
v_res_557_ = l_Lean_Meta_LibrarySearch_DeclMod_toCtorIdx(v_x_4__boxed_556_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___redArg(lean_object* v_k_558_){
_start:
{
lean_inc(v_k_558_);
return v_k_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___redArg___boxed(lean_object* v_k_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___redArg(v_k_559_);
lean_dec(v_k_559_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim(lean_object* v_motive_561_, lean_object* v_ctorIdx_562_, uint8_t v_t_563_, lean_object* v_h_564_, lean_object* v_k_565_){
_start:
{
lean_inc(v_k_565_);
return v_k_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___boxed(lean_object* v_motive_566_, lean_object* v_ctorIdx_567_, lean_object* v_t_568_, lean_object* v_h_569_, lean_object* v_k_570_){
_start:
{
uint8_t v_t_boxed_571_; lean_object* v_res_572_; 
v_t_boxed_571_ = lean_unbox(v_t_568_);
v_res_572_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorElim(v_motive_566_, v_ctorIdx_567_, v_t_boxed_571_, v_h_569_, v_k_570_);
lean_dec(v_k_570_);
lean_dec(v_ctorIdx_567_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim___redArg(lean_object* v_none_573_){
_start:
{
lean_inc(v_none_573_);
return v_none_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim___redArg___boxed(lean_object* v_none_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_Meta_LibrarySearch_DeclMod_none_elim___redArg(v_none_574_);
lean_dec(v_none_574_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim(lean_object* v_motive_576_, uint8_t v_t_577_, lean_object* v_h_578_, lean_object* v_none_579_){
_start:
{
lean_inc(v_none_579_);
return v_none_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim___boxed(lean_object* v_motive_580_, lean_object* v_t_581_, lean_object* v_h_582_, lean_object* v_none_583_){
_start:
{
uint8_t v_t_boxed_584_; lean_object* v_res_585_; 
v_t_boxed_584_ = lean_unbox(v_t_581_);
v_res_585_ = l_Lean_Meta_LibrarySearch_DeclMod_none_elim(v_motive_580_, v_t_boxed_584_, v_h_582_, v_none_583_);
lean_dec(v_none_583_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___redArg(lean_object* v_mp_586_){
_start:
{
lean_inc(v_mp_586_);
return v_mp_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___redArg___boxed(lean_object* v_mp_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___redArg(v_mp_587_);
lean_dec(v_mp_587_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim(lean_object* v_motive_589_, uint8_t v_t_590_, lean_object* v_h_591_, lean_object* v_mp_592_){
_start:
{
lean_inc(v_mp_592_);
return v_mp_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___boxed(lean_object* v_motive_593_, lean_object* v_t_594_, lean_object* v_h_595_, lean_object* v_mp_596_){
_start:
{
uint8_t v_t_boxed_597_; lean_object* v_res_598_; 
v_t_boxed_597_ = lean_unbox(v_t_594_);
v_res_598_ = l_Lean_Meta_LibrarySearch_DeclMod_mp_elim(v_motive_593_, v_t_boxed_597_, v_h_595_, v_mp_596_);
lean_dec(v_mp_596_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___redArg(lean_object* v_mpr_599_){
_start:
{
lean_inc(v_mpr_599_);
return v_mpr_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___redArg___boxed(lean_object* v_mpr_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___redArg(v_mpr_600_);
lean_dec(v_mpr_600_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim(lean_object* v_motive_602_, uint8_t v_t_603_, lean_object* v_h_604_, lean_object* v_mpr_605_){
_start:
{
lean_inc(v_mpr_605_);
return v_mpr_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___boxed(lean_object* v_motive_606_, lean_object* v_t_607_, lean_object* v_h_608_, lean_object* v_mpr_609_){
_start:
{
uint8_t v_t_boxed_610_; lean_object* v_res_611_; 
v_t_boxed_610_ = lean_unbox(v_t_607_);
v_res_611_ = l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim(v_motive_606_, v_t_boxed_610_, v_h_608_, v_mpr_609_);
lean_dec(v_mpr_609_);
return v_res_611_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_DeclMod_ofNat(lean_object* v_n_612_){
_start:
{
lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_613_ = lean_unsigned_to_nat(0u);
v___x_614_ = lean_nat_dec_le(v_n_612_, v___x_613_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_615_ = lean_unsigned_to_nat(1u);
v___x_616_ = lean_nat_dec_le(v_n_612_, v___x_615_);
if (v___x_616_ == 0)
{
uint8_t v___x_617_; 
v___x_617_ = 2;
return v___x_617_;
}
else
{
uint8_t v___x_618_; 
v___x_618_ = 1;
return v___x_618_;
}
}
else
{
uint8_t v___x_619_; 
v___x_619_ = 0;
return v___x_619_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ofNat___boxed(lean_object* v_n_620_){
_start:
{
uint8_t v_res_621_; lean_object* v_r_622_; 
v_res_621_ = l_Lean_Meta_LibrarySearch_DeclMod_ofNat(v_n_620_);
lean_dec(v_n_620_);
v_r_622_ = lean_box(v_res_621_);
return v_r_622_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_instDecidableEqDeclMod(uint8_t v_x_623_, uint8_t v_y_624_){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_625_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(v_x_623_);
v___x_626_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(v_y_624_);
v___x_627_ = lean_nat_dec_eq(v___x_625_, v___x_626_);
lean_dec(v___x_626_);
lean_dec(v___x_625_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_instDecidableEqDeclMod___boxed(lean_object* v_x_628_, lean_object* v_y_629_){
_start:
{
uint8_t v_x_13__boxed_630_; uint8_t v_y_14__boxed_631_; uint8_t v_res_632_; lean_object* v_r_633_; 
v_x_13__boxed_630_ = lean_unbox(v_x_628_);
v_y_14__boxed_631_ = lean_unbox(v_y_629_);
v_res_632_ = l_Lean_Meta_LibrarySearch_instDecidableEqDeclMod(v_x_13__boxed_630_, v_y_14__boxed_631_);
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
lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_638_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(v_x_636_);
v___x_639_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(v_y_637_);
v___x_640_ = lean_nat_dec_lt(v___x_638_, v___x_639_);
if (v___x_640_ == 0)
{
uint8_t v___x_641_; 
v___x_641_ = lean_nat_dec_eq(v___x_638_, v___x_639_);
lean_dec(v___x_639_);
lean_dec(v___x_638_);
if (v___x_641_ == 0)
{
uint8_t v___x_642_; 
v___x_642_ = 2;
return v___x_642_;
}
else
{
uint8_t v___x_643_; 
v___x_643_ = 1;
return v___x_643_;
}
}
else
{
uint8_t v___x_644_; 
lean_dec(v___x_639_);
lean_dec(v___x_638_);
v___x_644_ = 0;
return v___x_644_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_instOrdDeclMod_ord___boxed(lean_object* v_x_645_, lean_object* v_y_646_){
_start:
{
uint8_t v_x_30__boxed_647_; uint8_t v_y_31__boxed_648_; uint8_t v_res_649_; lean_object* v_r_650_; 
v_x_30__boxed_647_ = lean_unbox(v_x_645_);
v_y_31__boxed_648_ = lean_unbox(v_y_646_);
v_res_649_ = l_Lean_Meta_LibrarySearch_instOrdDeclMod_ord(v_x_30__boxed_647_, v_y_31__boxed_648_);
v_r_650_ = lean_box(v_res_649_);
return v_r_650_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_LibrarySearch_instHashableDeclMod_hash(uint8_t v_x_653_){
_start:
{
switch(v_x_653_)
{
case 0:
{
uint64_t v___x_654_; 
v___x_654_ = 0ULL;
return v___x_654_;
}
case 1:
{
uint64_t v___x_655_; 
v___x_655_ = 1ULL;
return v___x_655_;
}
default: 
{
uint64_t v___x_656_; 
v___x_656_ = 2ULL;
return v___x_656_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_instHashableDeclMod_hash___boxed(lean_object* v_x_657_){
_start:
{
uint8_t v_x_40__boxed_658_; uint64_t v_res_659_; lean_object* v_r_660_; 
v_x_40__boxed_658_ = lean_unbox(v_x_657_);
v_res_659_ = l_Lean_Meta_LibrarySearch_instHashableDeclMod_hash(v_x_40__boxed_658_);
v_r_660_ = lean_box_uint64(v_res_659_);
return v_r_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0(lean_object* v_k_663_, lean_object* v_b_664_, lean_object* v_c_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v___x_671_; 
lean_inc(v___y_669_);
lean_inc_ref(v___y_668_);
lean_inc(v___y_667_);
lean_inc_ref(v___y_666_);
v___x_671_ = lean_apply_7(v_k_663_, v_b_664_, v_c_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, lean_box(0));
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0___boxed(lean_object* v_k_672_, lean_object* v_b_673_, lean_object* v_c_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0(v_k_672_, v_b_673_, v_c_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(lean_object* v_type_681_, lean_object* v_k_682_, uint8_t v_cleanupAnnotations_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v___f_689_; uint8_t v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___f_689_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_689_, 0, v_k_682_);
v___x_690_ = 0;
v___x_691_ = lean_box(0);
v___x_692_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_690_, v___x_691_, v_type_681_, v___f_689_, v_cleanupAnnotations_683_, v___x_690_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
v_a_701_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_692_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_692_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___boxed(lean_object* v_type_709_, lean_object* v_k_710_, lean_object* v_cleanupAnnotations_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_717_; lean_object* v_res_718_; 
v_cleanupAnnotations_boxed_717_ = lean_unbox(v_cleanupAnnotations_711_);
v_res_718_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(v_type_709_, v_k_710_, v_cleanupAnnotations_boxed_717_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0(lean_object* v_00_u03b1_719_, lean_object* v_type_720_, lean_object* v_k_721_, uint8_t v_cleanupAnnotations_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(v_type_720_, v_k_721_, v_cleanupAnnotations_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___boxed(lean_object* v_00_u03b1_729_, lean_object* v_type_730_, lean_object* v_k_731_, lean_object* v_cleanupAnnotations_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_738_; lean_object* v_res_739_; 
v_cleanupAnnotations_boxed_738_ = lean_unbox(v_cleanupAnnotations_732_);
v_res_739_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0(v_00_u03b1_729_, v_type_730_, v_k_731_, v_cleanupAnnotations_boxed_738_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0(lean_object* v_name_746_, lean_object* v_x_747_, lean_object* v_type_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
uint8_t v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_754_ = 0;
v___x_755_ = lean_box(v___x_754_);
lean_inc(v_name_746_);
v___x_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_756_, 0, v_name_746_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_type_748_, v___x_756_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_807_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_807_ == 0)
{
v___x_760_ = v___x_757_;
v_isShared_761_ = v_isSharedCheck_807_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_757_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_807_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v_key_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v_key_762_ = lean_ctor_get(v_a_758_, 0);
v___x_763_ = lean_unsigned_to_nat(1u);
v___x_764_ = lean_mk_empty_array_with_capacity(v___x_763_);
lean_inc(v_a_758_);
v___x_765_ = lean_array_push(v___x_764_, v_a_758_);
v___x_766_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__2));
v___x_767_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_762_, v___x_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_769_; 
lean_dec(v_a_758_);
lean_dec(v_name_746_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 0, v___x_765_);
v___x_769_ = v___x_760_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_765_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
else
{
lean_object* v___x_771_; uint8_t v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
lean_del_object(v___x_760_);
v___x_771_ = lean_unsigned_to_nat(0u);
v___x_772_ = 1;
v___x_773_ = lean_box(v___x_772_);
lean_inc(v_name_746_);
v___x_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_774_, 0, v_name_746_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
lean_inc(v_a_758_);
v___x_775_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_a_758_, v___x_771_, v___x_774_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; uint8_t v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_a_776_);
lean_dec_ref_known(v___x_775_, 1);
v___x_777_ = 2;
v___x_778_ = lean_box(v___x_777_);
v___x_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_779_, 0, v_name_746_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
v___x_780_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_a_758_, v___x_763_, v___x_779_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_790_; 
v_a_781_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_790_ == 0)
{
v___x_783_ = v___x_780_;
v_isShared_784_ = v_isSharedCheck_790_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_780_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_790_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_788_; 
v___x_785_ = lean_array_push(v___x_765_, v_a_776_);
v___x_786_ = lean_array_push(v___x_785_, v_a_781_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v___x_786_);
v___x_788_ = v___x_783_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_dec(v_a_776_);
lean_dec_ref(v___x_765_);
v_a_791_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_780_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_780_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec_ref(v___x_765_);
lean_dec(v_a_758_);
lean_dec(v_name_746_);
v_a_799_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_775_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_775_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_dec(v_name_746_);
v_a_808_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_757_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_757_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___boxed(lean_object* v_name_816_, lean_object* v_x_817_, lean_object* v_type_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0(v_name_816_, v_x_817_, v_type_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec_ref(v_x_817_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport(lean_object* v_name_827_, lean_object* v_c_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_){
_start:
{
lean_object* v___x_834_; lean_object* v_env_835_; uint8_t v___x_836_; 
v___x_834_ = lean_st_ref_get(v_a_832_);
v_env_835_ = lean_ctor_get(v___x_834_, 0);
lean_inc_ref(v_env_835_);
lean_dec(v___x_834_);
lean_inc(v_name_827_);
v___x_836_ = l_Lean_Linter_isDeprecated(v_env_835_, v_name_827_);
if (v___x_836_ == 0)
{
uint8_t v___x_837_; 
lean_inc(v_name_827_);
v___x_837_ = l_Lean_Name_isMetaprogramming(v_name_827_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; lean_object* v_type_839_; lean_object* v___f_840_; lean_object* v___x_841_; 
v___x_838_ = l_Lean_AsyncConstantInfo_toConstantVal(v_c_828_);
v_type_839_ = lean_ctor_get(v___x_838_, 2);
lean_inc_ref(v_type_839_);
lean_dec_ref(v___x_838_);
v___f_840_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___boxed), 8, 1);
lean_closure_set(v___f_840_, 0, v_name_827_);
v___x_841_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(v_type_839_, v___f_840_, v___x_837_, v_a_829_, v_a_830_, v_a_831_, v_a_832_);
return v___x_841_;
}
else
{
lean_object* v___x_842_; lean_object* v___x_843_; 
lean_dec_ref(v_c_828_);
lean_dec(v_name_827_);
v___x_842_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___closed__0));
v___x_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_843_, 0, v___x_842_);
return v___x_843_;
}
}
else
{
lean_object* v___x_844_; lean_object* v___x_845_; 
lean_dec_ref(v_c_828_);
lean_dec(v_name_827_);
v___x_844_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___closed__0));
v___x_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
return v___x_845_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___boxed(lean_object* v_name_846_, lean_object* v_c_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport(v_name_846_, v_c_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_858108106____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_855_ = lean_box(0);
v___x_856_ = lean_st_mk_ref(v___x_855_);
v___x_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_858108106____hygCtx___hyg_2____boxed(lean_object* v_a_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_858108106____hygCtx___hyg_2_();
return v_res_859_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_constantsPerImportTask(void){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = lean_unsigned_to_nat(6500u);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2955776588____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_887_ = lean_box(0);
v___x_888_ = lean_st_mk_ref(v___x_887_);
v___x_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2955776588____hygCtx___hyg_2____boxed(lean_object* v_a_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2955776588____hygCtx___hyg_2_();
return v_res_891_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__1(void){
_start:
{
lean_object* v_droppedRef_893_; lean_object* v___x_894_; 
v_droppedRef_893_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_starLemmasExt;
v___x_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_894_, 0, v_droppedRef_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_libSearchFindDecls(lean_object* v_ty_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_901_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_ext;
v___x_902_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__0));
v___x_903_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_droppedKeys));
v___x_904_ = lean_unsigned_to_nat(6500u);
v___x_905_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__1, &l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__1_once, _init_l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__1);
v___x_906_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v___x_901_, v___x_902_, v___x_903_, v___x_904_, v___x_905_, v_ty_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_libSearchFindDecls___boxed(lean_object* v_ty_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_Meta_LibrarySearch_libSearchFindDecls(v_ty_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
return v_res_913_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2(void){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_917_ = lean_box(0);
v___x_918_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_getStarLemmas___closed__1));
v___x_919_ = l_Lean_mkConst(v___x_918_, v___x_917_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_getStarLemmas(lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
lean_object* v_ref_927_; lean_object* v___x_928_; 
v_ref_927_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_starLemmasExt;
v___x_928_ = lean_st_ref_get(v_ref_927_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2, &l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2_once, _init_l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2);
v___x_930_ = l_Lean_Meta_LibrarySearch_libSearchFindDecls(v___x_929_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_943_; 
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_943_ == 0)
{
lean_object* v_unused_944_; 
v_unused_944_ = lean_ctor_get(v___x_930_, 0);
lean_dec(v_unused_944_);
v___x_932_ = v___x_930_;
v_isShared_933_ = v_isSharedCheck_943_;
goto v_resetjp_931_;
}
else
{
lean_dec(v___x_930_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_943_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_934_; 
v___x_934_ = lean_st_ref_get(v_ref_927_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v___x_935_; lean_object* v___x_937_; 
v___x_935_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_getStarLemmas___closed__3));
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_935_);
v___x_937_ = v___x_932_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_935_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
else
{
lean_object* v_val_939_; lean_object* v___x_941_; 
v_val_939_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_val_939_);
lean_dec_ref_known(v___x_934_, 1);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v_val_939_);
v___x_941_ = v___x_932_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_val_939_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
else
{
return v___x_930_;
}
}
else
{
lean_object* v_val_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
v_val_945_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_928_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_val_945_);
lean_dec(v___x_928_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
lean_ctor_set_tag(v___x_947_, 0);
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_val_945_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_getStarLemmas___boxed(lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v_a_953_, v_a_954_, v_a_955_, v_a_956_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0(uint8_t v___x_959_, lean_object* v___x_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
if (v___x_959_ == 0)
{
lean_object* v___x_966_; 
v___x_966_ = l_Lean_getRemainingHeartbeats___redArg(v___y_963_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_976_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_976_ == 0)
{
v___x_969_ = v___x_966_;
v_isShared_970_ = v_isSharedCheck_976_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_966_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_976_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
uint8_t v___x_971_; lean_object* v___x_972_; lean_object* v___x_974_; 
v___x_971_ = lean_nat_dec_lt(v_a_967_, v___x_960_);
lean_dec(v_a_967_);
v___x_972_ = lean_box(v___x_971_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 0, v___x_972_);
v___x_974_ = v___x_969_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_972_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
else
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
v_a_977_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_984_ == 0)
{
v___x_979_ = v___x_966_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_966_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_a_977_);
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
else
{
uint8_t v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_985_ = 0;
v___x_986_ = lean_box(v___x_985_);
v___x_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
return v___x_987_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0___boxed(lean_object* v___x_988_, lean_object* v___x_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
uint8_t v___x_643__boxed_995_; lean_object* v_res_996_; 
v___x_643__boxed_995_ = lean_unbox(v___x_988_);
v_res_996_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0(v___x_643__boxed_995_, v___x_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___x_989_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(lean_object* v_leavePercent_997_, lean_object* v_a_998_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Lean_getMaxHeartbeats___redArg(v_a_998_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1002_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 1);
v___x_1002_ = l_Lean_getRemainingHeartbeats___redArg(v_a_998_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1017_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1017_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1017_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; lean_object* v___x_1012_; lean_object* v___y_1013_; lean_object* v___x_1015_; 
v___x_1007_ = lean_nat_mul(v_a_1003_, v_leavePercent_997_);
lean_dec(v_a_1003_);
v___x_1008_ = lean_unsigned_to_nat(100u);
v___x_1009_ = lean_nat_div(v___x_1007_, v___x_1008_);
lean_dec(v___x_1007_);
v___x_1010_ = lean_unsigned_to_nat(0u);
v___x_1011_ = lean_nat_dec_eq(v_a_1001_, v___x_1010_);
lean_dec(v_a_1001_);
v___x_1012_ = lean_box(v___x_1011_);
v___y_1013_ = lean_alloc_closure((void*)(l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___y_1013_, 0, v___x_1012_);
lean_closure_set(v___y_1013_, 1, v___x_1009_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v___y_1013_);
v___x_1015_ = v___x_1005_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___y_1013_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
lean_dec(v_a_1001_);
v_a_1018_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_1002_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1002_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
v_a_1026_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_1000_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1000_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___boxed(lean_object* v_leavePercent_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercent_1034_, v_a_1035_);
lean_dec_ref(v_a_1035_);
lean_dec(v_leavePercent_1034_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck(lean_object* v_leavePercent_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercent_1038_, v_a_1041_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___boxed(lean_object* v_leavePercent_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck(v_leavePercent_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
lean_dec(v_leavePercent_1045_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(lean_object* v_upperBound_1052_, lean_object* v_x_1053_, lean_object* v_f_1054_, lean_object* v_y_1055_, lean_object* v_g_1056_, lean_object* v_a_1057_, lean_object* v_b_1058_){
_start:
{
uint8_t v___x_1059_; 
v___x_1059_ = lean_nat_dec_lt(v_a_1057_, v_upperBound_1052_);
if (v___x_1059_ == 0)
{
lean_dec(v_a_1057_);
lean_dec(v_g_1056_);
lean_dec(v_f_1054_);
return v_b_1058_;
}
else
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1060_ = lean_array_fget_borrowed(v_x_1053_, v_a_1057_);
lean_inc(v_f_1054_);
lean_inc(v___x_1060_);
v___x_1061_ = lean_apply_1(v_f_1054_, v___x_1060_);
v___x_1062_ = lean_array_push(v_b_1058_, v___x_1061_);
v___x_1063_ = lean_array_fget_borrowed(v_y_1055_, v_a_1057_);
lean_inc(v_g_1056_);
lean_inc(v___x_1063_);
v___x_1064_ = lean_apply_1(v_g_1056_, v___x_1063_);
v___x_1065_ = lean_array_push(v___x_1062_, v___x_1064_);
v___x_1066_ = lean_unsigned_to_nat(1u);
v___x_1067_ = lean_nat_add(v_a_1057_, v___x_1066_);
lean_dec(v_a_1057_);
v_a_1057_ = v___x_1067_;
v_b_1058_ = v___x_1065_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg___boxed(lean_object* v_upperBound_1069_, lean_object* v_x_1070_, lean_object* v_f_1071_, lean_object* v_y_1072_, lean_object* v_g_1073_, lean_object* v_a_1074_, lean_object* v_b_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(v_upperBound_1069_, v_x_1070_, v_f_1071_, v_y_1072_, v_g_1073_, v_a_1074_, v_b_1075_);
lean_dec_ref(v_y_1072_);
lean_dec_ref(v_x_1070_);
lean_dec(v_upperBound_1069_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(lean_object* v_g_1077_, size_t v_sz_1078_, size_t v_i_1079_, lean_object* v_bs_1080_){
_start:
{
uint8_t v___x_1081_; 
v___x_1081_ = lean_usize_dec_lt(v_i_1079_, v_sz_1078_);
if (v___x_1081_ == 0)
{
lean_dec(v_g_1077_);
return v_bs_1080_;
}
else
{
lean_object* v_v_1082_; lean_object* v___x_1083_; lean_object* v_bs_x27_1084_; lean_object* v___x_1085_; size_t v___x_1086_; size_t v___x_1087_; lean_object* v___x_1088_; 
v_v_1082_ = lean_array_uget(v_bs_1080_, v_i_1079_);
v___x_1083_ = lean_unsigned_to_nat(0u);
v_bs_x27_1084_ = lean_array_uset(v_bs_1080_, v_i_1079_, v___x_1083_);
lean_inc(v_g_1077_);
v___x_1085_ = lean_apply_1(v_g_1077_, v_v_1082_);
v___x_1086_ = ((size_t)1ULL);
v___x_1087_ = lean_usize_add(v_i_1079_, v___x_1086_);
v___x_1088_ = lean_array_uset(v_bs_x27_1084_, v_i_1079_, v___x_1085_);
v_i_1079_ = v___x_1087_;
v_bs_1080_ = v___x_1088_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg___boxed(lean_object* v_g_1090_, lean_object* v_sz_1091_, lean_object* v_i_1092_, lean_object* v_bs_1093_){
_start:
{
size_t v_sz_boxed_1094_; size_t v_i_boxed_1095_; lean_object* v_res_1096_; 
v_sz_boxed_1094_ = lean_unbox_usize(v_sz_1091_);
lean_dec(v_sz_1091_);
v_i_boxed_1095_ = lean_unbox_usize(v_i_1092_);
lean_dec(v_i_1092_);
v_res_1096_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_g_1090_, v_sz_boxed_1094_, v_i_boxed_1095_, v_bs_1093_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith___redArg(lean_object* v_f_1097_, lean_object* v_x_1098_, lean_object* v_g_1099_, lean_object* v_y_1100_){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v_res_1104_; lean_object* v___y_1106_; uint8_t v___x_1120_; 
v___x_1101_ = lean_array_get_size(v_x_1098_);
v___x_1102_ = lean_array_get_size(v_y_1100_);
v___x_1103_ = lean_nat_add(v___x_1101_, v___x_1102_);
v_res_1104_ = lean_mk_empty_array_with_capacity(v___x_1103_);
lean_dec(v___x_1103_);
v___x_1120_ = lean_nat_dec_le(v___x_1101_, v___x_1102_);
if (v___x_1120_ == 0)
{
v___y_1106_ = v___x_1102_;
goto v___jp_1105_;
}
else
{
v___y_1106_ = v___x_1101_;
goto v___jp_1105_;
}
v___jp_1105_:
{
uint8_t v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1107_ = lean_nat_dec_lt(v___y_1106_, v___x_1101_);
v___x_1108_ = lean_unsigned_to_nat(0u);
lean_inc(v_g_1099_);
lean_inc(v_f_1097_);
v___x_1109_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(v___y_1106_, v_x_1098_, v_f_1097_, v_y_1100_, v_g_1099_, v___x_1108_, v_res_1104_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1110_; size_t v_sz_1111_; size_t v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
lean_dec(v_f_1097_);
v___x_1110_ = l_Array_extract___redArg(v_y_1100_, v___y_1106_, v___x_1102_);
v_sz_1111_ = lean_array_size(v___x_1110_);
v___x_1112_ = ((size_t)0ULL);
v___x_1113_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_g_1099_, v_sz_1111_, v___x_1112_, v___x_1110_);
v___x_1114_ = l_Array_append___redArg(v___x_1109_, v___x_1113_);
lean_dec_ref(v___x_1113_);
return v___x_1114_;
}
else
{
lean_object* v___x_1115_; size_t v_sz_1116_; size_t v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
lean_dec(v_g_1099_);
v___x_1115_ = l_Array_extract___redArg(v_x_1098_, v___y_1106_, v___x_1101_);
v_sz_1116_ = lean_array_size(v___x_1115_);
v___x_1117_ = ((size_t)0ULL);
v___x_1118_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_f_1097_, v_sz_1116_, v___x_1117_, v___x_1115_);
v___x_1119_ = l_Array_append___redArg(v___x_1109_, v___x_1118_);
lean_dec_ref(v___x_1118_);
return v___x_1119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith___redArg___boxed(lean_object* v_f_1121_, lean_object* v_x_1122_, lean_object* v_g_1123_, lean_object* v_y_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lean_Meta_LibrarySearch_interleaveWith___redArg(v_f_1121_, v_x_1122_, v_g_1123_, v_y_1124_);
lean_dec_ref(v_y_1124_);
lean_dec_ref(v_x_1122_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith(lean_object* v_00_u03b1_1126_, lean_object* v_00_u03b2_1127_, lean_object* v_00_u03b3_1128_, lean_object* v_f_1129_, lean_object* v_x_1130_, lean_object* v_g_1131_, lean_object* v_y_1132_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_Meta_LibrarySearch_interleaveWith___redArg(v_f_1129_, v_x_1130_, v_g_1131_, v_y_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith___boxed(lean_object* v_00_u03b1_1134_, lean_object* v_00_u03b2_1135_, lean_object* v_00_u03b3_1136_, lean_object* v_f_1137_, lean_object* v_x_1138_, lean_object* v_g_1139_, lean_object* v_y_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_Meta_LibrarySearch_interleaveWith(v_00_u03b1_1134_, v_00_u03b2_1135_, v_00_u03b3_1136_, v_f_1137_, v_x_1138_, v_g_1139_, v_y_1140_);
lean_dec_ref(v_y_1140_);
lean_dec_ref(v_x_1138_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0(lean_object* v_00_u03b2_1142_, lean_object* v_00_u03b3_1143_, lean_object* v_g_1144_, size_t v_sz_1145_, size_t v_i_1146_, lean_object* v_bs_1147_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_g_1144_, v_sz_1145_, v_i_1146_, v_bs_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___boxed(lean_object* v_00_u03b2_1149_, lean_object* v_00_u03b3_1150_, lean_object* v_g_1151_, lean_object* v_sz_1152_, lean_object* v_i_1153_, lean_object* v_bs_1154_){
_start:
{
size_t v_sz_boxed_1155_; size_t v_i_boxed_1156_; lean_object* v_res_1157_; 
v_sz_boxed_1155_ = lean_unbox_usize(v_sz_1152_);
lean_dec(v_sz_1152_);
v_i_boxed_1156_ = lean_unbox_usize(v_i_1153_);
lean_dec(v_i_1153_);
v_res_1157_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0(v_00_u03b2_1149_, v_00_u03b3_1150_, v_g_1151_, v_sz_boxed_1155_, v_i_boxed_1156_, v_bs_1154_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1(lean_object* v_00_u03b3_1158_, lean_object* v_upperBound_1159_, lean_object* v_00_u03b1_1160_, lean_object* v_x_1161_, lean_object* v_f_1162_, lean_object* v_00_u03b2_1163_, lean_object* v_y_1164_, lean_object* v_g_1165_, lean_object* v_inst_1166_, lean_object* v_R_1167_, lean_object* v_a_1168_, lean_object* v_b_1169_, lean_object* v_c_1170_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(v_upperBound_1159_, v_x_1161_, v_f_1162_, v_y_1164_, v_g_1165_, v_a_1168_, v_b_1169_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___boxed(lean_object* v_00_u03b3_1172_, lean_object* v_upperBound_1173_, lean_object* v_00_u03b1_1174_, lean_object* v_x_1175_, lean_object* v_f_1176_, lean_object* v_00_u03b2_1177_, lean_object* v_y_1178_, lean_object* v_g_1179_, lean_object* v_inst_1180_, lean_object* v_R_1181_, lean_object* v_a_1182_, lean_object* v_b_1183_, lean_object* v_c_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1(v_00_u03b3_1172_, v_upperBound_1173_, v_00_u03b1_1174_, v_x_1175_, v_f_1176_, v_00_u03b2_1177_, v_y_1178_, v_g_1179_, v_inst_1180_, v_R_1181_, v_a_1182_, v_b_1183_, v_c_1184_);
lean_dec_ref(v_y_1178_);
lean_dec_ref(v_x_1175_);
lean_dec(v_upperBound_1173_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_));
v___x_1194_ = l_Lean_registerInternalExceptionId(v___x_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2____boxed(lean_object* v_a_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_();
return v_res_1196_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0(void){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1197_ = lean_box(0);
v___x_1198_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_abortSpeculationId;
v___x_1199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
lean_ctor_set(v___x_1199_, 1, v___x_1197_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___redArg(lean_object* v_inst_1200_){
_start:
{
lean_object* v_throw_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v_throw_1201_ = lean_ctor_get(v_inst_1200_, 0);
lean_inc(v_throw_1201_);
lean_dec_ref(v_inst_1200_);
v___x_1202_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0, &l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0_once, _init_l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0);
v___x_1203_ = lean_apply_2(v_throw_1201_, lean_box(0), v___x_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation(lean_object* v_m_1204_, lean_object* v_00_u03b1_1205_, lean_object* v_inst_1206_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Lean_Meta_LibrarySearch_abortSpeculation___redArg(v_inst_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_isAbortSpeculation(lean_object* v_x_1208_){
_start:
{
if (lean_obj_tag(v_x_1208_) == 1)
{
lean_object* v_id_1209_; lean_object* v___x_1210_; uint8_t v___x_1211_; 
v_id_1209_ = lean_ctor_get(v_x_1208_, 0);
v___x_1210_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_abortSpeculationId;
v___x_1211_ = l_Lean_instBEqInternalExceptionId_beq(v_id_1209_, v___x_1210_);
return v___x_1211_;
}
else
{
uint8_t v___x_1212_; 
v___x_1212_ = 0;
return v___x_1212_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_isAbortSpeculation___boxed(lean_object* v_x_1213_){
_start:
{
uint8_t v_res_1214_; lean_object* v_r_1215_; 
v_res_1214_ = l_Lean_Meta_LibrarySearch_isAbortSpeculation(v_x_1213_);
lean_dec_ref(v_x_1213_);
v_r_1215_ = lean_box(v_res_1214_);
return v_r_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(lean_object* v_x_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Lean_Meta_saveState___redArg(v___y_1218_, v___y_1220_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; lean_object* v___x_1224_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_a_1223_);
lean_dec_ref_known(v___x_1222_, 1);
lean_inc(v___y_1220_);
lean_inc_ref(v___y_1219_);
lean_inc(v___y_1218_);
lean_inc_ref(v___y_1217_);
v___x_1224_ = lean_apply_5(v_x_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, lean_box(0));
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1233_; 
lean_dec(v_a_1223_);
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1227_ = v___x_1224_;
v_isShared_1228_ = v_isSharedCheck_1233_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1224_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1233_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1229_; lean_object* v___x_1231_; 
v___x_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1229_, 0, v_a_1225_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 0, v___x_1229_);
v___x_1231_ = v___x_1227_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1229_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
else
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1263_; 
v_a_1234_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1236_ = v___x_1224_;
v_isShared_1237_ = v_isSharedCheck_1263_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1224_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1263_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
uint8_t v___y_1239_; uint8_t v___x_1261_; 
v___x_1261_ = l_Lean_Exception_isInterrupt(v_a_1234_);
if (v___x_1261_ == 0)
{
uint8_t v___x_1262_; 
lean_inc(v_a_1234_);
v___x_1262_ = l_Lean_Exception_isRuntime(v_a_1234_);
v___y_1239_ = v___x_1262_;
goto v___jp_1238_;
}
else
{
v___y_1239_ = v___x_1261_;
goto v___jp_1238_;
}
v___jp_1238_:
{
if (v___y_1239_ == 0)
{
lean_object* v___x_1240_; 
lean_del_object(v___x_1236_);
lean_dec(v_a_1234_);
v___x_1240_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1223_, v___y_1218_, v___y_1220_);
lean_dec(v_a_1223_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1248_; 
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1248_ == 0)
{
lean_object* v_unused_1249_; 
v_unused_1249_ = lean_ctor_get(v___x_1240_, 0);
lean_dec(v_unused_1249_);
v___x_1242_ = v___x_1240_;
v_isShared_1243_ = v_isSharedCheck_1248_;
goto v_resetjp_1241_;
}
else
{
lean_dec(v___x_1240_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1248_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1244_; lean_object* v___x_1246_; 
v___x_1244_ = lean_box(0);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 0, v___x_1244_);
v___x_1246_ = v___x_1242_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1244_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
v_a_1250_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1240_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1240_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
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
else
{
lean_object* v___x_1259_; 
lean_dec(v_a_1223_);
if (v_isShared_1237_ == 0)
{
v___x_1259_ = v___x_1236_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1234_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
}
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec_ref(v_x_1216_);
v_a_1264_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1222_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1222_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg___boxed(lean_object* v_x_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(v_x_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0(lean_object* v_00_u03b1_1279_, lean_object* v_x_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(v_x_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___boxed(lean_object* v_00_u03b1_1287_, lean_object* v_x_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0(v_00_u03b1_1287_, v_x_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(lean_object* v_e_1295_, lean_object* v___y_1296_){
_start:
{
uint8_t v___x_1298_; 
v___x_1298_ = l_Lean_Expr_hasMVar(v_e_1295_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; 
v___x_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1299_, 0, v_e_1295_);
return v___x_1299_;
}
else
{
lean_object* v___x_1300_; lean_object* v_mctx_1301_; lean_object* v___x_1302_; lean_object* v_fst_1303_; lean_object* v_snd_1304_; lean_object* v___x_1305_; lean_object* v_cache_1306_; lean_object* v_zetaDeltaFVarIds_1307_; lean_object* v_postponed_1308_; lean_object* v_diag_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1318_; 
v___x_1300_ = lean_st_ref_get(v___y_1296_);
v_mctx_1301_ = lean_ctor_get(v___x_1300_, 0);
lean_inc_ref(v_mctx_1301_);
lean_dec(v___x_1300_);
v___x_1302_ = l_Lean_instantiateMVarsCore(v_mctx_1301_, v_e_1295_);
v_fst_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_fst_1303_);
v_snd_1304_ = lean_ctor_get(v___x_1302_, 1);
lean_inc(v_snd_1304_);
lean_dec_ref(v___x_1302_);
v___x_1305_ = lean_st_ref_take(v___y_1296_);
v_cache_1306_ = lean_ctor_get(v___x_1305_, 1);
v_zetaDeltaFVarIds_1307_ = lean_ctor_get(v___x_1305_, 2);
v_postponed_1308_ = lean_ctor_get(v___x_1305_, 3);
v_diag_1309_ = lean_ctor_get(v___x_1305_, 4);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1318_ == 0)
{
lean_object* v_unused_1319_; 
v_unused_1319_ = lean_ctor_get(v___x_1305_, 0);
lean_dec(v_unused_1319_);
v___x_1311_ = v___x_1305_;
v_isShared_1312_ = v_isSharedCheck_1318_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_diag_1309_);
lean_inc(v_postponed_1308_);
lean_inc(v_zetaDeltaFVarIds_1307_);
lean_inc(v_cache_1306_);
lean_dec(v___x_1305_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1318_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 0, v_snd_1304_);
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_snd_1304_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v_cache_1306_);
lean_ctor_set(v_reuseFailAlloc_1317_, 2, v_zetaDeltaFVarIds_1307_);
lean_ctor_set(v_reuseFailAlloc_1317_, 3, v_postponed_1308_);
lean_ctor_set(v_reuseFailAlloc_1317_, 4, v_diag_1309_);
v___x_1314_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = lean_st_ref_set(v___y_1296_, v___x_1314_);
v___x_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1316_, 0, v_fst_1303_);
return v___x_1316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg___boxed(lean_object* v_e_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(v_e_1320_, v___y_1321_);
lean_dec(v___y_1321_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1(lean_object* v_e_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(v_e_1324_, v___y_1326_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___boxed(lean_object* v_e_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1(v_e_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0(lean_object* v___x_1338_, lean_object* v_x_1339_){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1338_);
lean_ctor_set(v___x_1340_, 1, v_x_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(lean_object* v___x_1341_, size_t v_sz_1342_, size_t v_i_1343_, lean_object* v_bs_1344_){
_start:
{
uint8_t v___x_1345_; 
v___x_1345_ = lean_usize_dec_lt(v_i_1343_, v_sz_1342_);
if (v___x_1345_ == 0)
{
lean_dec_ref(v___x_1341_);
return v_bs_1344_;
}
else
{
lean_object* v_v_1346_; lean_object* v___x_1347_; lean_object* v_bs_x27_1348_; lean_object* v___x_1349_; size_t v___x_1350_; size_t v___x_1351_; lean_object* v___x_1352_; 
v_v_1346_ = lean_array_uget(v_bs_1344_, v_i_1343_);
v___x_1347_ = lean_unsigned_to_nat(0u);
v_bs_x27_1348_ = lean_array_uset(v_bs_1344_, v_i_1343_, v___x_1347_);
lean_inc_ref(v___x_1341_);
v___x_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1341_);
lean_ctor_set(v___x_1349_, 1, v_v_1346_);
v___x_1350_ = ((size_t)1ULL);
v___x_1351_ = lean_usize_add(v_i_1343_, v___x_1350_);
v___x_1352_ = lean_array_uset(v_bs_x27_1348_, v_i_1343_, v___x_1349_);
v_i_1343_ = v___x_1351_;
v_bs_1344_ = v___x_1352_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2___boxed(lean_object* v___x_1354_, lean_object* v_sz_1355_, lean_object* v_i_1356_, lean_object* v_bs_1357_){
_start:
{
size_t v_sz_boxed_1358_; size_t v_i_boxed_1359_; lean_object* v_res_1360_; 
v_sz_boxed_1358_ = lean_unbox_usize(v_sz_1355_);
lean_dec(v_sz_1355_);
v_i_boxed_1359_ = lean_unbox_usize(v_i_1356_);
lean_dec(v_i_1356_);
v_res_1360_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(v___x_1354_, v_sz_boxed_1358_, v_i_boxed_1359_, v_bs_1357_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearchSymm(lean_object* v_searchFn_1361_, lean_object* v_goal_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_){
_start:
{
lean_object* v___x_1368_; 
lean_inc(v_goal_1362_);
v___x_1368_ = l_Lean_MVarId_getType(v_goal_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v___x_1370_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_a_1369_);
lean_dec_ref_known(v___x_1368_, 1);
lean_inc_ref(v_searchFn_1361_);
lean_inc(v_a_1366_);
lean_inc_ref(v_a_1365_);
lean_inc(v_a_1364_);
lean_inc_ref(v_a_1363_);
v___x_1370_ = lean_apply_6(v_searchFn_1361_, v_a_1369_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, lean_box(0));
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v_a_1371_; lean_object* v___x_1372_; lean_object* v_mctx_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v_a_1371_ = lean_ctor_get(v___x_1370_, 0);
lean_inc(v_a_1371_);
lean_dec_ref_known(v___x_1370_, 1);
v___x_1372_ = lean_st_ref_get(v_a_1364_);
v_mctx_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc_ref_n(v_mctx_1373_, 2);
lean_dec(v___x_1372_);
lean_inc(v_goal_1362_);
v___x_1374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1374_, 0, v_goal_1362_);
lean_ctor_set(v___x_1374_, 1, v_mctx_1373_);
v___x_1375_ = lean_alloc_closure((void*)(l_Lean_MVarId_applySymm___boxed), 6, 1);
lean_closure_set(v___x_1375_, 0, v_goal_1362_);
v___x_1376_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(v___x_1375_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1437_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1379_ = v___x_1376_;
v_isShared_1380_ = v_isSharedCheck_1437_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1376_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1437_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
if (lean_obj_tag(v_a_1377_) == 1)
{
lean_object* v_val_1381_; lean_object* v___x_1382_; 
lean_del_object(v___x_1379_);
v_val_1381_ = lean_ctor_get(v_a_1377_, 0);
lean_inc_n(v_val_1381_, 2);
lean_dec_ref_known(v_a_1377_, 1);
v___x_1382_ = l_Lean_MVarId_getType(v_val_1381_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1384_; lean_object* v_a_1385_; lean_object* v___x_1386_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_a_1383_);
lean_dec_ref_known(v___x_1382_, 1);
v___x_1384_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(v_a_1383_, v_a_1364_);
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref(v___x_1384_);
lean_inc(v_a_1366_);
lean_inc_ref(v_a_1365_);
lean_inc(v_a_1364_);
lean_inc_ref(v_a_1363_);
v___x_1386_ = lean_apply_6(v_searchFn_1361_, v_a_1385_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, lean_box(0));
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1414_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1389_ = v___x_1386_;
v_isShared_1390_ = v_isSharedCheck_1414_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1386_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1414_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v_cache_1393_; lean_object* v_zetaDeltaFVarIds_1394_; lean_object* v_postponed_1395_; lean_object* v_diag_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1412_; 
v___x_1391_ = lean_st_ref_get(v_a_1364_);
v___x_1392_ = lean_st_ref_take(v_a_1364_);
v_cache_1393_ = lean_ctor_get(v___x_1392_, 1);
v_zetaDeltaFVarIds_1394_ = lean_ctor_get(v___x_1392_, 2);
v_postponed_1395_ = lean_ctor_get(v___x_1392_, 3);
v_diag_1396_ = lean_ctor_get(v___x_1392_, 4);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1412_ == 0)
{
lean_object* v_unused_1413_; 
v_unused_1413_ = lean_ctor_get(v___x_1392_, 0);
lean_dec(v_unused_1413_);
v___x_1398_ = v___x_1392_;
v_isShared_1399_ = v_isSharedCheck_1412_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_diag_1396_);
lean_inc(v_postponed_1395_);
lean_inc(v_zetaDeltaFVarIds_1394_);
lean_inc(v_cache_1393_);
lean_dec(v___x_1392_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1412_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v_mctx_1373_);
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_mctx_1373_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v_cache_1393_);
lean_ctor_set(v_reuseFailAlloc_1411_, 2, v_zetaDeltaFVarIds_1394_);
lean_ctor_set(v_reuseFailAlloc_1411_, 3, v_postponed_1395_);
lean_ctor_set(v_reuseFailAlloc_1411_, 4, v_diag_1396_);
v___x_1401_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
lean_object* v___x_1402_; lean_object* v_mctx_1403_; lean_object* v___f_1404_; lean_object* v___x_1405_; lean_object* v___f_1406_; lean_object* v___x_1407_; lean_object* v___x_1409_; 
v___x_1402_ = lean_st_ref_set(v_a_1364_, v___x_1401_);
v_mctx_1403_ = lean_ctor_get(v___x_1391_, 0);
lean_inc_ref(v_mctx_1403_);
lean_dec(v___x_1391_);
v___f_1404_ = lean_alloc_closure((void*)(l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0), 2, 1);
lean_closure_set(v___f_1404_, 0, v___x_1374_);
v___x_1405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1405_, 0, v_val_1381_);
lean_ctor_set(v___x_1405_, 1, v_mctx_1403_);
v___f_1406_ = lean_alloc_closure((void*)(l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0), 2, 1);
lean_closure_set(v___f_1406_, 0, v___x_1405_);
v___x_1407_ = l_Lean_Meta_LibrarySearch_interleaveWith___redArg(v___f_1404_, v_a_1371_, v___f_1406_, v_a_1387_);
lean_dec(v_a_1387_);
lean_dec(v_a_1371_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1407_);
v___x_1409_ = v___x_1389_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
}
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
lean_dec(v_val_1381_);
lean_dec_ref_known(v___x_1374_, 2);
lean_dec_ref(v_mctx_1373_);
lean_dec(v_a_1371_);
v_a_1415_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1386_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1386_);
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
}
else
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
lean_dec(v_val_1381_);
lean_dec_ref_known(v___x_1374_, 2);
lean_dec_ref(v_mctx_1373_);
lean_dec(v_a_1371_);
lean_dec_ref(v_searchFn_1361_);
v_a_1423_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1425_ = v___x_1382_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1382_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1428_; 
if (v_isShared_1426_ == 0)
{
v___x_1428_ = v___x_1425_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_a_1423_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
else
{
size_t v_sz_1431_; size_t v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1435_; 
lean_dec(v_a_1377_);
lean_dec_ref(v_mctx_1373_);
lean_dec_ref(v_searchFn_1361_);
v_sz_1431_ = lean_array_size(v_a_1371_);
v___x_1432_ = ((size_t)0ULL);
v___x_1433_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(v___x_1374_, v_sz_1431_, v___x_1432_, v_a_1371_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 0, v___x_1433_);
v___x_1435_ = v___x_1379_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_dec_ref_known(v___x_1374_, 2);
lean_dec_ref(v_mctx_1373_);
lean_dec(v_a_1371_);
lean_dec_ref(v_searchFn_1361_);
v_a_1438_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1376_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1376_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
else
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
lean_dec(v_goal_1362_);
lean_dec_ref(v_searchFn_1361_);
v_a_1446_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1370_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1370_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
else
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
lean_dec(v_goal_1362_);
lean_dec_ref(v_searchFn_1361_);
v_a_1454_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1368_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1368_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_a_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearchSymm___boxed(lean_object* v_searchFn_1462_, lean_object* v_goal_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v_searchFn_1462_, v_goal_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_);
lean_dec(v_a_1467_);
lean_dec_ref(v_a_1466_);
lean_dec(v_a_1465_);
lean_dec_ref(v_a_1464_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0(lean_object* v_e_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1480_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___closed__1));
v___x_1481_ = lean_unsigned_to_nat(1u);
v___x_1482_ = lean_mk_empty_array_with_capacity(v___x_1481_);
v___x_1483_ = lean_array_push(v___x_1482_, v_e_1474_);
v___x_1484_ = l_Lean_Meta_mkAppM(v___x_1480_, v___x_1483_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___boxed(lean_object* v_e_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0(v_e_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1(lean_object* v_e_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1502_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___closed__1));
v___x_1503_ = lean_unsigned_to_nat(1u);
v___x_1504_ = lean_mk_empty_array_with_capacity(v___x_1503_);
v___x_1505_ = lean_array_push(v___x_1504_, v_e_1496_);
v___x_1506_ = l_Lean_Meta_mkAppM(v___x_1502_, v___x_1505_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___boxed(lean_object* v_e_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1(v_e_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(lean_object* v_lem_1516_, uint8_t v_mod_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_lem_1516_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_);
if (lean_obj_tag(v___x_1523_) == 0)
{
switch(v_mod_1517_)
{
case 0:
{
return v___x_1523_;
}
case 1:
{
lean_object* v_a_1524_; lean_object* v___f_1525_; lean_object* v___x_1526_; 
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_a_1524_);
lean_dec_ref_known(v___x_1523_, 1);
v___f_1525_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__0));
v___x_1526_ = l_Lean_Meta_mapForallTelescope(v___f_1525_, v_a_1524_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_);
return v___x_1526_;
}
default: 
{
lean_object* v_a_1527_; lean_object* v___f_1528_; lean_object* v___x_1529_; 
v_a_1527_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_a_1527_);
lean_dec_ref_known(v___x_1523_, 1);
v___f_1528_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__1));
v___x_1529_ = l_Lean_Meta_mapForallTelescope(v___f_1528_, v_a_1527_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_);
return v___x_1529_;
}
}
}
else
{
return v___x_1523_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___boxed(lean_object* v_lem_1530_, lean_object* v_mod_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_){
_start:
{
uint8_t v_mod_boxed_1537_; lean_object* v_res_1538_; 
v_mod_boxed_1537_ = lean_unbox(v_mod_1531_);
v_res_1538_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_lem_1530_, v_mod_boxed_1537_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_);
lean_dec(v_a_1535_);
lean_dec_ref(v_a_1534_);
lean_dec(v_a_1533_);
lean_dec_ref(v_a_1532_);
return v_res_1538_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar(lean_object* v_e_1539_){
_start:
{
switch(lean_obj_tag(v_e_1539_))
{
case 0:
{
uint8_t v___x_1540_; 
v___x_1540_ = 1;
return v___x_1540_;
}
case 1:
{
uint8_t v___x_1541_; 
v___x_1541_ = 1;
return v___x_1541_;
}
case 2:
{
uint8_t v___x_1542_; 
v___x_1542_ = 1;
return v___x_1542_;
}
default: 
{
uint8_t v___x_1543_; 
v___x_1543_ = 0;
return v___x_1543_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar___boxed(lean_object* v_e_1544_){
_start:
{
uint8_t v_res_1545_; lean_object* v_r_1546_; 
v_res_1545_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar(v_e_1544_);
lean_dec_ref(v_e_1544_);
v_r_1546_ = lean_box(v_res_1545_);
return v_r_1546_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1547_ = lean_unsigned_to_nat(32u);
v___x_1548_ = lean_mk_empty_array_with_capacity(v___x_1547_);
v___x_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
return v___x_1549_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1550_ = ((size_t)5ULL);
v___x_1551_ = lean_unsigned_to_nat(0u);
v___x_1552_ = lean_unsigned_to_nat(32u);
v___x_1553_ = lean_mk_empty_array_with_capacity(v___x_1552_);
v___x_1554_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0);
v___x_1555_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
lean_ctor_set(v___x_1555_, 1, v___x_1553_);
lean_ctor_set(v___x_1555_, 2, v___x_1551_);
lean_ctor_set(v___x_1555_, 3, v___x_1551_);
lean_ctor_set_usize(v___x_1555_, 4, v___x_1550_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(lean_object* v___y_1556_){
_start:
{
lean_object* v___x_1558_; lean_object* v_traceState_1559_; lean_object* v_traces_1560_; lean_object* v___x_1561_; lean_object* v_traceState_1562_; lean_object* v_env_1563_; lean_object* v_nextMacroScope_1564_; lean_object* v_ngen_1565_; lean_object* v_auxDeclNGen_1566_; lean_object* v_cache_1567_; lean_object* v_messages_1568_; lean_object* v_infoState_1569_; lean_object* v_snapshotTasks_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1589_; 
v___x_1558_ = lean_st_ref_get(v___y_1556_);
v_traceState_1559_ = lean_ctor_get(v___x_1558_, 4);
lean_inc_ref(v_traceState_1559_);
lean_dec(v___x_1558_);
v_traces_1560_ = lean_ctor_get(v_traceState_1559_, 0);
lean_inc_ref(v_traces_1560_);
lean_dec_ref(v_traceState_1559_);
v___x_1561_ = lean_st_ref_take(v___y_1556_);
v_traceState_1562_ = lean_ctor_get(v___x_1561_, 4);
v_env_1563_ = lean_ctor_get(v___x_1561_, 0);
v_nextMacroScope_1564_ = lean_ctor_get(v___x_1561_, 1);
v_ngen_1565_ = lean_ctor_get(v___x_1561_, 2);
v_auxDeclNGen_1566_ = lean_ctor_get(v___x_1561_, 3);
v_cache_1567_ = lean_ctor_get(v___x_1561_, 5);
v_messages_1568_ = lean_ctor_get(v___x_1561_, 6);
v_infoState_1569_ = lean_ctor_get(v___x_1561_, 7);
v_snapshotTasks_1570_ = lean_ctor_get(v___x_1561_, 8);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1572_ = v___x_1561_;
v_isShared_1573_ = v_isSharedCheck_1589_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_snapshotTasks_1570_);
lean_inc(v_infoState_1569_);
lean_inc(v_messages_1568_);
lean_inc(v_cache_1567_);
lean_inc(v_traceState_1562_);
lean_inc(v_auxDeclNGen_1566_);
lean_inc(v_ngen_1565_);
lean_inc(v_nextMacroScope_1564_);
lean_inc(v_env_1563_);
lean_dec(v___x_1561_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1589_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
uint64_t v_tid_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1587_; 
v_tid_1574_ = lean_ctor_get_uint64(v_traceState_1562_, sizeof(void*)*1);
v_isSharedCheck_1587_ = !lean_is_exclusive(v_traceState_1562_);
if (v_isSharedCheck_1587_ == 0)
{
lean_object* v_unused_1588_; 
v_unused_1588_ = lean_ctor_get(v_traceState_1562_, 0);
lean_dec(v_unused_1588_);
v___x_1576_ = v_traceState_1562_;
v_isShared_1577_ = v_isSharedCheck_1587_;
goto v_resetjp_1575_;
}
else
{
lean_dec(v_traceState_1562_);
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
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_env_1563_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_nextMacroScope_1564_);
lean_ctor_set(v_reuseFailAlloc_1585_, 2, v_ngen_1565_);
lean_ctor_set(v_reuseFailAlloc_1585_, 3, v_auxDeclNGen_1566_);
lean_ctor_set(v_reuseFailAlloc_1585_, 4, v___x_1580_);
lean_ctor_set(v_reuseFailAlloc_1585_, 5, v_cache_1567_);
lean_ctor_set(v_reuseFailAlloc_1585_, 6, v_messages_1568_);
lean_ctor_set(v_reuseFailAlloc_1585_, 7, v_infoState_1569_);
lean_ctor_set(v_reuseFailAlloc_1585_, 8, v_snapshotTasks_1570_);
v___x_1582_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = lean_st_ref_set(v___y_1556_, v___x_1582_);
v___x_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1584_, 0, v_traces_1560_);
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
uint8_t v_snd_11696__boxed_1668_; lean_object* v_res_1669_; 
v_snd_11696__boxed_1668_ = lean_unbox(v_snd_1661_);
v_res_1669_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0(v_fst_1660_, v_snd_11696__boxed_1668_, v_x_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
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
lean_object* v_fileName_1729_; lean_object* v_fileMap_1730_; lean_object* v_options_1731_; lean_object* v_currRecDepth_1732_; lean_object* v_maxRecDepth_1733_; lean_object* v_ref_1734_; lean_object* v_currNamespace_1735_; lean_object* v_openDecls_1736_; lean_object* v_initHeartbeats_1737_; lean_object* v_maxHeartbeats_1738_; lean_object* v_quotContext_1739_; lean_object* v_currMacroScope_1740_; uint8_t v_diag_1741_; lean_object* v_cancelTk_x3f_1742_; uint8_t v_suppressElabErrors_1743_; lean_object* v_inheritedTraceOptions_1744_; lean_object* v___x_1745_; lean_object* v_traceState_1746_; lean_object* v_traces_1747_; lean_object* v_ref_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; size_t v_sz_1751_; size_t v___x_1752_; lean_object* v___x_1753_; lean_object* v_msg_1754_; lean_object* v___x_1755_; lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1793_; 
v_fileName_1729_ = lean_ctor_get(v___y_1726_, 0);
v_fileMap_1730_ = lean_ctor_get(v___y_1726_, 1);
v_options_1731_ = lean_ctor_get(v___y_1726_, 2);
v_currRecDepth_1732_ = lean_ctor_get(v___y_1726_, 3);
v_maxRecDepth_1733_ = lean_ctor_get(v___y_1726_, 4);
v_ref_1734_ = lean_ctor_get(v___y_1726_, 5);
v_currNamespace_1735_ = lean_ctor_get(v___y_1726_, 6);
v_openDecls_1736_ = lean_ctor_get(v___y_1726_, 7);
v_initHeartbeats_1737_ = lean_ctor_get(v___y_1726_, 8);
v_maxHeartbeats_1738_ = lean_ctor_get(v___y_1726_, 9);
v_quotContext_1739_ = lean_ctor_get(v___y_1726_, 10);
v_currMacroScope_1740_ = lean_ctor_get(v___y_1726_, 11);
v_diag_1741_ = lean_ctor_get_uint8(v___y_1726_, sizeof(void*)*14);
v_cancelTk_x3f_1742_ = lean_ctor_get(v___y_1726_, 12);
v_suppressElabErrors_1743_ = lean_ctor_get_uint8(v___y_1726_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1744_ = lean_ctor_get(v___y_1726_, 13);
v___x_1745_ = lean_st_ref_get(v___y_1727_);
v_traceState_1746_ = lean_ctor_get(v___x_1745_, 4);
lean_inc_ref(v_traceState_1746_);
lean_dec(v___x_1745_);
v_traces_1747_ = lean_ctor_get(v_traceState_1746_, 0);
lean_inc_ref(v_traces_1747_);
lean_dec_ref(v_traceState_1746_);
v_ref_1748_ = l_Lean_replaceRef(v_ref_1722_, v_ref_1734_);
lean_inc_ref(v_inheritedTraceOptions_1744_);
lean_inc(v_cancelTk_x3f_1742_);
lean_inc(v_currMacroScope_1740_);
lean_inc(v_quotContext_1739_);
lean_inc(v_maxHeartbeats_1738_);
lean_inc(v_initHeartbeats_1737_);
lean_inc(v_openDecls_1736_);
lean_inc(v_currNamespace_1735_);
lean_inc(v_maxRecDepth_1733_);
lean_inc(v_currRecDepth_1732_);
lean_inc_ref(v_options_1731_);
lean_inc_ref(v_fileMap_1730_);
lean_inc_ref(v_fileName_1729_);
v___x_1749_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1749_, 0, v_fileName_1729_);
lean_ctor_set(v___x_1749_, 1, v_fileMap_1730_);
lean_ctor_set(v___x_1749_, 2, v_options_1731_);
lean_ctor_set(v___x_1749_, 3, v_currRecDepth_1732_);
lean_ctor_set(v___x_1749_, 4, v_maxRecDepth_1733_);
lean_ctor_set(v___x_1749_, 5, v_ref_1748_);
lean_ctor_set(v___x_1749_, 6, v_currNamespace_1735_);
lean_ctor_set(v___x_1749_, 7, v_openDecls_1736_);
lean_ctor_set(v___x_1749_, 8, v_initHeartbeats_1737_);
lean_ctor_set(v___x_1749_, 9, v_maxHeartbeats_1738_);
lean_ctor_set(v___x_1749_, 10, v_quotContext_1739_);
lean_ctor_set(v___x_1749_, 11, v_currMacroScope_1740_);
lean_ctor_set(v___x_1749_, 12, v_cancelTk_x3f_1742_);
lean_ctor_set(v___x_1749_, 13, v_inheritedTraceOptions_1744_);
lean_ctor_set_uint8(v___x_1749_, sizeof(void*)*14, v_diag_1741_);
lean_ctor_set_uint8(v___x_1749_, sizeof(void*)*14 + 1, v_suppressElabErrors_1743_);
v___x_1750_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1747_);
lean_dec_ref(v_traces_1747_);
v_sz_1751_ = lean_array_size(v___x_1750_);
v___x_1752_ = ((size_t)0ULL);
v___x_1753_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3(v_sz_1751_, v___x_1752_, v___x_1750_);
v_msg_1754_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1754_, 0, v_data_1721_);
lean_ctor_set(v_msg_1754_, 1, v_msg_1723_);
lean_ctor_set(v_msg_1754_, 2, v___x_1753_);
v___x_1755_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(v_msg_1754_, v___y_1724_, v___y_1725_, v___x_1749_, v___y_1727_);
lean_dec_ref_known(v___x_1749_, 14);
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1758_ = v___x_1755_;
v_isShared_1759_ = v_isSharedCheck_1793_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1755_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1793_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1760_; lean_object* v_traceState_1761_; lean_object* v_env_1762_; lean_object* v_nextMacroScope_1763_; lean_object* v_ngen_1764_; lean_object* v_auxDeclNGen_1765_; lean_object* v_cache_1766_; lean_object* v_messages_1767_; lean_object* v_infoState_1768_; lean_object* v_snapshotTasks_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1792_; 
v___x_1760_ = lean_st_ref_take(v___y_1727_);
v_traceState_1761_ = lean_ctor_get(v___x_1760_, 4);
v_env_1762_ = lean_ctor_get(v___x_1760_, 0);
v_nextMacroScope_1763_ = lean_ctor_get(v___x_1760_, 1);
v_ngen_1764_ = lean_ctor_get(v___x_1760_, 2);
v_auxDeclNGen_1765_ = lean_ctor_get(v___x_1760_, 3);
v_cache_1766_ = lean_ctor_get(v___x_1760_, 5);
v_messages_1767_ = lean_ctor_get(v___x_1760_, 6);
v_infoState_1768_ = lean_ctor_get(v___x_1760_, 7);
v_snapshotTasks_1769_ = lean_ctor_get(v___x_1760_, 8);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1771_ = v___x_1760_;
v_isShared_1772_ = v_isSharedCheck_1792_;
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
v_isShared_1772_ = v_isSharedCheck_1792_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
uint64_t v_tid_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1790_; 
v_tid_1773_ = lean_ctor_get_uint64(v_traceState_1761_, sizeof(void*)*1);
v_isSharedCheck_1790_ = !lean_is_exclusive(v_traceState_1761_);
if (v_isSharedCheck_1790_ == 0)
{
lean_object* v_unused_1791_; 
v_unused_1791_ = lean_ctor_get(v_traceState_1761_, 0);
lean_dec(v_unused_1791_);
v___x_1775_ = v_traceState_1761_;
v_isShared_1776_ = v_isSharedCheck_1790_;
goto v_resetjp_1774_;
}
else
{
lean_dec(v_traceState_1761_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1790_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1780_; 
v___x_1777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1777_, 0, v_ref_1722_);
lean_ctor_set(v___x_1777_, 1, v_a_1756_);
v___x_1778_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1720_, v___x_1777_);
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 0, v___x_1778_);
v___x_1780_ = v___x_1775_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1778_);
lean_ctor_set_uint64(v_reuseFailAlloc_1789_, sizeof(void*)*1, v_tid_1773_);
v___x_1780_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
lean_object* v___x_1782_; 
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 4, v___x_1780_);
v___x_1782_ = v___x_1771_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_env_1762_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v_nextMacroScope_1763_);
lean_ctor_set(v_reuseFailAlloc_1788_, 2, v_ngen_1764_);
lean_ctor_set(v_reuseFailAlloc_1788_, 3, v_auxDeclNGen_1765_);
lean_ctor_set(v_reuseFailAlloc_1788_, 4, v___x_1780_);
lean_ctor_set(v_reuseFailAlloc_1788_, 5, v_cache_1766_);
lean_ctor_set(v_reuseFailAlloc_1788_, 6, v_messages_1767_);
lean_ctor_set(v_reuseFailAlloc_1788_, 7, v_infoState_1768_);
lean_ctor_set(v_reuseFailAlloc_1788_, 8, v_snapshotTasks_1769_);
v___x_1782_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1786_; 
v___x_1783_ = lean_st_ref_set(v___y_1727_, v___x_1782_);
v___x_1784_ = lean_box(0);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 0, v___x_1784_);
v___x_1786_ = v___x_1758_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1784_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2___boxed(lean_object* v_oldTraces_1794_, lean_object* v_data_1795_, lean_object* v_ref_1796_, lean_object* v_msg_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(v_oldTraces_1794_, v_data_1795_, v_ref_1796_, v_msg_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
return v_res_1803_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(lean_object* v_e_1804_){
_start:
{
if (lean_obj_tag(v_e_1804_) == 0)
{
uint8_t v___x_1805_; 
v___x_1805_ = 2;
return v___x_1805_;
}
else
{
uint8_t v___x_1806_; 
v___x_1806_ = 0;
return v___x_1806_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4___boxed(lean_object* v_e_1807_){
_start:
{
uint8_t v_res_1808_; lean_object* v_r_1809_; 
v_res_1808_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(v_e_1807_);
lean_dec_ref(v_e_1807_);
v_r_1809_ = lean_box(v_res_1808_);
return v_r_1809_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1810_; double v___x_1811_; 
v___x_1810_ = lean_unsigned_to_nat(0u);
v___x_1811_ = lean_float_of_nat(v___x_1810_);
return v___x_1811_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1813_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__1));
v___x_1814_ = l_Lean_stringToMessageData(v___x_1813_);
return v___x_1814_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1815_; double v___x_1816_; 
v___x_1815_ = lean_unsigned_to_nat(1000u);
v___x_1816_ = lean_float_of_nat(v___x_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(lean_object* v_cls_1817_, uint8_t v_collapsed_1818_, lean_object* v_tag_1819_, lean_object* v_opts_1820_, uint8_t v_clsEnabled_1821_, lean_object* v_oldTraces_1822_, lean_object* v_msg_1823_, lean_object* v_resStartStop_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v_fst_1830_; lean_object* v_snd_1831_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v_data_1835_; lean_object* v_fst_1846_; lean_object* v_snd_1847_; lean_object* v___x_1848_; uint8_t v___x_1849_; lean_object* v___y_1851_; lean_object* v_a_1852_; uint8_t v___y_1867_; double v___y_1898_; 
v_fst_1830_ = lean_ctor_get(v_resStartStop_1824_, 0);
lean_inc(v_fst_1830_);
v_snd_1831_ = lean_ctor_get(v_resStartStop_1824_, 1);
lean_inc(v_snd_1831_);
lean_dec_ref(v_resStartStop_1824_);
v_fst_1846_ = lean_ctor_get(v_snd_1831_, 0);
lean_inc(v_fst_1846_);
v_snd_1847_ = lean_ctor_get(v_snd_1831_, 1);
lean_inc(v_snd_1847_);
lean_dec(v_snd_1831_);
v___x_1848_ = l_Lean_trace_profiler;
v___x_1849_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_1820_, v___x_1848_);
if (v___x_1849_ == 0)
{
v___y_1867_ = v___x_1849_;
goto v___jp_1866_;
}
else
{
lean_object* v___x_1903_; uint8_t v___x_1904_; 
v___x_1903_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1904_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_1820_, v___x_1903_);
if (v___x_1904_ == 0)
{
lean_object* v___x_1905_; lean_object* v___x_1906_; double v___x_1907_; double v___x_1908_; double v___x_1909_; 
v___x_1905_ = l_Lean_trace_profiler_threshold;
v___x_1906_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_1820_, v___x_1905_);
v___x_1907_ = lean_float_of_nat(v___x_1906_);
v___x_1908_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3);
v___x_1909_ = lean_float_div(v___x_1907_, v___x_1908_);
v___y_1898_ = v___x_1909_;
goto v___jp_1897_;
}
else
{
lean_object* v___x_1910_; lean_object* v___x_1911_; double v___x_1912_; 
v___x_1910_ = l_Lean_trace_profiler_threshold;
v___x_1911_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_1820_, v___x_1910_);
v___x_1912_ = lean_float_of_nat(v___x_1911_);
v___y_1898_ = v___x_1912_;
goto v___jp_1897_;
}
}
v___jp_1832_:
{
lean_object* v___x_1836_; 
lean_inc(v___y_1834_);
v___x_1836_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(v_oldTraces_1822_, v_data_1835_, v___y_1834_, v___y_1833_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v___x_1837_; 
lean_dec_ref_known(v___x_1836_, 1);
v___x_1837_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_1830_);
return v___x_1837_;
}
else
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
lean_dec(v_fst_1830_);
v_a_1838_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___x_1836_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1836_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1838_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
v___jp_1850_:
{
uint8_t v_result_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; double v___x_1856_; lean_object* v_data_1857_; 
v_result_1853_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(v_fst_1830_);
v___x_1854_ = lean_box(v_result_1853_);
v___x_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
v___x_1856_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0);
lean_inc_ref(v_tag_1819_);
lean_inc_ref(v___x_1855_);
lean_inc(v_cls_1817_);
v_data_1857_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1857_, 0, v_cls_1817_);
lean_ctor_set(v_data_1857_, 1, v___x_1855_);
lean_ctor_set(v_data_1857_, 2, v_tag_1819_);
lean_ctor_set_float(v_data_1857_, sizeof(void*)*3, v___x_1856_);
lean_ctor_set_float(v_data_1857_, sizeof(void*)*3 + 8, v___x_1856_);
lean_ctor_set_uint8(v_data_1857_, sizeof(void*)*3 + 16, v_collapsed_1818_);
if (v___x_1849_ == 0)
{
lean_dec_ref_known(v___x_1855_, 1);
lean_dec(v_snd_1847_);
lean_dec(v_fst_1846_);
lean_dec_ref(v_tag_1819_);
lean_dec(v_cls_1817_);
v___y_1833_ = v_a_1852_;
v___y_1834_ = v___y_1851_;
v_data_1835_ = v_data_1857_;
goto v___jp_1832_;
}
else
{
lean_object* v_data_1858_; double v___x_1859_; double v___x_1860_; 
lean_dec_ref_known(v_data_1857_, 3);
v_data_1858_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1858_, 0, v_cls_1817_);
lean_ctor_set(v_data_1858_, 1, v___x_1855_);
lean_ctor_set(v_data_1858_, 2, v_tag_1819_);
v___x_1859_ = lean_unbox_float(v_fst_1846_);
lean_dec(v_fst_1846_);
lean_ctor_set_float(v_data_1858_, sizeof(void*)*3, v___x_1859_);
v___x_1860_ = lean_unbox_float(v_snd_1847_);
lean_dec(v_snd_1847_);
lean_ctor_set_float(v_data_1858_, sizeof(void*)*3 + 8, v___x_1860_);
lean_ctor_set_uint8(v_data_1858_, sizeof(void*)*3 + 16, v_collapsed_1818_);
v___y_1833_ = v_a_1852_;
v___y_1834_ = v___y_1851_;
v_data_1835_ = v_data_1858_;
goto v___jp_1832_;
}
}
v___jp_1861_:
{
lean_object* v_ref_1862_; lean_object* v___x_1863_; 
v_ref_1862_ = lean_ctor_get(v___y_1827_, 5);
lean_inc(v___y_1828_);
lean_inc_ref(v___y_1827_);
lean_inc(v___y_1826_);
lean_inc_ref(v___y_1825_);
lean_inc(v_fst_1830_);
v___x_1863_ = lean_apply_6(v_msg_1823_, v_fst_1830_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, lean_box(0));
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_a_1864_);
lean_dec_ref_known(v___x_1863_, 1);
v___y_1851_ = v_ref_1862_;
v_a_1852_ = v_a_1864_;
goto v___jp_1850_;
}
else
{
lean_object* v___x_1865_; 
lean_dec_ref_known(v___x_1863_, 1);
v___x_1865_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2);
v___y_1851_ = v_ref_1862_;
v_a_1852_ = v___x_1865_;
goto v___jp_1850_;
}
}
v___jp_1866_:
{
if (v_clsEnabled_1821_ == 0)
{
if (v___y_1867_ == 0)
{
lean_object* v___x_1868_; lean_object* v_traceState_1869_; lean_object* v_env_1870_; lean_object* v_nextMacroScope_1871_; lean_object* v_ngen_1872_; lean_object* v_auxDeclNGen_1873_; lean_object* v_cache_1874_; lean_object* v_messages_1875_; lean_object* v_infoState_1876_; lean_object* v_snapshotTasks_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1896_; 
lean_dec(v_snd_1847_);
lean_dec(v_fst_1846_);
lean_dec_ref(v_msg_1823_);
lean_dec_ref(v_tag_1819_);
lean_dec(v_cls_1817_);
v___x_1868_ = lean_st_ref_take(v___y_1828_);
v_traceState_1869_ = lean_ctor_get(v___x_1868_, 4);
v_env_1870_ = lean_ctor_get(v___x_1868_, 0);
v_nextMacroScope_1871_ = lean_ctor_get(v___x_1868_, 1);
v_ngen_1872_ = lean_ctor_get(v___x_1868_, 2);
v_auxDeclNGen_1873_ = lean_ctor_get(v___x_1868_, 3);
v_cache_1874_ = lean_ctor_get(v___x_1868_, 5);
v_messages_1875_ = lean_ctor_get(v___x_1868_, 6);
v_infoState_1876_ = lean_ctor_get(v___x_1868_, 7);
v_snapshotTasks_1877_ = lean_ctor_get(v___x_1868_, 8);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1879_ = v___x_1868_;
v_isShared_1880_ = v_isSharedCheck_1896_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_snapshotTasks_1877_);
lean_inc(v_infoState_1876_);
lean_inc(v_messages_1875_);
lean_inc(v_cache_1874_);
lean_inc(v_traceState_1869_);
lean_inc(v_auxDeclNGen_1873_);
lean_inc(v_ngen_1872_);
lean_inc(v_nextMacroScope_1871_);
lean_inc(v_env_1870_);
lean_dec(v___x_1868_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1896_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
uint64_t v_tid_1881_; lean_object* v_traces_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1895_; 
v_tid_1881_ = lean_ctor_get_uint64(v_traceState_1869_, sizeof(void*)*1);
v_traces_1882_ = lean_ctor_get(v_traceState_1869_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v_traceState_1869_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1884_ = v_traceState_1869_;
v_isShared_1885_ = v_isSharedCheck_1895_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_traces_1882_);
lean_dec(v_traceState_1869_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1895_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1886_; lean_object* v___x_1888_; 
v___x_1886_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1822_, v_traces_1882_);
lean_dec_ref(v_traces_1882_);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 0, v___x_1886_);
v___x_1888_ = v___x_1884_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1886_);
lean_ctor_set_uint64(v_reuseFailAlloc_1894_, sizeof(void*)*1, v_tid_1881_);
v___x_1888_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1890_; 
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 4, v___x_1888_);
v___x_1890_ = v___x_1879_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_env_1870_);
lean_ctor_set(v_reuseFailAlloc_1893_, 1, v_nextMacroScope_1871_);
lean_ctor_set(v_reuseFailAlloc_1893_, 2, v_ngen_1872_);
lean_ctor_set(v_reuseFailAlloc_1893_, 3, v_auxDeclNGen_1873_);
lean_ctor_set(v_reuseFailAlloc_1893_, 4, v___x_1888_);
lean_ctor_set(v_reuseFailAlloc_1893_, 5, v_cache_1874_);
lean_ctor_set(v_reuseFailAlloc_1893_, 6, v_messages_1875_);
lean_ctor_set(v_reuseFailAlloc_1893_, 7, v_infoState_1876_);
lean_ctor_set(v_reuseFailAlloc_1893_, 8, v_snapshotTasks_1877_);
v___x_1890_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = lean_st_ref_set(v___y_1828_, v___x_1890_);
v___x_1892_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_1830_);
return v___x_1892_;
}
}
}
}
}
else
{
goto v___jp_1861_;
}
}
else
{
goto v___jp_1861_;
}
}
v___jp_1897_:
{
double v___x_1899_; double v___x_1900_; double v___x_1901_; uint8_t v___x_1902_; 
v___x_1899_ = lean_unbox_float(v_snd_1847_);
v___x_1900_ = lean_unbox_float(v_fst_1846_);
v___x_1901_ = lean_float_sub(v___x_1899_, v___x_1900_);
v___x_1902_ = lean_float_decLt(v___y_1898_, v___x_1901_);
v___y_1867_ = v___x_1902_;
goto v___jp_1866_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___boxed(lean_object* v_cls_1913_, lean_object* v_collapsed_1914_, lean_object* v_tag_1915_, lean_object* v_opts_1916_, lean_object* v_clsEnabled_1917_, lean_object* v_oldTraces_1918_, lean_object* v_msg_1919_, lean_object* v_resStartStop_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
uint8_t v_collapsed_boxed_1926_; uint8_t v_clsEnabled_boxed_1927_; lean_object* v_res_1928_; 
v_collapsed_boxed_1926_ = lean_unbox(v_collapsed_1914_);
v_clsEnabled_boxed_1927_ = lean_unbox(v_clsEnabled_1917_);
v_res_1928_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v_cls_1913_, v_collapsed_boxed_1926_, v_tag_1915_, v_opts_1916_, v_clsEnabled_boxed_1927_, v_oldTraces_1918_, v_msg_1919_, v_resStartStop_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
lean_dec_ref(v_opts_1916_);
return v_res_1928_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2(void){
_start:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1932_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_1933_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__1));
v___x_1934_ = l_Lean_Name_append(v___x_1933_, v___x_1932_);
return v___x_1934_;
}
}
static double _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3(void){
_start:
{
lean_object* v___x_1935_; double v___x_1936_; 
v___x_1935_ = lean_unsigned_to_nat(1000000000u);
v___x_1936_ = lean_float_of_nat(v___x_1935_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(lean_object* v_cfg_1937_, lean_object* v_act_1938_, lean_object* v_allowFailure_1939_, lean_object* v_cand_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_){
_start:
{
lean_object* v_fst_1946_; lean_object* v_snd_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_2233_; 
v_fst_1946_ = lean_ctor_get(v_cand_1940_, 0);
v_snd_1947_ = lean_ctor_get(v_cand_1940_, 1);
v_isSharedCheck_2233_ = !lean_is_exclusive(v_cand_1940_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_1949_ = v_cand_1940_;
v_isShared_1950_ = v_isSharedCheck_2233_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_snd_1947_);
lean_inc(v_fst_1946_);
lean_dec(v_cand_1940_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_2233_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v_options_1951_; uint8_t v_hasTrace_1952_; 
v_options_1951_ = lean_ctor_get(v_a_1943_, 2);
v_hasTrace_1952_ = lean_ctor_get_uint8(v_options_1951_, sizeof(void*)*1);
if (v_hasTrace_1952_ == 0)
{
lean_object* v_fst_1953_; lean_object* v_snd_1954_; lean_object* v_fst_1955_; lean_object* v_snd_1956_; lean_object* v___x_1957_; lean_object* v_cache_1958_; lean_object* v_zetaDeltaFVarIds_1959_; lean_object* v_postponed_1960_; lean_object* v_diag_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_2009_; 
lean_del_object(v___x_1949_);
v_fst_1953_ = lean_ctor_get(v_fst_1946_, 0);
lean_inc(v_fst_1953_);
v_snd_1954_ = lean_ctor_get(v_fst_1946_, 1);
lean_inc(v_snd_1954_);
lean_dec(v_fst_1946_);
v_fst_1955_ = lean_ctor_get(v_snd_1947_, 0);
lean_inc(v_fst_1955_);
v_snd_1956_ = lean_ctor_get(v_snd_1947_, 1);
lean_inc(v_snd_1956_);
lean_dec(v_snd_1947_);
v___x_1957_ = lean_st_ref_take(v_a_1942_);
v_cache_1958_ = lean_ctor_get(v___x_1957_, 1);
v_zetaDeltaFVarIds_1959_ = lean_ctor_get(v___x_1957_, 2);
v_postponed_1960_ = lean_ctor_get(v___x_1957_, 3);
v_diag_1961_ = lean_ctor_get(v___x_1957_, 4);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_2009_ == 0)
{
lean_object* v_unused_2010_; 
v_unused_2010_ = lean_ctor_get(v___x_1957_, 0);
lean_dec(v_unused_2010_);
v___x_1963_ = v___x_1957_;
v_isShared_1964_ = v_isSharedCheck_2009_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_diag_1961_);
lean_inc(v_postponed_1960_);
lean_inc(v_zetaDeltaFVarIds_1959_);
lean_inc(v_cache_1958_);
lean_dec(v___x_1957_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_2009_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v_snd_1954_);
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_snd_1954_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v_cache_1958_);
lean_ctor_set(v_reuseFailAlloc_2008_, 2, v_zetaDeltaFVarIds_1959_);
lean_ctor_set(v_reuseFailAlloc_2008_, 3, v_postponed_1960_);
lean_ctor_set(v_reuseFailAlloc_2008_, 4, v_diag_1961_);
v___x_1966_ = v_reuseFailAlloc_2008_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
lean_object* v___x_1967_; uint8_t v___x_1968_; lean_object* v___x_1969_; 
v___x_1967_ = lean_st_ref_set(v_a_1942_, v___x_1966_);
v___x_1968_ = lean_unbox(v_snd_1956_);
lean_dec(v_snd_1956_);
v___x_1969_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_1955_, v___x_1968_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_a_1970_);
lean_dec_ref_known(v___x_1969_, 1);
v___x_1971_ = lean_box(0);
lean_inc(v_fst_1953_);
v___x_1972_ = l_Lean_MVarId_apply(v_fst_1953_, v_a_1970_, v_cfg_1937_, v___x_1971_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_a_1973_; lean_object* v___x_1974_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
lean_inc_n(v_a_1973_, 2);
lean_dec_ref_known(v___x_1972_, 1);
lean_inc(v_a_1944_);
lean_inc_ref(v_a_1943_);
lean_inc(v_a_1942_);
lean_inc_ref(v_a_1941_);
v___x_1974_ = lean_apply_6(v_act_1938_, v_a_1973_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, lean_box(0));
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_dec(v_a_1973_);
lean_dec(v_fst_1953_);
lean_dec_ref(v_allowFailure_1939_);
return v___x_1974_;
}
else
{
lean_object* v_a_1975_; uint8_t v___y_1977_; uint8_t v___x_1998_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_a_1975_);
v___x_1998_ = l_Lean_Exception_isInterrupt(v_a_1975_);
if (v___x_1998_ == 0)
{
uint8_t v___x_1999_; 
v___x_1999_ = l_Lean_Exception_isRuntime(v_a_1975_);
v___y_1977_ = v___x_1999_;
goto v___jp_1976_;
}
else
{
lean_dec(v_a_1975_);
v___y_1977_ = v___x_1998_;
goto v___jp_1976_;
}
v___jp_1976_:
{
if (v___y_1977_ == 0)
{
lean_object* v___x_1978_; 
lean_dec_ref_known(v___x_1974_, 1);
lean_inc(v_a_1944_);
lean_inc_ref(v_a_1943_);
lean_inc(v_a_1942_);
lean_inc_ref(v_a_1941_);
v___x_1978_ = lean_apply_6(v_allowFailure_1939_, v_fst_1953_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, lean_box(0));
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1989_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1981_ = v___x_1978_;
v_isShared_1982_ = v_isSharedCheck_1989_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1978_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1989_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
uint8_t v___x_1983_; 
v___x_1983_ = lean_unbox(v_a_1979_);
lean_dec(v_a_1979_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
lean_del_object(v___x_1981_);
lean_dec(v_a_1973_);
v___x_1984_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1);
v___x_1985_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_1984_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
return v___x_1985_;
}
else
{
lean_object* v___x_1987_; 
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 0, v_a_1973_);
v___x_1987_ = v___x_1981_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_a_1973_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
}
else
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
lean_dec(v_a_1973_);
v_a_1990_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1992_ = v___x_1978_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1978_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
else
{
lean_dec(v_a_1973_);
lean_dec(v_fst_1953_);
lean_dec_ref(v_allowFailure_1939_);
return v___x_1974_;
}
}
}
}
else
{
lean_dec(v_fst_1953_);
lean_dec_ref(v_allowFailure_1939_);
lean_dec_ref(v_act_1938_);
return v___x_1972_;
}
}
else
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
lean_dec(v_fst_1953_);
lean_dec_ref(v_allowFailure_1939_);
lean_dec_ref(v_act_1938_);
lean_dec_ref(v_cfg_1937_);
v_a_2000_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1969_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1969_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
}
}
else
{
lean_object* v_fst_2011_; lean_object* v_snd_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2232_; 
v_fst_2011_ = lean_ctor_get(v_fst_1946_, 0);
v_snd_2012_ = lean_ctor_get(v_fst_1946_, 1);
v_isSharedCheck_2232_ = !lean_is_exclusive(v_fst_1946_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2014_ = v_fst_1946_;
v_isShared_2015_ = v_isSharedCheck_2232_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_snd_2012_);
lean_inc(v_fst_2011_);
lean_dec(v_fst_1946_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2232_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v_fst_2016_; lean_object* v_snd_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2231_; 
v_fst_2016_ = lean_ctor_get(v_snd_1947_, 0);
v_snd_2017_ = lean_ctor_get(v_snd_1947_, 1);
v_isSharedCheck_2231_ = !lean_is_exclusive(v_snd_1947_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2019_ = v_snd_1947_;
v_isShared_2020_ = v_isSharedCheck_2231_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_snd_2017_);
lean_inc(v_fst_2016_);
lean_dec(v_snd_1947_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2231_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v_inheritedTraceOptions_2021_; lean_object* v___f_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; uint8_t v___x_2026_; lean_object* v___y_2028_; lean_object* v___y_2029_; lean_object* v_a_2030_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v_a_2049_; lean_object* v___y_2052_; lean_object* v___y_2053_; lean_object* v_a_2054_; lean_object* v___y_2057_; lean_object* v___y_2058_; lean_object* v___y_2059_; lean_object* v___y_2063_; lean_object* v___y_2064_; lean_object* v___y_2065_; lean_object* v___y_2066_; uint8_t v___y_2067_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v_a_2077_; lean_object* v___y_2089_; lean_object* v___y_2090_; lean_object* v_a_2091_; lean_object* v___y_2094_; lean_object* v___y_2095_; lean_object* v_a_2096_; lean_object* v___y_2099_; lean_object* v___y_2100_; lean_object* v___y_2101_; lean_object* v___y_2105_; lean_object* v___y_2106_; lean_object* v___y_2107_; lean_object* v___y_2108_; uint8_t v___y_2109_; 
v_inheritedTraceOptions_2021_ = lean_ctor_get(v_a_1943_, 13);
lean_inc(v_snd_2017_);
lean_inc(v_fst_2016_);
v___f_2022_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2022_, 0, v_fst_2016_);
lean_closure_set(v___f_2022_, 1, v_snd_2017_);
v___x_2023_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_2024_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__4));
v___x_2025_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2);
v___x_2026_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2021_, v_options_1951_, v___x_2025_);
if (v___x_2026_ == 0)
{
lean_object* v___x_2175_; uint8_t v___x_2176_; 
v___x_2175_ = l_Lean_trace_profiler;
v___x_2176_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_1951_, v___x_2175_);
if (v___x_2176_ == 0)
{
lean_object* v___x_2177_; lean_object* v_cache_2178_; lean_object* v_zetaDeltaFVarIds_2179_; lean_object* v_postponed_2180_; lean_object* v_diag_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2229_; 
lean_dec_ref(v___f_2022_);
lean_del_object(v___x_2019_);
lean_del_object(v___x_2014_);
lean_del_object(v___x_1949_);
v___x_2177_ = lean_st_ref_take(v_a_1942_);
v_cache_2178_ = lean_ctor_get(v___x_2177_, 1);
v_zetaDeltaFVarIds_2179_ = lean_ctor_get(v___x_2177_, 2);
v_postponed_2180_ = lean_ctor_get(v___x_2177_, 3);
v_diag_2181_ = lean_ctor_get(v___x_2177_, 4);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2229_ == 0)
{
lean_object* v_unused_2230_; 
v_unused_2230_ = lean_ctor_get(v___x_2177_, 0);
lean_dec(v_unused_2230_);
v___x_2183_ = v___x_2177_;
v_isShared_2184_ = v_isSharedCheck_2229_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_diag_2181_);
lean_inc(v_postponed_2180_);
lean_inc(v_zetaDeltaFVarIds_2179_);
lean_inc(v_cache_2178_);
lean_dec(v___x_2177_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2229_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 0, v_snd_2012_);
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_snd_2012_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v_cache_2178_);
lean_ctor_set(v_reuseFailAlloc_2228_, 2, v_zetaDeltaFVarIds_2179_);
lean_ctor_set(v_reuseFailAlloc_2228_, 3, v_postponed_2180_);
lean_ctor_set(v_reuseFailAlloc_2228_, 4, v_diag_2181_);
v___x_2186_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
lean_object* v___x_2187_; uint8_t v___x_2188_; lean_object* v___x_2189_; 
v___x_2187_ = lean_st_ref_set(v_a_1942_, v___x_2186_);
v___x_2188_ = lean_unbox(v_snd_2017_);
lean_dec(v_snd_2017_);
v___x_2189_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_2016_, v___x_2188_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_a_2190_);
lean_dec_ref_known(v___x_2189_, 1);
v___x_2191_ = lean_box(0);
lean_inc(v_fst_2011_);
v___x_2192_ = l_Lean_MVarId_apply(v_fst_2011_, v_a_2190_, v_cfg_1937_, v___x_2191_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; lean_object* v___x_2194_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc_n(v_a_2193_, 2);
lean_dec_ref_known(v___x_2192_, 1);
lean_inc(v_a_1944_);
lean_inc_ref(v_a_1943_);
lean_inc(v_a_1942_);
lean_inc_ref(v_a_1941_);
v___x_2194_ = lean_apply_6(v_act_1938_, v_a_2193_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, lean_box(0));
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_dec(v_a_2193_);
lean_dec(v_fst_2011_);
lean_dec_ref(v_allowFailure_1939_);
return v___x_2194_;
}
else
{
lean_object* v_a_2195_; uint8_t v___y_2197_; uint8_t v___x_2218_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_a_2195_);
v___x_2218_ = l_Lean_Exception_isInterrupt(v_a_2195_);
if (v___x_2218_ == 0)
{
uint8_t v___x_2219_; 
v___x_2219_ = l_Lean_Exception_isRuntime(v_a_2195_);
v___y_2197_ = v___x_2219_;
goto v___jp_2196_;
}
else
{
lean_dec(v_a_2195_);
v___y_2197_ = v___x_2218_;
goto v___jp_2196_;
}
v___jp_2196_:
{
if (v___y_2197_ == 0)
{
lean_object* v___x_2198_; 
lean_dec_ref_known(v___x_2194_, 1);
lean_inc(v_a_1944_);
lean_inc_ref(v_a_1943_);
lean_inc(v_a_1942_);
lean_inc_ref(v_a_1941_);
v___x_2198_ = lean_apply_6(v_allowFailure_1939_, v_fst_2011_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, lean_box(0));
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2209_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2201_ = v___x_2198_;
v_isShared_2202_ = v_isSharedCheck_2209_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2198_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2209_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
uint8_t v___x_2203_; 
v___x_2203_ = lean_unbox(v_a_2199_);
lean_dec(v_a_2199_);
if (v___x_2203_ == 0)
{
lean_object* v___x_2204_; lean_object* v___x_2205_; 
lean_del_object(v___x_2201_);
lean_dec(v_a_2193_);
v___x_2204_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1);
v___x_2205_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2204_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
return v___x_2205_;
}
else
{
lean_object* v___x_2207_; 
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 0, v_a_2193_);
v___x_2207_ = v___x_2201_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2193_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
lean_dec(v_a_2193_);
v_a_2210_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2198_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2198_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2215_; 
if (v_isShared_2213_ == 0)
{
v___x_2215_ = v___x_2212_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2210_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
else
{
lean_dec(v_a_2193_);
lean_dec(v_fst_2011_);
lean_dec_ref(v_allowFailure_1939_);
return v___x_2194_;
}
}
}
}
else
{
lean_dec(v_fst_2011_);
lean_dec_ref(v_allowFailure_1939_);
lean_dec_ref(v_act_1938_);
return v___x_2192_;
}
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
lean_dec(v_fst_2011_);
lean_dec_ref(v_allowFailure_1939_);
lean_dec_ref(v_act_1938_);
lean_dec_ref(v_cfg_1937_);
v_a_2220_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2189_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2189_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
}
}
else
{
goto v___jp_2116_;
}
}
else
{
goto v___jp_2116_;
}
v___jp_2027_:
{
lean_object* v___x_2031_; double v___x_2032_; double v___x_2033_; double v___x_2034_; double v___x_2035_; double v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2040_; 
v___x_2031_ = lean_io_mono_nanos_now();
v___x_2032_ = lean_float_of_nat(v___y_2029_);
v___x_2033_ = lean_float_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3);
v___x_2034_ = lean_float_div(v___x_2032_, v___x_2033_);
v___x_2035_ = lean_float_of_nat(v___x_2031_);
v___x_2036_ = lean_float_div(v___x_2035_, v___x_2033_);
v___x_2037_ = lean_box_float(v___x_2034_);
v___x_2038_ = lean_box_float(v___x_2036_);
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 1, v___x_2038_);
lean_ctor_set(v___x_2019_, 0, v___x_2037_);
v___x_2040_ = v___x_2019_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2037_);
lean_ctor_set(v_reuseFailAlloc_2045_, 1, v___x_2038_);
v___x_2040_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
lean_object* v___x_2042_; 
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 1, v___x_2040_);
lean_ctor_set(v___x_2014_, 0, v_a_2030_);
v___x_2042_ = v___x_2014_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2030_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
lean_object* v___x_2043_; 
v___x_2043_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v___x_2023_, v_hasTrace_1952_, v___x_2024_, v_options_1951_, v___x_2026_, v___y_2028_, v___f_2022_, v___x_2042_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
return v___x_2043_;
}
}
}
v___jp_2046_:
{
lean_object* v___x_2050_; 
v___x_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2050_, 0, v_a_2049_);
v___y_2028_ = v___y_2047_;
v___y_2029_ = v___y_2048_;
v_a_2030_ = v___x_2050_;
goto v___jp_2027_;
}
v___jp_2051_:
{
lean_object* v___x_2055_; 
v___x_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2055_, 0, v_a_2054_);
v___y_2028_ = v___y_2052_;
v___y_2029_ = v___y_2053_;
v_a_2030_ = v___x_2055_;
goto v___jp_2027_;
}
v___jp_2056_:
{
if (lean_obj_tag(v___y_2059_) == 0)
{
lean_object* v_a_2060_; 
v_a_2060_ = lean_ctor_get(v___y_2059_, 0);
lean_inc(v_a_2060_);
lean_dec_ref_known(v___y_2059_, 1);
v___y_2047_ = v___y_2057_;
v___y_2048_ = v___y_2058_;
v_a_2049_ = v_a_2060_;
goto v___jp_2046_;
}
else
{
lean_object* v_a_2061_; 
v_a_2061_ = lean_ctor_get(v___y_2059_, 0);
lean_inc(v_a_2061_);
lean_dec_ref_known(v___y_2059_, 1);
v___y_2052_ = v___y_2057_;
v___y_2053_ = v___y_2058_;
v_a_2054_ = v_a_2061_;
goto v___jp_2051_;
}
}
v___jp_2062_:
{
if (v___y_2067_ == 0)
{
lean_object* v___x_2068_; 
lean_dec_ref(v___y_2064_);
lean_inc(v_a_1944_);
lean_inc_ref(v_a_1943_);
lean_inc(v_a_1942_);
lean_inc_ref(v_a_1941_);
v___x_2068_ = lean_apply_6(v_allowFailure_1939_, v_fst_2011_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, lean_box(0));
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v_a_2069_; uint8_t v___x_2070_; 
v_a_2069_ = lean_ctor_get(v___x_2068_, 0);
lean_inc(v_a_2069_);
lean_dec_ref_known(v___x_2068_, 1);
v___x_2070_ = lean_unbox(v_a_2069_);
lean_dec(v_a_2069_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; lean_object* v___x_2072_; 
lean_dec(v___y_2066_);
v___x_2071_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1);
v___x_2072_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2071_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
v___y_2057_ = v___y_2063_;
v___y_2058_ = v___y_2065_;
v___y_2059_ = v___x_2072_;
goto v___jp_2056_;
}
else
{
v___y_2047_ = v___y_2063_;
v___y_2048_ = v___y_2065_;
v_a_2049_ = v___y_2066_;
goto v___jp_2046_;
}
}
else
{
lean_object* v_a_2073_; 
lean_dec(v___y_2066_);
v_a_2073_ = lean_ctor_get(v___x_2068_, 0);
lean_inc(v_a_2073_);
lean_dec_ref_known(v___x_2068_, 1);
v___y_2052_ = v___y_2063_;
v___y_2053_ = v___y_2065_;
v_a_2054_ = v_a_2073_;
goto v___jp_2051_;
}
}
else
{
lean_dec(v___y_2066_);
lean_dec(v_fst_2011_);
lean_dec_ref(v_allowFailure_1939_);
v___y_2052_ = v___y_2063_;
v___y_2053_ = v___y_2065_;
v_a_2054_ = v___y_2064_;
goto v___jp_2051_;
}
}
v___jp_2074_:
{
lean_object* v___x_2078_; double v___x_2079_; double v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2084_; 
v___x_2078_ = lean_io_get_num_heartbeats();
v___x_2079_ = lean_float_of_nat(v___y_2076_);
v___x_2080_ = lean_float_of_nat(v___x_2078_);
v___x_2081_ = lean_box_float(v___x_2079_);
v___x_2082_ = lean_box_float(v___x_2080_);
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 1, v___x_2082_);
lean_ctor_set(v___x_1949_, 0, v___x_2081_);
v___x_2084_ = v___x_1949_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2081_);
lean_ctor_set(v_reuseFailAlloc_2087_, 1, v___x_2082_);
v___x_2084_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2085_, 0, v_a_2077_);
lean_ctor_set(v___x_2085_, 1, v___x_2084_);
v___x_2086_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v___x_2023_, v_hasTrace_1952_, v___x_2024_, v_options_1951_, v___x_2026_, v___y_2075_, v___f_2022_, v___x_2085_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
return v___x_2086_;
}
}
v___jp_2088_:
{
lean_object* v___x_2092_; 
v___x_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2092_, 0, v_a_2091_);
v___y_2075_ = v___y_2089_;
v___y_2076_ = v___y_2090_;
v_a_2077_ = v___x_2092_;
goto v___jp_2074_;
}
v___jp_2093_:
{
lean_object* v___x_2097_; 
v___x_2097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2097_, 0, v_a_2096_);
v___y_2075_ = v___y_2094_;
v___y_2076_ = v___y_2095_;
v_a_2077_ = v___x_2097_;
goto v___jp_2074_;
}
v___jp_2098_:
{
if (lean_obj_tag(v___y_2101_) == 0)
{
lean_object* v_a_2102_; 
v_a_2102_ = lean_ctor_get(v___y_2101_, 0);
lean_inc(v_a_2102_);
lean_dec_ref_known(v___y_2101_, 1);
v___y_2089_ = v___y_2099_;
v___y_2090_ = v___y_2100_;
v_a_2091_ = v_a_2102_;
goto v___jp_2088_;
}
else
{
lean_object* v_a_2103_; 
v_a_2103_ = lean_ctor_get(v___y_2101_, 0);
lean_inc(v_a_2103_);
lean_dec_ref_known(v___y_2101_, 1);
v___y_2094_ = v___y_2099_;
v___y_2095_ = v___y_2100_;
v_a_2096_ = v_a_2103_;
goto v___jp_2093_;
}
}
v___jp_2104_:
{
if (v___y_2109_ == 0)
{
lean_object* v___x_2110_; 
lean_dec_ref(v___y_2107_);
lean_inc(v_a_1944_);
lean_inc_ref(v_a_1943_);
lean_inc(v_a_1942_);
lean_inc_ref(v_a_1941_);
v___x_2110_ = lean_apply_6(v_allowFailure_1939_, v_fst_2011_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, lean_box(0));
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v_a_2111_; uint8_t v___x_2112_; 
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
lean_inc(v_a_2111_);
lean_dec_ref_known(v___x_2110_, 1);
v___x_2112_ = lean_unbox(v_a_2111_);
lean_dec(v_a_2111_);
if (v___x_2112_ == 0)
{
lean_object* v___x_2113_; lean_object* v___x_2114_; 
lean_dec(v___y_2106_);
v___x_2113_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1);
v___x_2114_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2113_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
v___y_2099_ = v___y_2105_;
v___y_2100_ = v___y_2108_;
v___y_2101_ = v___x_2114_;
goto v___jp_2098_;
}
else
{
v___y_2089_ = v___y_2105_;
v___y_2090_ = v___y_2108_;
v_a_2091_ = v___y_2106_;
goto v___jp_2088_;
}
}
else
{
lean_object* v_a_2115_; 
lean_dec(v___y_2106_);
v_a_2115_ = lean_ctor_get(v___x_2110_, 0);
lean_inc(v_a_2115_);
lean_dec_ref_known(v___x_2110_, 1);
v___y_2094_ = v___y_2105_;
v___y_2095_ = v___y_2108_;
v_a_2096_ = v_a_2115_;
goto v___jp_2093_;
}
}
else
{
lean_dec(v___y_2106_);
lean_dec(v_fst_2011_);
lean_dec_ref(v_allowFailure_1939_);
v___y_2094_ = v___y_2105_;
v___y_2095_ = v___y_2108_;
v_a_2096_ = v___y_2107_;
goto v___jp_2093_;
}
}
v___jp_2116_:
{
lean_object* v___x_2117_; lean_object* v_a_2118_; lean_object* v___x_2119_; uint8_t v___x_2120_; 
v___x_2117_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v_a_1944_);
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_a_2118_);
lean_dec_ref(v___x_2117_);
v___x_2119_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2120_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_1951_, v___x_2119_);
if (v___x_2120_ == 0)
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v_cache_2123_; lean_object* v_zetaDeltaFVarIds_2124_; lean_object* v_postponed_2125_; lean_object* v_diag_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2146_; 
lean_del_object(v___x_1949_);
v___x_2121_ = lean_io_mono_nanos_now();
v___x_2122_ = lean_st_ref_take(v_a_1942_);
v_cache_2123_ = lean_ctor_get(v___x_2122_, 1);
v_zetaDeltaFVarIds_2124_ = lean_ctor_get(v___x_2122_, 2);
v_postponed_2125_ = lean_ctor_get(v___x_2122_, 3);
v_diag_2126_ = lean_ctor_get(v___x_2122_, 4);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2146_ == 0)
{
lean_object* v_unused_2147_; 
v_unused_2147_ = lean_ctor_get(v___x_2122_, 0);
lean_dec(v_unused_2147_);
v___x_2128_ = v___x_2122_;
v_isShared_2129_ = v_isSharedCheck_2146_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_diag_2126_);
lean_inc(v_postponed_2125_);
lean_inc(v_zetaDeltaFVarIds_2124_);
lean_inc(v_cache_2123_);
lean_dec(v___x_2122_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2146_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 0, v_snd_2012_);
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_snd_2012_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v_cache_2123_);
lean_ctor_set(v_reuseFailAlloc_2145_, 2, v_zetaDeltaFVarIds_2124_);
lean_ctor_set(v_reuseFailAlloc_2145_, 3, v_postponed_2125_);
lean_ctor_set(v_reuseFailAlloc_2145_, 4, v_diag_2126_);
v___x_2131_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
lean_object* v___x_2132_; uint8_t v___x_2133_; lean_object* v___x_2134_; 
v___x_2132_ = lean_st_ref_set(v_a_1942_, v___x_2131_);
v___x_2133_ = lean_unbox(v_snd_2017_);
lean_dec(v_snd_2017_);
v___x_2134_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_2016_, v___x_2133_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref_known(v___x_2134_, 1);
v___x_2136_ = lean_box(0);
lean_inc(v_fst_2011_);
v___x_2137_ = l_Lean_MVarId_apply(v_fst_2011_, v_a_2135_, v_cfg_1937_, v___x_2136_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2139_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc_n(v_a_2138_, 2);
lean_dec_ref_known(v___x_2137_, 1);
lean_inc(v_a_1944_);
lean_inc_ref(v_a_1943_);
lean_inc(v_a_1942_);
lean_inc_ref(v_a_1941_);
v___x_2139_ = lean_apply_6(v_act_1938_, v_a_2138_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, lean_box(0));
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; 
lean_dec(v_a_2138_);
lean_dec(v_fst_2011_);
lean_dec_ref(v_allowFailure_1939_);
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___x_2139_, 1);
v___y_2047_ = v_a_2118_;
v___y_2048_ = v___x_2121_;
v_a_2049_ = v_a_2140_;
goto v___jp_2046_;
}
else
{
lean_object* v_a_2141_; uint8_t v___x_2142_; 
v_a_2141_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2141_);
lean_dec_ref_known(v___x_2139_, 1);
v___x_2142_ = l_Lean_Exception_isInterrupt(v_a_2141_);
if (v___x_2142_ == 0)
{
uint8_t v___x_2143_; 
lean_inc(v_a_2141_);
v___x_2143_ = l_Lean_Exception_isRuntime(v_a_2141_);
v___y_2063_ = v_a_2118_;
v___y_2064_ = v_a_2141_;
v___y_2065_ = v___x_2121_;
v___y_2066_ = v_a_2138_;
v___y_2067_ = v___x_2143_;
goto v___jp_2062_;
}
else
{
v___y_2063_ = v_a_2118_;
v___y_2064_ = v_a_2141_;
v___y_2065_ = v___x_2121_;
v___y_2066_ = v_a_2138_;
v___y_2067_ = v___x_2142_;
goto v___jp_2062_;
}
}
}
else
{
lean_dec(v_fst_2011_);
lean_dec_ref(v_allowFailure_1939_);
lean_dec_ref(v_act_1938_);
v___y_2057_ = v_a_2118_;
v___y_2058_ = v___x_2121_;
v___y_2059_ = v___x_2137_;
goto v___jp_2056_;
}
}
else
{
lean_object* v_a_2144_; 
lean_dec(v_fst_2011_);
lean_dec_ref(v_allowFailure_1939_);
lean_dec_ref(v_act_1938_);
lean_dec_ref(v_cfg_1937_);
v_a_2144_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2144_);
lean_dec_ref_known(v___x_2134_, 1);
v___y_2052_ = v_a_2118_;
v___y_2053_ = v___x_2121_;
v_a_2054_ = v_a_2144_;
goto v___jp_2051_;
}
}
}
}
else
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v_cache_2150_; lean_object* v_zetaDeltaFVarIds_2151_; lean_object* v_postponed_2152_; lean_object* v_diag_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2173_; 
lean_del_object(v___x_2019_);
lean_del_object(v___x_2014_);
v___x_2148_ = lean_io_get_num_heartbeats();
v___x_2149_ = lean_st_ref_take(v_a_1942_);
v_cache_2150_ = lean_ctor_get(v___x_2149_, 1);
v_zetaDeltaFVarIds_2151_ = lean_ctor_get(v___x_2149_, 2);
v_postponed_2152_ = lean_ctor_get(v___x_2149_, 3);
v_diag_2153_ = lean_ctor_get(v___x_2149_, 4);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2173_ == 0)
{
lean_object* v_unused_2174_; 
v_unused_2174_ = lean_ctor_get(v___x_2149_, 0);
lean_dec(v_unused_2174_);
v___x_2155_ = v___x_2149_;
v_isShared_2156_ = v_isSharedCheck_2173_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_diag_2153_);
lean_inc(v_postponed_2152_);
lean_inc(v_zetaDeltaFVarIds_2151_);
lean_inc(v_cache_2150_);
lean_dec(v___x_2149_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2173_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 0, v_snd_2012_);
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_snd_2012_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_cache_2150_);
lean_ctor_set(v_reuseFailAlloc_2172_, 2, v_zetaDeltaFVarIds_2151_);
lean_ctor_set(v_reuseFailAlloc_2172_, 3, v_postponed_2152_);
lean_ctor_set(v_reuseFailAlloc_2172_, 4, v_diag_2153_);
v___x_2158_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
lean_object* v___x_2159_; uint8_t v___x_2160_; lean_object* v___x_2161_; 
v___x_2159_ = lean_st_ref_set(v_a_1942_, v___x_2158_);
v___x_2160_ = lean_unbox(v_snd_2017_);
lean_dec(v_snd_2017_);
v___x_2161_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_2016_, v___x_2160_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v_a_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v_a_2162_ = lean_ctor_get(v___x_2161_, 0);
lean_inc(v_a_2162_);
lean_dec_ref_known(v___x_2161_, 1);
v___x_2163_ = lean_box(0);
lean_inc(v_fst_2011_);
v___x_2164_ = l_Lean_MVarId_apply(v_fst_2011_, v_a_2162_, v_cfg_1937_, v___x_2163_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; lean_object* v___x_2166_; 
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
lean_inc_n(v_a_2165_, 2);
lean_dec_ref_known(v___x_2164_, 1);
lean_inc(v_a_1944_);
lean_inc_ref(v_a_1943_);
lean_inc(v_a_1942_);
lean_inc_ref(v_a_1941_);
v___x_2166_ = lean_apply_6(v_act_1938_, v_a_2165_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, lean_box(0));
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_a_2167_; 
lean_dec(v_a_2165_);
lean_dec(v_fst_2011_);
lean_dec_ref(v_allowFailure_1939_);
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_a_2167_);
lean_dec_ref_known(v___x_2166_, 1);
v___y_2089_ = v_a_2118_;
v___y_2090_ = v___x_2148_;
v_a_2091_ = v_a_2167_;
goto v___jp_2088_;
}
else
{
lean_object* v_a_2168_; uint8_t v___x_2169_; 
v_a_2168_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_a_2168_);
lean_dec_ref_known(v___x_2166_, 1);
v___x_2169_ = l_Lean_Exception_isInterrupt(v_a_2168_);
if (v___x_2169_ == 0)
{
uint8_t v___x_2170_; 
lean_inc(v_a_2168_);
v___x_2170_ = l_Lean_Exception_isRuntime(v_a_2168_);
v___y_2105_ = v_a_2118_;
v___y_2106_ = v_a_2165_;
v___y_2107_ = v_a_2168_;
v___y_2108_ = v___x_2148_;
v___y_2109_ = v___x_2170_;
goto v___jp_2104_;
}
else
{
v___y_2105_ = v_a_2118_;
v___y_2106_ = v_a_2165_;
v___y_2107_ = v_a_2168_;
v___y_2108_ = v___x_2148_;
v___y_2109_ = v___x_2169_;
goto v___jp_2104_;
}
}
}
else
{
lean_dec(v_fst_2011_);
lean_dec_ref(v_allowFailure_1939_);
lean_dec_ref(v_act_1938_);
v___y_2099_ = v_a_2118_;
v___y_2100_ = v___x_2148_;
v___y_2101_ = v___x_2164_;
goto v___jp_2098_;
}
}
else
{
lean_object* v_a_2171_; 
lean_dec(v_fst_2011_);
lean_dec_ref(v_allowFailure_1939_);
lean_dec_ref(v_act_1938_);
lean_dec_ref(v_cfg_1937_);
v_a_2171_ = lean_ctor_get(v___x_2161_, 0);
lean_inc(v_a_2171_);
lean_dec_ref_known(v___x_2161_, 1);
v___y_2094_ = v_a_2118_;
v___y_2095_ = v___x_2148_;
v_a_2096_ = v_a_2171_;
goto v___jp_2093_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___boxed(lean_object* v_cfg_2234_, lean_object* v_act_2235_, lean_object* v_allowFailure_2236_, lean_object* v_cand_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(v_cfg_2234_, v_act_2235_, v_allowFailure_2236_, v_cand_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_);
lean_dec(v_a_2241_);
lean_dec_ref(v_a_2240_);
lean_dec(v_a_2239_);
lean_dec_ref(v_a_2238_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3(lean_object* v_00_u03b1_2244_, lean_object* v_x_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_){
_start:
{
lean_object* v___x_2251_; 
v___x_2251_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_x_2245_);
return v___x_2251_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2252_, lean_object* v_x_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3(v_00_u03b1_2252_, v_x_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(lean_object* v_act_2262_, lean_object* v_a_2263_, uint8_t v_collectAll_2264_, lean_object* v_as_2265_, size_t v_sz_2266_, size_t v_i_2267_, lean_object* v_b_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v_a_2275_; uint8_t v___x_2279_; 
v___x_2279_ = lean_usize_dec_lt(v_i_2267_, v_sz_2266_);
if (v___x_2279_ == 0)
{
lean_object* v___x_2280_; 
lean_dec_ref(v_act_2262_);
v___x_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2280_, 0, v_b_2268_);
return v___x_2280_;
}
else
{
lean_object* v_snd_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2354_; 
v_snd_2281_ = lean_ctor_get(v_b_2268_, 1);
v_isSharedCheck_2354_ = !lean_is_exclusive(v_b_2268_);
if (v_isSharedCheck_2354_ == 0)
{
lean_object* v_unused_2355_; 
v_unused_2355_ = lean_ctor_get(v_b_2268_, 0);
lean_dec(v_unused_2355_);
v___x_2283_ = v_b_2268_;
v_isShared_2284_ = v_isSharedCheck_2354_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_snd_2281_);
lean_dec(v_b_2268_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2354_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2285_; lean_object* v_a_2286_; lean_object* v___x_2287_; 
v___x_2285_ = lean_box(0);
v_a_2286_ = lean_array_uget_borrowed(v_as_2265_, v_i_2267_);
lean_inc_ref(v_act_2262_);
lean_inc(v___y_2272_);
lean_inc_ref(v___y_2271_);
lean_inc(v___y_2270_);
lean_inc_ref(v___y_2269_);
lean_inc(v_a_2286_);
v___x_2287_ = lean_apply_6(v_act_2262_, v_a_2286_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, lean_box(0));
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2317_; 
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2290_ = v___x_2287_;
v_isShared_2291_ = v_isSharedCheck_2317_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2287_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2317_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
uint8_t v___y_2310_; uint8_t v___x_2316_; 
v___x_2316_ = l_List_isEmpty___redArg(v_a_2288_);
if (v___x_2316_ == 0)
{
v___y_2310_ = v___x_2316_;
goto v___jp_2309_;
}
else
{
if (v_collectAll_2264_ == 0)
{
v___y_2310_ = v___x_2316_;
goto v___jp_2309_;
}
else
{
lean_del_object(v___x_2290_);
goto v___jp_2292_;
}
}
v___jp_2292_:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2293_ = lean_st_ref_get(v___y_2270_);
v___x_2294_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2263_, v___y_2270_, v___y_2272_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_mctx_2295_; lean_object* v___x_2297_; 
lean_dec_ref_known(v___x_2294_, 1);
v_mctx_2295_ = lean_ctor_get(v___x_2293_, 0);
lean_inc_ref(v_mctx_2295_);
lean_dec(v___x_2293_);
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 1, v_mctx_2295_);
lean_ctor_set(v___x_2283_, 0, v_a_2288_);
v___x_2297_ = v___x_2283_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2288_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v_mctx_2295_);
v___x_2297_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2298_ = lean_array_push(v_snd_2281_, v___x_2297_);
v___x_2299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2285_);
lean_ctor_set(v___x_2299_, 1, v___x_2298_);
v_a_2275_ = v___x_2299_;
goto v___jp_2274_;
}
}
else
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2308_; 
lean_dec(v___x_2293_);
lean_dec(v_a_2288_);
lean_del_object(v___x_2283_);
lean_dec(v_snd_2281_);
lean_dec_ref(v_act_2262_);
v_a_2301_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2303_ = v___x_2294_;
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2294_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2306_; 
if (v_isShared_2304_ == 0)
{
v___x_2306_ = v___x_2303_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_a_2301_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
}
v___jp_2309_:
{
if (v___y_2310_ == 0)
{
lean_del_object(v___x_2290_);
goto v___jp_2292_;
}
else
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2314_; 
lean_dec(v_a_2288_);
lean_del_object(v___x_2283_);
lean_dec_ref(v_act_2262_);
v___x_2311_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0___closed__0));
v___x_2312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2311_);
lean_ctor_set(v___x_2312_, 1, v_snd_2281_);
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 0, v___x_2312_);
v___x_2314_ = v___x_2290_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v___x_2312_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2353_; 
v_a_2318_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2320_ = v___x_2287_;
v_isShared_2321_ = v_isSharedCheck_2353_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2287_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2353_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
uint8_t v___y_2323_; uint8_t v___x_2351_; 
v___x_2351_ = l_Lean_Exception_isInterrupt(v_a_2318_);
if (v___x_2351_ == 0)
{
uint8_t v___x_2352_; 
lean_inc(v_a_2318_);
v___x_2352_ = l_Lean_Exception_isRuntime(v_a_2318_);
v___y_2323_ = v___x_2352_;
goto v___jp_2322_;
}
else
{
v___y_2323_ = v___x_2351_;
goto v___jp_2322_;
}
v___jp_2322_:
{
if (v___y_2323_ == 0)
{
lean_object* v___x_2324_; 
lean_del_object(v___x_2320_);
v___x_2324_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2263_, v___y_2270_, v___y_2272_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2338_; 
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2338_ == 0)
{
lean_object* v_unused_2339_; 
v_unused_2339_ = lean_ctor_get(v___x_2324_, 0);
lean_dec(v_unused_2339_);
v___x_2326_ = v___x_2324_;
v_isShared_2327_ = v_isSharedCheck_2338_;
goto v_resetjp_2325_;
}
else
{
lean_dec(v___x_2324_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2338_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
uint8_t v___x_2328_; 
v___x_2328_ = l_Lean_Meta_LibrarySearch_isAbortSpeculation(v_a_2318_);
lean_dec(v_a_2318_);
if (v___x_2328_ == 0)
{
lean_object* v___x_2330_; 
lean_del_object(v___x_2326_);
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 0, v___x_2285_);
v___x_2330_ = v___x_2283_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v___x_2285_);
lean_ctor_set(v_reuseFailAlloc_2331_, 1, v_snd_2281_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
v_a_2275_ = v___x_2330_;
goto v___jp_2274_;
}
}
else
{
lean_object* v___x_2333_; 
lean_dec_ref(v_act_2262_);
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 0, v___x_2285_);
v___x_2333_ = v___x_2283_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v___x_2285_);
lean_ctor_set(v_reuseFailAlloc_2337_, 1, v_snd_2281_);
v___x_2333_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
lean_object* v___x_2335_; 
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 0, v___x_2333_);
v___x_2335_ = v___x_2326_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2333_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
}
}
else
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
lean_dec(v_a_2318_);
lean_del_object(v___x_2283_);
lean_dec(v_snd_2281_);
lean_dec_ref(v_act_2262_);
v_a_2340_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2324_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2324_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
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
else
{
lean_object* v___x_2349_; 
lean_del_object(v___x_2283_);
lean_dec(v_snd_2281_);
lean_dec_ref(v_act_2262_);
if (v_isShared_2321_ == 0)
{
v___x_2349_ = v___x_2320_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2318_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
}
}
}
v___jp_2274_:
{
size_t v___x_2276_; size_t v___x_2277_; 
v___x_2276_ = ((size_t)1ULL);
v___x_2277_ = lean_usize_add(v_i_2267_, v___x_2276_);
v_i_2267_ = v___x_2277_;
v_b_2268_ = v_a_2275_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0___boxed(lean_object* v_act_2356_, lean_object* v_a_2357_, lean_object* v_collectAll_2358_, lean_object* v_as_2359_, lean_object* v_sz_2360_, lean_object* v_i_2361_, lean_object* v_b_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_){
_start:
{
uint8_t v_collectAll_boxed_2368_; size_t v_sz_boxed_2369_; size_t v_i_boxed_2370_; lean_object* v_res_2371_; 
v_collectAll_boxed_2368_ = lean_unbox(v_collectAll_2358_);
v_sz_boxed_2369_ = lean_unbox_usize(v_sz_2360_);
lean_dec(v_sz_2360_);
v_i_boxed_2370_ = lean_unbox_usize(v_i_2361_);
lean_dec(v_i_2361_);
v_res_2371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(v_act_2356_, v_a_2357_, v_collectAll_boxed_2368_, v_as_2359_, v_sz_boxed_2369_, v_i_boxed_2370_, v_b_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec_ref(v_as_2359_);
lean_dec_ref(v_a_2357_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryOnEach(lean_object* v_act_2377_, lean_object* v_candidates_2378_, uint8_t v_collectAll_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_){
_start:
{
lean_object* v___x_2385_; 
v___x_2385_ = l_Lean_Meta_saveState___redArg(v_a_2381_, v_a_2383_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v_a_2386_; lean_object* v___x_2387_; size_t v_sz_2388_; size_t v___x_2389_; lean_object* v___x_2390_; 
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
lean_inc(v_a_2386_);
lean_dec_ref_known(v___x_2385_, 1);
v___x_2387_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryOnEach___closed__1));
v_sz_2388_ = lean_array_size(v_candidates_2378_);
v___x_2389_ = ((size_t)0ULL);
v___x_2390_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(v_act_2377_, v_a_2386_, v_collectAll_2379_, v_candidates_2378_, v_sz_2388_, v___x_2389_, v___x_2387_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_);
lean_dec(v_a_2386_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2405_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2393_ = v___x_2390_;
v_isShared_2394_ = v_isSharedCheck_2405_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2390_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2405_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v_fst_2395_; 
v_fst_2395_ = lean_ctor_get(v_a_2391_, 0);
if (lean_obj_tag(v_fst_2395_) == 0)
{
lean_object* v_snd_2396_; lean_object* v___x_2397_; lean_object* v___x_2399_; 
v_snd_2396_ = lean_ctor_get(v_a_2391_, 1);
lean_inc(v_snd_2396_);
lean_dec(v_a_2391_);
v___x_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2397_, 0, v_snd_2396_);
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 0, v___x_2397_);
v___x_2399_ = v___x_2393_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v___x_2397_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
else
{
lean_object* v_val_2401_; lean_object* v___x_2403_; 
lean_inc_ref(v_fst_2395_);
lean_dec(v_a_2391_);
v_val_2401_ = lean_ctor_get(v_fst_2395_, 0);
lean_inc(v_val_2401_);
lean_dec_ref_known(v_fst_2395_, 1);
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 0, v_val_2401_);
v___x_2403_ = v___x_2393_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_val_2401_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
else
{
lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2413_; 
v_a_2406_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2408_ = v___x_2390_;
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_dec(v___x_2390_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2411_; 
if (v_isShared_2409_ == 0)
{
v___x_2411_ = v___x_2408_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_a_2406_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
else
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2421_; 
lean_dec_ref(v_act_2377_);
v_a_2414_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2416_ = v___x_2385_;
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2385_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2419_; 
if (v_isShared_2417_ == 0)
{
v___x_2419_ = v___x_2416_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_a_2414_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryOnEach___boxed(lean_object* v_act_2422_, lean_object* v_candidates_2423_, lean_object* v_collectAll_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_){
_start:
{
uint8_t v_collectAll_boxed_2430_; lean_object* v_res_2431_; 
v_collectAll_boxed_2430_ = lean_unbox(v_collectAll_2424_);
v_res_2431_ = l_Lean_Meta_LibrarySearch_tryOnEach(v_act_2422_, v_candidates_2423_, v_collectAll_boxed_2430_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
lean_dec(v_a_2428_);
lean_dec_ref(v_a_2427_);
lean_dec(v_a_2426_);
lean_dec_ref(v_a_2425_);
lean_dec_ref(v_candidates_2423_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg(){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2433_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0, &l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0_once, _init_l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0);
v___x_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2433_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg___boxed(lean_object* v___y_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg();
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0(lean_object* v_00_u03b1_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v___x_2443_; 
v___x_2443_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg();
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___boxed(lean_object* v_00_u03b1_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0(v_00_u03b1_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(lean_object* v_category_2451_, lean_object* v_opts_2452_, lean_object* v_act_2453_, lean_object* v_decl_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; 
lean_inc(v___y_2458_);
lean_inc_ref(v___y_2457_);
lean_inc(v___y_2456_);
lean_inc_ref(v___y_2455_);
v___x_2460_ = lean_apply_4(v_act_2453_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
v___x_2461_ = l_Lean_profileitIOUnsafe___redArg(v_category_2451_, v_opts_2452_, v___x_2460_, v_decl_2454_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg___boxed(lean_object* v_category_2462_, lean_object* v_opts_2463_, lean_object* v_act_2464_, lean_object* v_decl_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_){
_start:
{
lean_object* v_res_2471_; 
v_res_2471_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v_category_2462_, v_opts_2463_, v_act_2464_, v_decl_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
lean_dec(v___y_2469_);
lean_dec_ref(v___y_2468_);
lean_dec(v___y_2467_);
lean_dec_ref(v___y_2466_);
lean_dec_ref(v_opts_2463_);
lean_dec_ref(v_category_2462_);
return v_res_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3(lean_object* v_00_u03b1_2472_, lean_object* v_category_2473_, lean_object* v_opts_2474_, lean_object* v_act_2475_, lean_object* v_decl_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
lean_object* v___x_2482_; 
v___x_2482_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v_category_2473_, v_opts_2474_, v_act_2475_, v_decl_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___boxed(lean_object* v_00_u03b1_2483_, lean_object* v_category_2484_, lean_object* v_opts_2485_, lean_object* v_act_2486_, lean_object* v_decl_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3(v_00_u03b1_2483_, v_category_2484_, v_opts_2485_, v_act_2486_, v_decl_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec_ref(v_opts_2485_);
lean_dec_ref(v_category_2484_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0(lean_object* v_a_2494_, lean_object* v___x_2495_, lean_object* v_tactic_2496_, lean_object* v_allowFailure_2497_, lean_object* v_cand_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v___x_2504_; 
lean_inc(v___y_2502_);
lean_inc_ref(v___y_2501_);
lean_inc(v___y_2500_);
lean_inc_ref(v___y_2499_);
v___x_2504_ = lean_apply_5(v_a_2494_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, lean_box(0));
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v_a_2505_; uint8_t v___x_2506_; 
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_a_2505_);
lean_dec_ref_known(v___x_2504_, 1);
v___x_2506_ = lean_unbox(v_a_2505_);
lean_dec(v_a_2505_);
if (v___x_2506_ == 0)
{
lean_object* v___x_2507_; 
v___x_2507_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(v___x_2495_, v_tactic_2496_, v_allowFailure_2497_, v_cand_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_);
return v___x_2507_;
}
else
{
lean_object* v___x_2508_; lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2516_; 
lean_dec_ref(v_cand_2498_);
lean_dec_ref(v_allowFailure_2497_);
lean_dec_ref(v_tactic_2496_);
lean_dec_ref(v___x_2495_);
v___x_2508_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg();
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2511_ = v___x_2508_;
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2508_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2514_; 
if (v_isShared_2512_ == 0)
{
v___x_2514_ = v___x_2511_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_a_2509_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
}
else
{
lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2524_; 
lean_dec_ref(v_cand_2498_);
lean_dec_ref(v_allowFailure_2497_);
lean_dec_ref(v_tactic_2496_);
lean_dec_ref(v___x_2495_);
v_a_2517_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2519_ = v___x_2504_;
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v___x_2504_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2522_; 
if (v_isShared_2520_ == 0)
{
v___x_2522_ = v___x_2519_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_a_2517_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed(lean_object* v_a_2525_, lean_object* v___x_2526_, lean_object* v_tactic_2527_, lean_object* v_allowFailure_2528_, lean_object* v_cand_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v_res_2535_; 
v_res_2535_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0(v_a_2525_, v___x_2526_, v_tactic_2527_, v_allowFailure_2528_, v_cand_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
return v_res_2535_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(lean_object* v_as_2536_, size_t v_i_2537_, size_t v_stop_2538_){
_start:
{
uint8_t v___x_2539_; 
v___x_2539_ = lean_usize_dec_eq(v_i_2537_, v_stop_2538_);
if (v___x_2539_ == 0)
{
lean_object* v___x_2540_; lean_object* v_fst_2541_; uint8_t v___x_2542_; 
v___x_2540_ = lean_array_uget_borrowed(v_as_2536_, v_i_2537_);
v_fst_2541_ = lean_ctor_get(v___x_2540_, 0);
v___x_2542_ = l_List_isEmpty___redArg(v_fst_2541_);
if (v___x_2542_ == 0)
{
size_t v___x_2543_; size_t v___x_2544_; 
v___x_2543_ = ((size_t)1ULL);
v___x_2544_ = lean_usize_add(v_i_2537_, v___x_2543_);
v_i_2537_ = v___x_2544_;
goto _start;
}
else
{
return v___x_2542_;
}
}
else
{
uint8_t v___x_2546_; 
v___x_2546_ = 0;
return v___x_2546_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2___boxed(lean_object* v_as_2547_, lean_object* v_i_2548_, lean_object* v_stop_2549_){
_start:
{
size_t v_i_boxed_2550_; size_t v_stop_boxed_2551_; uint8_t v_res_2552_; lean_object* v_r_2553_; 
v_i_boxed_2550_ = lean_unbox_usize(v_i_2548_);
lean_dec(v_i_2548_);
v_stop_boxed_2551_ = lean_unbox_usize(v_stop_2549_);
lean_dec(v_stop_2549_);
v_res_2552_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_as_2547_, v_i_boxed_2550_, v_stop_boxed_2551_);
lean_dec_ref(v_as_2547_);
v_r_2553_ = lean_box(v_res_2552_);
return v_r_2553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(lean_object* v_goal_2554_, lean_object* v___x_2555_, size_t v_sz_2556_, size_t v_i_2557_, lean_object* v_bs_2558_){
_start:
{
uint8_t v___x_2559_; 
v___x_2559_ = lean_usize_dec_lt(v_i_2557_, v_sz_2556_);
if (v___x_2559_ == 0)
{
lean_dec_ref(v___x_2555_);
lean_dec(v_goal_2554_);
return v_bs_2558_;
}
else
{
lean_object* v_v_2560_; lean_object* v___x_2561_; lean_object* v_bs_x27_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; size_t v___x_2565_; size_t v___x_2566_; lean_object* v___x_2567_; 
v_v_2560_ = lean_array_uget(v_bs_2558_, v_i_2557_);
v___x_2561_ = lean_unsigned_to_nat(0u);
v_bs_x27_2562_ = lean_array_uset(v_bs_2558_, v_i_2557_, v___x_2561_);
lean_inc_ref(v___x_2555_);
lean_inc(v_goal_2554_);
v___x_2563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2563_, 0, v_goal_2554_);
lean_ctor_set(v___x_2563_, 1, v___x_2555_);
v___x_2564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2563_);
lean_ctor_set(v___x_2564_, 1, v_v_2560_);
v___x_2565_ = ((size_t)1ULL);
v___x_2566_ = lean_usize_add(v_i_2557_, v___x_2565_);
v___x_2567_ = lean_array_uset(v_bs_x27_2562_, v_i_2557_, v___x_2564_);
v_i_2557_ = v___x_2566_;
v_bs_2558_ = v___x_2567_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1___boxed(lean_object* v_goal_2569_, lean_object* v___x_2570_, lean_object* v_sz_2571_, lean_object* v_i_2572_, lean_object* v_bs_2573_){
_start:
{
size_t v_sz_boxed_2574_; size_t v_i_boxed_2575_; lean_object* v_res_2576_; 
v_sz_boxed_2574_ = lean_unbox_usize(v_sz_2571_);
lean_dec(v_sz_2571_);
v_i_boxed_2575_ = lean_unbox_usize(v_i_2572_);
lean_dec(v_i_2572_);
v_res_2576_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2569_, v___x_2570_, v_sz_boxed_2574_, v_i_boxed_2575_, v_bs_2573_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1(lean_object* v_leavePercentHeartbeats_2578_, lean_object* v_goal_2579_, lean_object* v___x_2580_, lean_object* v_tactic_2581_, lean_object* v_allowFailure_2582_, uint8_t v_collectAll_2583_, uint8_t v_includeStar_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_){
_start:
{
lean_object* v___x_2593_; 
v___x_2593_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercentHeartbeats_2578_, v___y_2587_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2594_);
lean_dec_ref_known(v___x_2593_, 1);
v___x_2595_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___closed__0));
lean_inc(v_goal_2579_);
v___x_2596_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v___x_2595_, v_goal_2579_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v_a_2597_; lean_object* v___f_2598_; lean_object* v___x_2599_; 
v_a_2597_ = lean_ctor_get(v___x_2596_, 0);
lean_inc(v_a_2597_);
lean_dec_ref_known(v___x_2596_, 1);
v___f_2598_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2598_, 0, v_a_2594_);
lean_closure_set(v___f_2598_, 1, v___x_2580_);
lean_closure_set(v___f_2598_, 2, v_tactic_2581_);
lean_closure_set(v___f_2598_, 3, v_allowFailure_2582_);
lean_inc_ref(v___f_2598_);
v___x_2599_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2598_, v_a_2597_, v_collectAll_2583_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
lean_dec(v_a_2597_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v_a_2600_; 
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
lean_inc(v_a_2600_);
if (lean_obj_tag(v_a_2600_) == 0)
{
lean_dec_ref_known(v___x_2599_, 1);
lean_dec_ref(v___f_2598_);
lean_dec(v_goal_2579_);
goto v___jp_2590_;
}
else
{
lean_object* v_val_2601_; lean_object* v___x_2650_; lean_object* v___x_2651_; uint8_t v___x_2652_; 
v_val_2601_ = lean_ctor_get(v_a_2600_, 0);
v___x_2650_ = lean_unsigned_to_nat(0u);
v___x_2651_ = lean_array_get_size(v_val_2601_);
v___x_2652_ = lean_nat_dec_lt(v___x_2650_, v___x_2651_);
if (v___x_2652_ == 0)
{
goto v___jp_2646_;
}
else
{
if (v___x_2652_ == 0)
{
goto v___jp_2646_;
}
else
{
size_t v___x_2653_; size_t v___x_2654_; uint8_t v___x_2655_; 
v___x_2653_ = ((size_t)0ULL);
v___x_2654_ = lean_usize_of_nat(v___x_2651_);
v___x_2655_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_val_2601_, v___x_2653_, v___x_2654_);
if (v___x_2655_ == 0)
{
goto v___jp_2646_;
}
else
{
lean_dec_ref_known(v_a_2600_, 1);
lean_dec_ref(v___f_2598_);
lean_dec(v_goal_2579_);
return v___x_2599_;
}
}
}
v___jp_2602_:
{
if (v_includeStar_2584_ == 0)
{
lean_dec_ref_known(v_a_2600_, 1);
lean_dec_ref(v___f_2598_);
lean_dec(v_goal_2579_);
return v___x_2599_;
}
else
{
lean_object* v___x_2603_; 
lean_dec_ref_known(v___x_2599_, 1);
v___x_2603_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2637_; 
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2606_ = v___x_2603_;
v_isShared_2607_ = v_isSharedCheck_2637_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2603_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2637_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; uint8_t v___x_2610_; 
v___x_2608_ = lean_array_get_size(v_a_2604_);
v___x_2609_ = lean_unsigned_to_nat(0u);
v___x_2610_ = lean_nat_dec_eq(v___x_2608_, v___x_2609_);
if (v___x_2610_ == 0)
{
lean_object* v___x_2611_; lean_object* v_mctx_2612_; size_t v_sz_2613_; size_t v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
lean_inc(v_val_2601_);
lean_del_object(v___x_2606_);
lean_dec_ref_known(v_a_2600_, 1);
v___x_2611_ = lean_st_ref_get(v___y_2586_);
v_mctx_2612_ = lean_ctor_get(v___x_2611_, 0);
lean_inc_ref(v_mctx_2612_);
lean_dec(v___x_2611_);
v_sz_2613_ = lean_array_size(v_a_2604_);
v___x_2614_ = ((size_t)0ULL);
v___x_2615_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2579_, v_mctx_2612_, v_sz_2613_, v___x_2614_, v_a_2604_);
v___x_2616_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2598_, v___x_2615_, v_collectAll_2583_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
lean_dec_ref(v___x_2615_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2633_; 
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2619_ = v___x_2616_;
v_isShared_2620_ = v_isSharedCheck_2633_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2616_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2633_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
if (lean_obj_tag(v_a_2617_) == 0)
{
lean_del_object(v___x_2619_);
lean_dec(v_val_2601_);
goto v___jp_2590_;
}
else
{
lean_object* v_val_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2632_; 
v_val_2621_ = lean_ctor_get(v_a_2617_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v_a_2617_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2623_ = v_a_2617_;
v_isShared_2624_ = v_isSharedCheck_2632_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_val_2621_);
lean_dec(v_a_2617_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2632_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2625_; lean_object* v___x_2627_; 
v___x_2625_ = l_Array_append___redArg(v_val_2601_, v_val_2621_);
lean_dec(v_val_2621_);
if (v_isShared_2624_ == 0)
{
lean_ctor_set(v___x_2623_, 0, v___x_2625_);
v___x_2627_ = v___x_2623_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v___x_2625_);
v___x_2627_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
lean_object* v___x_2629_; 
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 0, v___x_2627_);
v___x_2629_ = v___x_2619_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v___x_2627_);
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
}
}
else
{
lean_dec(v_val_2601_);
return v___x_2616_;
}
}
else
{
lean_object* v___x_2635_; 
lean_dec(v_a_2604_);
lean_dec_ref(v___f_2598_);
lean_dec(v_goal_2579_);
if (v_isShared_2607_ == 0)
{
lean_ctor_set(v___x_2606_, 0, v_a_2600_);
v___x_2635_ = v___x_2606_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_a_2600_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
else
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2645_; 
lean_dec_ref_known(v_a_2600_, 1);
lean_dec_ref(v___f_2598_);
lean_dec(v_goal_2579_);
v_a_2638_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2640_ = v___x_2603_;
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2603_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2643_; 
if (v_isShared_2641_ == 0)
{
v___x_2643_ = v___x_2640_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2638_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
}
}
v___jp_2646_:
{
if (v_collectAll_2583_ == 0)
{
lean_object* v___x_2647_; lean_object* v___x_2648_; uint8_t v___x_2649_; 
v___x_2647_ = lean_array_get_size(v_val_2601_);
v___x_2648_ = lean_unsigned_to_nat(0u);
v___x_2649_ = lean_nat_dec_eq(v___x_2647_, v___x_2648_);
if (v___x_2649_ == 0)
{
lean_dec_ref_known(v_a_2600_, 1);
lean_dec_ref(v___f_2598_);
lean_dec(v_goal_2579_);
return v___x_2599_;
}
else
{
goto v___jp_2602_;
}
}
else
{
goto v___jp_2602_;
}
}
}
}
else
{
lean_dec_ref(v___f_2598_);
lean_dec(v_goal_2579_);
return v___x_2599_;
}
}
else
{
lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2663_; 
lean_dec(v_a_2594_);
lean_dec_ref(v_allowFailure_2582_);
lean_dec_ref(v_tactic_2581_);
lean_dec_ref(v___x_2580_);
lean_dec(v_goal_2579_);
v_a_2656_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2658_ = v___x_2596_;
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2596_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2661_; 
if (v_isShared_2659_ == 0)
{
v___x_2661_ = v___x_2658_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_a_2656_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
}
else
{
lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2671_; 
lean_dec_ref(v_allowFailure_2582_);
lean_dec_ref(v_tactic_2581_);
lean_dec_ref(v___x_2580_);
lean_dec(v_goal_2579_);
v_a_2664_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2666_ = v___x_2593_;
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_dec(v___x_2593_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2669_; 
if (v_isShared_2667_ == 0)
{
v___x_2669_ = v___x_2666_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_a_2664_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
v___jp_2590_:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2591_ = lean_box(0);
v___x_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2591_);
return v___x_2592_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed(lean_object* v_leavePercentHeartbeats_2672_, lean_object* v_goal_2673_, lean_object* v___x_2674_, lean_object* v_tactic_2675_, lean_object* v_allowFailure_2676_, lean_object* v_collectAll_2677_, lean_object* v_includeStar_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
uint8_t v_collectAll_boxed_2684_; uint8_t v_includeStar_boxed_2685_; lean_object* v_res_2686_; 
v_collectAll_boxed_2684_ = lean_unbox(v_collectAll_2677_);
v_includeStar_boxed_2685_ = lean_unbox(v_includeStar_2678_);
v_res_2686_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1(v_leavePercentHeartbeats_2672_, v_goal_2673_, v___x_2674_, v_tactic_2675_, v_allowFailure_2676_, v_collectAll_boxed_2684_, v_includeStar_boxed_2685_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec(v_leavePercentHeartbeats_2672_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2(lean_object* v_goal_2687_, lean_object* v_x_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_){
_start:
{
lean_object* v___x_2694_; 
v___x_2694_ = l_Lean_MVarId_getType(v_goal_2687_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2703_; 
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2697_ = v___x_2694_;
v_isShared_2698_ = v_isSharedCheck_2703_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2694_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2703_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2699_; lean_object* v___x_2701_; 
v___x_2699_ = l_Lean_MessageData_ofExpr(v_a_2695_);
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 0, v___x_2699_);
v___x_2701_ = v___x_2697_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2699_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
v_a_2704_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2694_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2694_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2___boxed(lean_object* v_goal_2712_, lean_object* v_x_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2(v_goal_2712_, v_x_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec_ref(v_x_2713_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4(lean_object* v_leavePercentHeartbeats_2720_, lean_object* v_goal_2721_, lean_object* v___x_2722_, lean_object* v_tactic_2723_, lean_object* v_allowFailure_2724_, uint8_t v_collectAll_2725_, uint8_t v_includeStar_2726_, uint8_t v___x_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
lean_object* v___x_2736_; 
v___x_2736_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercentHeartbeats_2720_, v___y_2730_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; 
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_a_2737_);
lean_dec_ref_known(v___x_2736_, 1);
v___x_2738_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___closed__0));
lean_inc(v_goal_2721_);
v___x_2739_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v___x_2738_, v_goal_2721_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v_a_2740_; lean_object* v___f_2741_; lean_object* v___x_2742_; 
v_a_2740_ = lean_ctor_get(v___x_2739_, 0);
lean_inc(v_a_2740_);
lean_dec_ref_known(v___x_2739_, 1);
v___f_2741_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2741_, 0, v_a_2737_);
lean_closure_set(v___f_2741_, 1, v___x_2722_);
lean_closure_set(v___f_2741_, 2, v_tactic_2723_);
lean_closure_set(v___f_2741_, 3, v_allowFailure_2724_);
lean_inc_ref(v___f_2741_);
v___x_2742_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2741_, v_a_2740_, v_collectAll_2725_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
lean_dec(v_a_2740_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
lean_inc(v_a_2743_);
if (lean_obj_tag(v_a_2743_) == 0)
{
lean_dec_ref_known(v___x_2742_, 1);
lean_dec_ref(v___f_2741_);
lean_dec(v_goal_2721_);
goto v___jp_2733_;
}
else
{
lean_object* v_val_2744_; uint8_t v___y_2790_; lean_object* v___x_2794_; lean_object* v___x_2795_; uint8_t v___x_2796_; 
v_val_2744_ = lean_ctor_get(v_a_2743_, 0);
v___x_2794_ = lean_unsigned_to_nat(0u);
v___x_2795_ = lean_array_get_size(v_val_2744_);
v___x_2796_ = lean_nat_dec_lt(v___x_2794_, v___x_2795_);
if (v___x_2796_ == 0)
{
v___y_2790_ = v___x_2727_;
goto v___jp_2789_;
}
else
{
if (v___x_2796_ == 0)
{
v___y_2790_ = v___x_2727_;
goto v___jp_2789_;
}
else
{
size_t v___x_2797_; size_t v___x_2798_; uint8_t v___x_2799_; 
v___x_2797_ = ((size_t)0ULL);
v___x_2798_ = lean_usize_of_nat(v___x_2795_);
v___x_2799_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_val_2744_, v___x_2797_, v___x_2798_);
v___y_2790_ = v___x_2799_;
goto v___jp_2789_;
}
}
v___jp_2745_:
{
if (v_includeStar_2726_ == 0)
{
lean_dec_ref_known(v_a_2743_, 1);
lean_dec_ref(v___f_2741_);
lean_dec(v_goal_2721_);
return v___x_2742_;
}
else
{
lean_object* v___x_2746_; 
lean_dec_ref_known(v___x_2742_, 1);
v___x_2746_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2780_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2749_ = v___x_2746_;
v_isShared_2750_ = v_isSharedCheck_2780_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2746_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2780_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; uint8_t v___x_2753_; 
v___x_2751_ = lean_array_get_size(v_a_2747_);
v___x_2752_ = lean_unsigned_to_nat(0u);
v___x_2753_ = lean_nat_dec_eq(v___x_2751_, v___x_2752_);
if (v___x_2753_ == 0)
{
lean_object* v___x_2754_; lean_object* v_mctx_2755_; size_t v_sz_2756_; size_t v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
lean_inc(v_val_2744_);
lean_del_object(v___x_2749_);
lean_dec_ref_known(v_a_2743_, 1);
v___x_2754_ = lean_st_ref_get(v___y_2729_);
v_mctx_2755_ = lean_ctor_get(v___x_2754_, 0);
lean_inc_ref(v_mctx_2755_);
lean_dec(v___x_2754_);
v_sz_2756_ = lean_array_size(v_a_2747_);
v___x_2757_ = ((size_t)0ULL);
v___x_2758_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2721_, v_mctx_2755_, v_sz_2756_, v___x_2757_, v_a_2747_);
v___x_2759_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2741_, v___x_2758_, v_collectAll_2725_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
lean_dec_ref(v___x_2758_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2776_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2762_ = v___x_2759_;
v_isShared_2763_ = v_isSharedCheck_2776_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2759_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2776_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
if (lean_obj_tag(v_a_2760_) == 0)
{
lean_del_object(v___x_2762_);
lean_dec(v_val_2744_);
goto v___jp_2733_;
}
else
{
lean_object* v_val_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2775_; 
v_val_2764_ = lean_ctor_get(v_a_2760_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v_a_2760_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2766_ = v_a_2760_;
v_isShared_2767_ = v_isSharedCheck_2775_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_val_2764_);
lean_dec(v_a_2760_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2775_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2768_; lean_object* v___x_2770_; 
v___x_2768_ = l_Array_append___redArg(v_val_2744_, v_val_2764_);
lean_dec(v_val_2764_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 0, v___x_2768_);
v___x_2770_ = v___x_2766_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v___x_2768_);
v___x_2770_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
lean_object* v___x_2772_; 
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 0, v___x_2770_);
v___x_2772_ = v___x_2762_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v___x_2770_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
}
}
else
{
lean_dec(v_val_2744_);
return v___x_2759_;
}
}
else
{
lean_object* v___x_2778_; 
lean_dec(v_a_2747_);
lean_dec_ref(v___f_2741_);
lean_dec(v_goal_2721_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 0, v_a_2743_);
v___x_2778_ = v___x_2749_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_a_2743_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
}
else
{
lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2788_; 
lean_dec_ref_known(v_a_2743_, 1);
lean_dec_ref(v___f_2741_);
lean_dec(v_goal_2721_);
v_a_2781_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2783_ = v___x_2746_;
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2746_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2786_; 
if (v_isShared_2784_ == 0)
{
v___x_2786_ = v___x_2783_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_a_2781_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
}
}
v___jp_2789_:
{
if (v___y_2790_ == 0)
{
if (v_collectAll_2725_ == 0)
{
lean_object* v___x_2791_; lean_object* v___x_2792_; uint8_t v___x_2793_; 
v___x_2791_ = lean_array_get_size(v_val_2744_);
v___x_2792_ = lean_unsigned_to_nat(0u);
v___x_2793_ = lean_nat_dec_eq(v___x_2791_, v___x_2792_);
if (v___x_2793_ == 0)
{
lean_dec_ref_known(v_a_2743_, 1);
lean_dec_ref(v___f_2741_);
lean_dec(v_goal_2721_);
return v___x_2742_;
}
else
{
goto v___jp_2745_;
}
}
else
{
goto v___jp_2745_;
}
}
else
{
lean_dec_ref_known(v_a_2743_, 1);
lean_dec_ref(v___f_2741_);
lean_dec(v_goal_2721_);
return v___x_2742_;
}
}
}
}
else
{
lean_dec_ref(v___f_2741_);
lean_dec(v_goal_2721_);
return v___x_2742_;
}
}
else
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
lean_dec(v_a_2737_);
lean_dec_ref(v_allowFailure_2724_);
lean_dec_ref(v_tactic_2723_);
lean_dec_ref(v___x_2722_);
lean_dec(v_goal_2721_);
v_a_2800_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___x_2739_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2739_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
else
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2815_; 
lean_dec_ref(v_allowFailure_2724_);
lean_dec_ref(v_tactic_2723_);
lean_dec_ref(v___x_2722_);
lean_dec(v_goal_2721_);
v_a_2808_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v___x_2736_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2736_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2813_; 
if (v_isShared_2811_ == 0)
{
v___x_2813_ = v___x_2810_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_a_2808_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
v___jp_2733_:
{
lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2734_ = lean_box(0);
v___x_2735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2734_);
return v___x_2735_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4___boxed(lean_object* v_leavePercentHeartbeats_2816_, lean_object* v_goal_2817_, lean_object* v___x_2818_, lean_object* v_tactic_2819_, lean_object* v_allowFailure_2820_, lean_object* v_collectAll_2821_, lean_object* v_includeStar_2822_, lean_object* v___x_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
uint8_t v_collectAll_boxed_2829_; uint8_t v_includeStar_boxed_2830_; uint8_t v___x_15813__boxed_2831_; lean_object* v_res_2832_; 
v_collectAll_boxed_2829_ = lean_unbox(v_collectAll_2821_);
v_includeStar_boxed_2830_ = lean_unbox(v_includeStar_2822_);
v___x_15813__boxed_2831_ = lean_unbox(v___x_2823_);
v_res_2832_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4(v_leavePercentHeartbeats_2816_, v_goal_2817_, v___x_2818_, v_tactic_2819_, v_allowFailure_2820_, v_collectAll_boxed_2829_, v_includeStar_boxed_2830_, v___x_15813__boxed_2831_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
lean_dec(v_leavePercentHeartbeats_2816_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__5(lean_object* v_leavePercentHeartbeats_2833_, lean_object* v_goal_2834_, lean_object* v___x_2835_, lean_object* v_tactic_2836_, lean_object* v_allowFailure_2837_, uint8_t v_collectAll_2838_, uint8_t v_includeStar_2839_, uint8_t v___x_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
lean_object* v___x_2849_; 
v___x_2849_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercentHeartbeats_2833_, v___y_2843_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2850_);
lean_dec_ref_known(v___x_2849_, 1);
v___x_2851_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___closed__0));
lean_inc(v_goal_2834_);
v___x_2852_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v___x_2851_, v_goal_2834_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v___f_2854_; lean_object* v___x_2855_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_a_2853_);
lean_dec_ref_known(v___x_2852_, 1);
v___f_2854_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2854_, 0, v_a_2850_);
lean_closure_set(v___f_2854_, 1, v___x_2835_);
lean_closure_set(v___f_2854_, 2, v_tactic_2836_);
lean_closure_set(v___f_2854_, 3, v_allowFailure_2837_);
lean_inc_ref(v___f_2854_);
v___x_2855_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2854_, v_a_2853_, v_collectAll_2838_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
lean_dec(v_a_2853_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_a_2856_);
if (lean_obj_tag(v_a_2856_) == 0)
{
lean_dec_ref_known(v___x_2855_, 1);
lean_dec_ref(v___f_2854_);
lean_dec(v_goal_2834_);
goto v___jp_2846_;
}
else
{
lean_object* v_val_2857_; lean_object* v___x_2907_; lean_object* v___x_2908_; uint8_t v___x_2909_; 
v_val_2857_ = lean_ctor_get(v_a_2856_, 0);
v___x_2907_ = lean_unsigned_to_nat(0u);
v___x_2908_ = lean_array_get_size(v_val_2857_);
v___x_2909_ = lean_nat_dec_lt(v___x_2907_, v___x_2908_);
if (v___x_2909_ == 0)
{
goto v___jp_2903_;
}
else
{
if (v___x_2909_ == 0)
{
goto v___jp_2903_;
}
else
{
size_t v___x_2910_; size_t v___x_2911_; uint8_t v___x_2912_; 
v___x_2910_ = ((size_t)0ULL);
v___x_2911_ = lean_usize_of_nat(v___x_2908_);
v___x_2912_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_val_2857_, v___x_2910_, v___x_2911_);
if (v___x_2912_ == 0)
{
goto v___jp_2903_;
}
else
{
if (v___x_2840_ == 0)
{
goto v___jp_2902_;
}
else
{
lean_dec_ref_known(v_a_2856_, 1);
lean_dec_ref(v___f_2854_);
lean_dec(v_goal_2834_);
return v___x_2855_;
}
}
}
}
v___jp_2858_:
{
lean_object* v___x_2859_; 
v___x_2859_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2893_; 
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2862_ = v___x_2859_;
v_isShared_2863_ = v_isSharedCheck_2893_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2859_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2893_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2864_; lean_object* v___x_2865_; uint8_t v___x_2866_; 
v___x_2864_ = lean_array_get_size(v_a_2860_);
v___x_2865_ = lean_unsigned_to_nat(0u);
v___x_2866_ = lean_nat_dec_eq(v___x_2864_, v___x_2865_);
if (v___x_2866_ == 0)
{
lean_object* v___x_2867_; lean_object* v_mctx_2868_; size_t v_sz_2869_; size_t v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
lean_inc(v_val_2857_);
lean_del_object(v___x_2862_);
lean_dec_ref_known(v_a_2856_, 1);
v___x_2867_ = lean_st_ref_get(v___y_2842_);
v_mctx_2868_ = lean_ctor_get(v___x_2867_, 0);
lean_inc_ref(v_mctx_2868_);
lean_dec(v___x_2867_);
v_sz_2869_ = lean_array_size(v_a_2860_);
v___x_2870_ = ((size_t)0ULL);
v___x_2871_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2834_, v_mctx_2868_, v_sz_2869_, v___x_2870_, v_a_2860_);
v___x_2872_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2854_, v___x_2871_, v_collectAll_2838_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
lean_dec_ref(v___x_2871_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2889_; 
v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2875_ = v___x_2872_;
v_isShared_2876_ = v_isSharedCheck_2889_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2872_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2889_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
if (lean_obj_tag(v_a_2873_) == 0)
{
lean_del_object(v___x_2875_);
lean_dec(v_val_2857_);
goto v___jp_2846_;
}
else
{
lean_object* v_val_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2888_; 
v_val_2877_ = lean_ctor_get(v_a_2873_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v_a_2873_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2879_ = v_a_2873_;
v_isShared_2880_ = v_isSharedCheck_2888_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_val_2877_);
lean_dec(v_a_2873_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2888_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2881_; lean_object* v___x_2883_; 
v___x_2881_ = l_Array_append___redArg(v_val_2857_, v_val_2877_);
lean_dec(v_val_2877_);
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 0, v___x_2881_);
v___x_2883_ = v___x_2879_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v___x_2881_);
v___x_2883_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
lean_object* v___x_2885_; 
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 0, v___x_2883_);
v___x_2885_ = v___x_2875_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2883_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
}
}
else
{
lean_dec(v_val_2857_);
return v___x_2872_;
}
}
else
{
lean_object* v___x_2891_; 
lean_dec(v_a_2860_);
lean_dec_ref(v___f_2854_);
lean_dec(v_goal_2834_);
if (v_isShared_2863_ == 0)
{
lean_ctor_set(v___x_2862_, 0, v_a_2856_);
v___x_2891_ = v___x_2862_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2856_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
else
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
lean_dec_ref_known(v_a_2856_, 1);
lean_dec_ref(v___f_2854_);
lean_dec(v_goal_2834_);
v_a_2894_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v___x_2859_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2859_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2894_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
}
v___jp_2902_:
{
if (v_includeStar_2839_ == 0)
{
if (v___x_2840_ == 0)
{
lean_dec_ref_known(v___x_2855_, 1);
goto v___jp_2858_;
}
else
{
lean_dec_ref_known(v_a_2856_, 1);
lean_dec_ref(v___f_2854_);
lean_dec(v_goal_2834_);
return v___x_2855_;
}
}
else
{
lean_dec_ref_known(v___x_2855_, 1);
goto v___jp_2858_;
}
}
v___jp_2903_:
{
if (v_collectAll_2838_ == 0)
{
if (v___x_2840_ == 0)
{
goto v___jp_2902_;
}
else
{
lean_object* v___x_2904_; lean_object* v___x_2905_; uint8_t v___x_2906_; 
v___x_2904_ = lean_array_get_size(v_val_2857_);
v___x_2905_ = lean_unsigned_to_nat(0u);
v___x_2906_ = lean_nat_dec_eq(v___x_2904_, v___x_2905_);
if (v___x_2906_ == 0)
{
lean_dec_ref_known(v_a_2856_, 1);
lean_dec_ref(v___f_2854_);
lean_dec(v_goal_2834_);
return v___x_2855_;
}
else
{
goto v___jp_2902_;
}
}
}
else
{
goto v___jp_2902_;
}
}
}
}
else
{
lean_dec_ref(v___f_2854_);
lean_dec(v_goal_2834_);
return v___x_2855_;
}
}
else
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
lean_dec(v_a_2850_);
lean_dec_ref(v_allowFailure_2837_);
lean_dec_ref(v_tactic_2836_);
lean_dec_ref(v___x_2835_);
lean_dec(v_goal_2834_);
v_a_2913_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2915_ = v___x_2852_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2852_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
if (v_isShared_2916_ == 0)
{
v___x_2918_ = v___x_2915_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_a_2913_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
}
else
{
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2928_; 
lean_dec_ref(v_allowFailure_2837_);
lean_dec_ref(v_tactic_2836_);
lean_dec_ref(v___x_2835_);
lean_dec(v_goal_2834_);
v_a_2921_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2923_ = v___x_2849_;
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2849_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2926_; 
if (v_isShared_2924_ == 0)
{
v___x_2926_ = v___x_2923_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_a_2921_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
v___jp_2846_:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___x_2847_ = lean_box(0);
v___x_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2847_);
return v___x_2848_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__5___boxed(lean_object* v_leavePercentHeartbeats_2929_, lean_object* v_goal_2930_, lean_object* v___x_2931_, lean_object* v_tactic_2932_, lean_object* v_allowFailure_2933_, lean_object* v_collectAll_2934_, lean_object* v_includeStar_2935_, lean_object* v___x_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
uint8_t v_collectAll_boxed_2942_; uint8_t v_includeStar_boxed_2943_; uint8_t v___x_16002__boxed_2944_; lean_object* v_res_2945_; 
v_collectAll_boxed_2942_ = lean_unbox(v_collectAll_2934_);
v_includeStar_boxed_2943_ = lean_unbox(v_includeStar_2935_);
v___x_16002__boxed_2944_ = lean_unbox(v___x_2936_);
v_res_2945_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__5(v_leavePercentHeartbeats_2929_, v_goal_2930_, v___x_2931_, v_tactic_2932_, v_allowFailure_2933_, v_collectAll_boxed_2942_, v_includeStar_boxed_2943_, v___x_16002__boxed_2944_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec(v_leavePercentHeartbeats_2929_);
return v_res_2945_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(lean_object* v_e_2946_){
_start:
{
if (lean_obj_tag(v_e_2946_) == 0)
{
uint8_t v___x_2947_; 
v___x_2947_ = 2;
return v___x_2947_;
}
else
{
lean_object* v_a_2948_; 
v_a_2948_ = lean_ctor_get(v_e_2946_, 0);
if (lean_obj_tag(v_a_2948_) == 0)
{
uint8_t v___x_2949_; 
v___x_2949_ = 1;
return v___x_2949_;
}
else
{
uint8_t v___x_2950_; 
v___x_2950_ = 0;
return v___x_2950_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4___boxed(lean_object* v_e_2951_){
_start:
{
uint8_t v_res_2952_; lean_object* v_r_2953_; 
v_res_2952_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(v_e_2951_);
lean_dec_ref(v_e_2951_);
v_r_2953_ = lean_box(v_res_2952_);
return v_r_2953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(lean_object* v_cls_2954_, uint8_t v_collapsed_2955_, lean_object* v_tag_2956_, lean_object* v_opts_2957_, uint8_t v_clsEnabled_2958_, lean_object* v_oldTraces_2959_, lean_object* v_msg_2960_, lean_object* v_resStartStop_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_){
_start:
{
lean_object* v_fst_2967_; lean_object* v_snd_2968_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v_data_2972_; lean_object* v_fst_2983_; lean_object* v_snd_2984_; lean_object* v___x_2985_; uint8_t v___x_2986_; lean_object* v___y_2988_; lean_object* v_a_2989_; uint8_t v___y_3004_; double v___y_3035_; 
v_fst_2967_ = lean_ctor_get(v_resStartStop_2961_, 0);
lean_inc(v_fst_2967_);
v_snd_2968_ = lean_ctor_get(v_resStartStop_2961_, 1);
lean_inc(v_snd_2968_);
lean_dec_ref(v_resStartStop_2961_);
v_fst_2983_ = lean_ctor_get(v_snd_2968_, 0);
lean_inc(v_fst_2983_);
v_snd_2984_ = lean_ctor_get(v_snd_2968_, 1);
lean_inc(v_snd_2984_);
lean_dec(v_snd_2968_);
v___x_2985_ = l_Lean_trace_profiler;
v___x_2986_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_2957_, v___x_2985_);
if (v___x_2986_ == 0)
{
v___y_3004_ = v___x_2986_;
goto v___jp_3003_;
}
else
{
lean_object* v___x_3040_; uint8_t v___x_3041_; 
v___x_3040_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3041_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_2957_, v___x_3040_);
if (v___x_3041_ == 0)
{
lean_object* v___x_3042_; lean_object* v___x_3043_; double v___x_3044_; double v___x_3045_; double v___x_3046_; 
v___x_3042_ = l_Lean_trace_profiler_threshold;
v___x_3043_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_2957_, v___x_3042_);
v___x_3044_ = lean_float_of_nat(v___x_3043_);
v___x_3045_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3);
v___x_3046_ = lean_float_div(v___x_3044_, v___x_3045_);
v___y_3035_ = v___x_3046_;
goto v___jp_3034_;
}
else
{
lean_object* v___x_3047_; lean_object* v___x_3048_; double v___x_3049_; 
v___x_3047_ = l_Lean_trace_profiler_threshold;
v___x_3048_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_2957_, v___x_3047_);
v___x_3049_ = lean_float_of_nat(v___x_3048_);
v___y_3035_ = v___x_3049_;
goto v___jp_3034_;
}
}
v___jp_2969_:
{
lean_object* v___x_2973_; 
lean_inc(v___y_2970_);
v___x_2973_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(v_oldTraces_2959_, v_data_2972_, v___y_2970_, v___y_2971_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v___x_2974_; 
lean_dec_ref_known(v___x_2973_, 1);
v___x_2974_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_2967_);
return v___x_2974_;
}
else
{
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2982_; 
lean_dec(v_fst_2967_);
v_a_2975_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2977_ = v___x_2973_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2973_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2980_; 
if (v_isShared_2978_ == 0)
{
v___x_2980_ = v___x_2977_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2975_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
}
v___jp_2987_:
{
uint8_t v_result_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; double v___x_2993_; lean_object* v_data_2994_; 
v_result_2990_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(v_fst_2967_);
v___x_2991_ = lean_box(v_result_2990_);
v___x_2992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2991_);
v___x_2993_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0);
lean_inc_ref(v_tag_2956_);
lean_inc_ref(v___x_2992_);
lean_inc(v_cls_2954_);
v_data_2994_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2994_, 0, v_cls_2954_);
lean_ctor_set(v_data_2994_, 1, v___x_2992_);
lean_ctor_set(v_data_2994_, 2, v_tag_2956_);
lean_ctor_set_float(v_data_2994_, sizeof(void*)*3, v___x_2993_);
lean_ctor_set_float(v_data_2994_, sizeof(void*)*3 + 8, v___x_2993_);
lean_ctor_set_uint8(v_data_2994_, sizeof(void*)*3 + 16, v_collapsed_2955_);
if (v___x_2986_ == 0)
{
lean_dec_ref_known(v___x_2992_, 1);
lean_dec(v_snd_2984_);
lean_dec(v_fst_2983_);
lean_dec_ref(v_tag_2956_);
lean_dec(v_cls_2954_);
v___y_2970_ = v___y_2988_;
v___y_2971_ = v_a_2989_;
v_data_2972_ = v_data_2994_;
goto v___jp_2969_;
}
else
{
lean_object* v_data_2995_; double v___x_2996_; double v___x_2997_; 
lean_dec_ref_known(v_data_2994_, 3);
v_data_2995_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2995_, 0, v_cls_2954_);
lean_ctor_set(v_data_2995_, 1, v___x_2992_);
lean_ctor_set(v_data_2995_, 2, v_tag_2956_);
v___x_2996_ = lean_unbox_float(v_fst_2983_);
lean_dec(v_fst_2983_);
lean_ctor_set_float(v_data_2995_, sizeof(void*)*3, v___x_2996_);
v___x_2997_ = lean_unbox_float(v_snd_2984_);
lean_dec(v_snd_2984_);
lean_ctor_set_float(v_data_2995_, sizeof(void*)*3 + 8, v___x_2997_);
lean_ctor_set_uint8(v_data_2995_, sizeof(void*)*3 + 16, v_collapsed_2955_);
v___y_2970_ = v___y_2988_;
v___y_2971_ = v_a_2989_;
v_data_2972_ = v_data_2995_;
goto v___jp_2969_;
}
}
v___jp_2998_:
{
lean_object* v_ref_2999_; lean_object* v___x_3000_; 
v_ref_2999_ = lean_ctor_get(v___y_2964_, 5);
lean_inc(v___y_2965_);
lean_inc_ref(v___y_2964_);
lean_inc(v___y_2963_);
lean_inc_ref(v___y_2962_);
lean_inc(v_fst_2967_);
v___x_3000_ = lean_apply_6(v_msg_2960_, v_fst_2967_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, lean_box(0));
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v_a_3001_; 
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
lean_inc(v_a_3001_);
lean_dec_ref_known(v___x_3000_, 1);
v___y_2988_ = v_ref_2999_;
v_a_2989_ = v_a_3001_;
goto v___jp_2987_;
}
else
{
lean_object* v___x_3002_; 
lean_dec_ref_known(v___x_3000_, 1);
v___x_3002_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2);
v___y_2988_ = v_ref_2999_;
v_a_2989_ = v___x_3002_;
goto v___jp_2987_;
}
}
v___jp_3003_:
{
if (v_clsEnabled_2958_ == 0)
{
if (v___y_3004_ == 0)
{
lean_object* v___x_3005_; lean_object* v_traceState_3006_; lean_object* v_env_3007_; lean_object* v_nextMacroScope_3008_; lean_object* v_ngen_3009_; lean_object* v_auxDeclNGen_3010_; lean_object* v_cache_3011_; lean_object* v_messages_3012_; lean_object* v_infoState_3013_; lean_object* v_snapshotTasks_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3033_; 
lean_dec(v_snd_2984_);
lean_dec(v_fst_2983_);
lean_dec_ref(v_msg_2960_);
lean_dec_ref(v_tag_2956_);
lean_dec(v_cls_2954_);
v___x_3005_ = lean_st_ref_take(v___y_2965_);
v_traceState_3006_ = lean_ctor_get(v___x_3005_, 4);
v_env_3007_ = lean_ctor_get(v___x_3005_, 0);
v_nextMacroScope_3008_ = lean_ctor_get(v___x_3005_, 1);
v_ngen_3009_ = lean_ctor_get(v___x_3005_, 2);
v_auxDeclNGen_3010_ = lean_ctor_get(v___x_3005_, 3);
v_cache_3011_ = lean_ctor_get(v___x_3005_, 5);
v_messages_3012_ = lean_ctor_get(v___x_3005_, 6);
v_infoState_3013_ = lean_ctor_get(v___x_3005_, 7);
v_snapshotTasks_3014_ = lean_ctor_get(v___x_3005_, 8);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3016_ = v___x_3005_;
v_isShared_3017_ = v_isSharedCheck_3033_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_snapshotTasks_3014_);
lean_inc(v_infoState_3013_);
lean_inc(v_messages_3012_);
lean_inc(v_cache_3011_);
lean_inc(v_traceState_3006_);
lean_inc(v_auxDeclNGen_3010_);
lean_inc(v_ngen_3009_);
lean_inc(v_nextMacroScope_3008_);
lean_inc(v_env_3007_);
lean_dec(v___x_3005_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3033_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
uint64_t v_tid_3018_; lean_object* v_traces_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3032_; 
v_tid_3018_ = lean_ctor_get_uint64(v_traceState_3006_, sizeof(void*)*1);
v_traces_3019_ = lean_ctor_get(v_traceState_3006_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v_traceState_3006_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3021_ = v_traceState_3006_;
v_isShared_3022_ = v_isSharedCheck_3032_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_traces_3019_);
lean_dec(v_traceState_3006_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3032_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3023_; lean_object* v___x_3025_; 
v___x_3023_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2959_, v_traces_3019_);
lean_dec_ref(v_traces_3019_);
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 0, v___x_3023_);
v___x_3025_ = v___x_3021_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v___x_3023_);
lean_ctor_set_uint64(v_reuseFailAlloc_3031_, sizeof(void*)*1, v_tid_3018_);
v___x_3025_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
lean_object* v___x_3027_; 
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 4, v___x_3025_);
v___x_3027_ = v___x_3016_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_env_3007_);
lean_ctor_set(v_reuseFailAlloc_3030_, 1, v_nextMacroScope_3008_);
lean_ctor_set(v_reuseFailAlloc_3030_, 2, v_ngen_3009_);
lean_ctor_set(v_reuseFailAlloc_3030_, 3, v_auxDeclNGen_3010_);
lean_ctor_set(v_reuseFailAlloc_3030_, 4, v___x_3025_);
lean_ctor_set(v_reuseFailAlloc_3030_, 5, v_cache_3011_);
lean_ctor_set(v_reuseFailAlloc_3030_, 6, v_messages_3012_);
lean_ctor_set(v_reuseFailAlloc_3030_, 7, v_infoState_3013_);
lean_ctor_set(v_reuseFailAlloc_3030_, 8, v_snapshotTasks_3014_);
v___x_3027_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3028_ = lean_st_ref_set(v___y_2965_, v___x_3027_);
v___x_3029_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_2967_);
return v___x_3029_;
}
}
}
}
}
else
{
goto v___jp_2998_;
}
}
else
{
goto v___jp_2998_;
}
}
v___jp_3034_:
{
double v___x_3036_; double v___x_3037_; double v___x_3038_; uint8_t v___x_3039_; 
v___x_3036_ = lean_unbox_float(v_snd_2984_);
v___x_3037_ = lean_unbox_float(v_fst_2983_);
v___x_3038_ = lean_float_sub(v___x_3036_, v___x_3037_);
v___x_3039_ = lean_float_decLt(v___y_3035_, v___x_3038_);
v___y_3004_ = v___x_3039_;
goto v___jp_3003_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4___boxed(lean_object* v_cls_3050_, lean_object* v_collapsed_3051_, lean_object* v_tag_3052_, lean_object* v_opts_3053_, lean_object* v_clsEnabled_3054_, lean_object* v_oldTraces_3055_, lean_object* v_msg_3056_, lean_object* v_resStartStop_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_){
_start:
{
uint8_t v_collapsed_boxed_3063_; uint8_t v_clsEnabled_boxed_3064_; lean_object* v_res_3065_; 
v_collapsed_boxed_3063_ = lean_unbox(v_collapsed_3051_);
v_clsEnabled_boxed_3064_ = lean_unbox(v_clsEnabled_3054_);
v_res_3065_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v_cls_3050_, v_collapsed_boxed_3063_, v_tag_3052_, v_opts_3053_, v_clsEnabled_boxed_3064_, v_oldTraces_3055_, v_msg_3056_, v_resStartStop_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec_ref(v_opts_3053_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(lean_object* v_goal_3069_, lean_object* v_tactic_3070_, lean_object* v_allowFailure_3071_, lean_object* v_leavePercentHeartbeats_3072_, uint8_t v_includeStar_3073_, uint8_t v_collectAll_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_){
_start:
{
lean_object* v_options_3080_; lean_object* v_inheritedTraceOptions_3081_; uint8_t v_hasTrace_3082_; lean_object* v___x_3083_; 
v_options_3080_ = lean_ctor_get(v_a_3077_, 2);
v_inheritedTraceOptions_3081_ = lean_ctor_get(v_a_3077_, 13);
v_hasTrace_3082_ = lean_ctor_get_uint8(v_options_3080_, sizeof(void*)*1);
v___x_3083_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
if (v_hasTrace_3082_ == 0)
{
lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___f_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3084_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___closed__0));
v___x_3085_ = lean_box(v_collectAll_3074_);
v___x_3086_ = lean_box(v_includeStar_3073_);
v___f_3087_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed), 12, 7);
lean_closure_set(v___f_3087_, 0, v_leavePercentHeartbeats_3072_);
lean_closure_set(v___f_3087_, 1, v_goal_3069_);
lean_closure_set(v___f_3087_, 2, v___x_3084_);
lean_closure_set(v___f_3087_, 3, v_tactic_3070_);
lean_closure_set(v___f_3087_, 4, v_allowFailure_3071_);
lean_closure_set(v___f_3087_, 5, v___x_3085_);
lean_closure_set(v___f_3087_, 6, v___x_3086_);
v___x_3088_ = lean_box(0);
v___x_3089_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_3083_, v_options_3080_, v___f_3087_, v___x_3088_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_);
return v___x_3089_;
}
else
{
lean_object* v___f_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; uint8_t v___x_3094_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v_a_3098_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v_a_3113_; 
lean_inc(v_goal_3069_);
v___f_3090_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2___boxed), 7, 1);
lean_closure_set(v___f_3090_, 0, v_goal_3069_);
v___x_3091_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_3092_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__4));
v___x_3093_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2);
v___x_3094_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3081_, v_options_3080_, v___x_3093_);
if (v___x_3094_ == 0)
{
lean_object* v___x_3177_; uint8_t v___x_3178_; 
v___x_3177_ = l_Lean_trace_profiler;
v___x_3178_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_3080_, v___x_3177_);
if (v___x_3178_ == 0)
{
uint8_t v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___f_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; 
lean_dec_ref(v___f_3090_);
v___x_3179_ = 0;
v___x_3180_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3180_, 0, v___x_3179_);
lean_ctor_set_uint8(v___x_3180_, 1, v_hasTrace_3082_);
lean_ctor_set_uint8(v___x_3180_, 2, v_hasTrace_3082_);
lean_ctor_set_uint8(v___x_3180_, 3, v_hasTrace_3082_);
v___x_3181_ = lean_box(v_collectAll_3074_);
v___x_3182_ = lean_box(v_includeStar_3073_);
v___x_3183_ = lean_box(v___x_3178_);
v___f_3184_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4___boxed), 13, 8);
lean_closure_set(v___f_3184_, 0, v_leavePercentHeartbeats_3072_);
lean_closure_set(v___f_3184_, 1, v_goal_3069_);
lean_closure_set(v___f_3184_, 2, v___x_3180_);
lean_closure_set(v___f_3184_, 3, v_tactic_3070_);
lean_closure_set(v___f_3184_, 4, v_allowFailure_3071_);
lean_closure_set(v___f_3184_, 5, v___x_3181_);
lean_closure_set(v___f_3184_, 6, v___x_3182_);
lean_closure_set(v___f_3184_, 7, v___x_3183_);
v___x_3185_ = lean_box(0);
v___x_3186_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_3083_, v_options_3080_, v___f_3184_, v___x_3185_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_);
return v___x_3186_;
}
else
{
goto v___jp_3122_;
}
}
else
{
goto v___jp_3122_;
}
v___jp_3095_:
{
lean_object* v___x_3099_; double v___x_3100_; double v___x_3101_; double v___x_3102_; double v___x_3103_; double v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3099_ = lean_io_mono_nanos_now();
v___x_3100_ = lean_float_of_nat(v___y_3096_);
v___x_3101_ = lean_float_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3);
v___x_3102_ = lean_float_div(v___x_3100_, v___x_3101_);
v___x_3103_ = lean_float_of_nat(v___x_3099_);
v___x_3104_ = lean_float_div(v___x_3103_, v___x_3101_);
v___x_3105_ = lean_box_float(v___x_3102_);
v___x_3106_ = lean_box_float(v___x_3104_);
v___x_3107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3105_);
lean_ctor_set(v___x_3107_, 1, v___x_3106_);
v___x_3108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3108_, 0, v_a_3098_);
lean_ctor_set(v___x_3108_, 1, v___x_3107_);
v___x_3109_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v___x_3091_, v_hasTrace_3082_, v___x_3092_, v_options_3080_, v___x_3094_, v___y_3097_, v___f_3090_, v___x_3108_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_);
return v___x_3109_;
}
v___jp_3110_:
{
lean_object* v___x_3114_; double v___x_3115_; double v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3114_ = lean_io_get_num_heartbeats();
v___x_3115_ = lean_float_of_nat(v___y_3112_);
v___x_3116_ = lean_float_of_nat(v___x_3114_);
v___x_3117_ = lean_box_float(v___x_3115_);
v___x_3118_ = lean_box_float(v___x_3116_);
v___x_3119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3119_, 0, v___x_3117_);
lean_ctor_set(v___x_3119_, 1, v___x_3118_);
v___x_3120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3120_, 0, v_a_3113_);
lean_ctor_set(v___x_3120_, 1, v___x_3119_);
v___x_3121_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v___x_3091_, v_hasTrace_3082_, v___x_3092_, v_options_3080_, v___x_3094_, v___y_3111_, v___f_3090_, v___x_3120_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_);
return v___x_3121_;
}
v___jp_3122_:
{
lean_object* v___x_3123_; lean_object* v_a_3124_; lean_object* v___x_3125_; uint8_t v___x_3126_; 
v___x_3123_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v_a_3078_);
v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
lean_inc(v_a_3124_);
lean_dec_ref(v___x_3123_);
v___x_3125_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3126_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_3080_, v___x_3125_);
if (v___x_3126_ == 0)
{
lean_object* v___x_3127_; uint8_t v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___f_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3127_ = lean_io_mono_nanos_now();
v___x_3128_ = 0;
v___x_3129_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3129_, 0, v___x_3128_);
lean_ctor_set_uint8(v___x_3129_, 1, v_hasTrace_3082_);
lean_ctor_set_uint8(v___x_3129_, 2, v_hasTrace_3082_);
lean_ctor_set_uint8(v___x_3129_, 3, v_hasTrace_3082_);
v___x_3130_ = lean_box(v_collectAll_3074_);
v___x_3131_ = lean_box(v_includeStar_3073_);
v___x_3132_ = lean_box(v___x_3126_);
v___f_3133_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4___boxed), 13, 8);
lean_closure_set(v___f_3133_, 0, v_leavePercentHeartbeats_3072_);
lean_closure_set(v___f_3133_, 1, v_goal_3069_);
lean_closure_set(v___f_3133_, 2, v___x_3129_);
lean_closure_set(v___f_3133_, 3, v_tactic_3070_);
lean_closure_set(v___f_3133_, 4, v_allowFailure_3071_);
lean_closure_set(v___f_3133_, 5, v___x_3130_);
lean_closure_set(v___f_3133_, 6, v___x_3131_);
lean_closure_set(v___f_3133_, 7, v___x_3132_);
v___x_3134_ = lean_box(0);
v___x_3135_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_3083_, v_options_3080_, v___f_3133_, v___x_3134_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_);
if (lean_obj_tag(v___x_3135_) == 0)
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
v_a_3136_ = lean_ctor_get(v___x_3135_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3138_ = v___x_3135_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3135_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3139_ == 0)
{
lean_ctor_set_tag(v___x_3138_, 1);
v___x_3141_ = v___x_3138_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3136_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
v___y_3096_ = v___x_3127_;
v___y_3097_ = v_a_3124_;
v_a_3098_ = v___x_3141_;
goto v___jp_3095_;
}
}
}
else
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
v_a_3144_ = lean_ctor_get(v___x_3135_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3146_ = v___x_3135_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3135_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
lean_ctor_set_tag(v___x_3146_, 0);
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3144_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
v___y_3096_ = v___x_3127_;
v___y_3097_ = v_a_3124_;
v_a_3098_ = v___x_3149_;
goto v___jp_3095_;
}
}
}
}
else
{
lean_object* v___x_3152_; uint8_t v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___f_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3152_ = lean_io_get_num_heartbeats();
v___x_3153_ = 0;
v___x_3154_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3154_, 0, v___x_3153_);
lean_ctor_set_uint8(v___x_3154_, 1, v___x_3126_);
lean_ctor_set_uint8(v___x_3154_, 2, v___x_3126_);
lean_ctor_set_uint8(v___x_3154_, 3, v___x_3126_);
v___x_3155_ = lean_box(v_collectAll_3074_);
v___x_3156_ = lean_box(v_includeStar_3073_);
v___x_3157_ = lean_box(v___x_3126_);
v___f_3158_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__5___boxed), 13, 8);
lean_closure_set(v___f_3158_, 0, v_leavePercentHeartbeats_3072_);
lean_closure_set(v___f_3158_, 1, v_goal_3069_);
lean_closure_set(v___f_3158_, 2, v___x_3154_);
lean_closure_set(v___f_3158_, 3, v_tactic_3070_);
lean_closure_set(v___f_3158_, 4, v_allowFailure_3071_);
lean_closure_set(v___f_3158_, 5, v___x_3155_);
lean_closure_set(v___f_3158_, 6, v___x_3156_);
lean_closure_set(v___f_3158_, 7, v___x_3157_);
v___x_3159_ = lean_box(0);
v___x_3160_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_3083_, v_options_3080_, v___f_3158_, v___x_3159_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3168_; 
v_a_3161_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3163_ = v___x_3160_;
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___x_3160_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3166_; 
if (v_isShared_3164_ == 0)
{
lean_ctor_set_tag(v___x_3163_, 1);
v___x_3166_ = v___x_3163_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_a_3161_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
v___y_3111_ = v_a_3124_;
v___y_3112_ = v___x_3152_;
v_a_3113_ = v___x_3166_;
goto v___jp_3110_;
}
}
}
else
{
lean_object* v_a_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3176_; 
v_a_3169_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3171_ = v___x_3160_;
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_a_3169_);
lean_dec(v___x_3160_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___x_3174_; 
if (v_isShared_3172_ == 0)
{
lean_ctor_set_tag(v___x_3171_, 0);
v___x_3174_ = v___x_3171_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_a_3169_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
v___y_3111_ = v_a_3124_;
v___y_3112_ = v___x_3152_;
v_a_3113_ = v___x_3174_;
goto v___jp_3110_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___boxed(lean_object* v_goal_3187_, lean_object* v_tactic_3188_, lean_object* v_allowFailure_3189_, lean_object* v_leavePercentHeartbeats_3190_, lean_object* v_includeStar_3191_, lean_object* v_collectAll_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_){
_start:
{
uint8_t v_includeStar_boxed_3198_; uint8_t v_collectAll_boxed_3199_; lean_object* v_res_3200_; 
v_includeStar_boxed_3198_ = lean_unbox(v_includeStar_3191_);
v_collectAll_boxed_3199_ = lean_unbox(v_collectAll_3192_);
v_res_3200_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(v_goal_3187_, v_tactic_3188_, v_allowFailure_3189_, v_leavePercentHeartbeats_3190_, v_includeStar_boxed_3198_, v_collectAll_boxed_3199_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_);
lean_dec(v_a_3196_);
lean_dec_ref(v_a_3195_);
lean_dec(v_a_3194_);
lean_dec_ref(v_a_3193_);
return v_res_3200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearch(lean_object* v_goal_3201_, lean_object* v_tactic_3202_, lean_object* v_allowFailure_3203_, lean_object* v_leavePercentHeartbeats_3204_, uint8_t v_includeStar_3205_, uint8_t v_collectAll_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_){
_start:
{
lean_object* v___x_3212_; 
v___x_3212_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(v_goal_3201_, v_tactic_3202_, v_allowFailure_3203_, v_leavePercentHeartbeats_3204_, v_includeStar_3205_, v_collectAll_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_);
return v___x_3212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearch___boxed(lean_object* v_goal_3213_, lean_object* v_tactic_3214_, lean_object* v_allowFailure_3215_, lean_object* v_leavePercentHeartbeats_3216_, lean_object* v_includeStar_3217_, lean_object* v_collectAll_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_){
_start:
{
uint8_t v_includeStar_boxed_3224_; uint8_t v_collectAll_boxed_3225_; lean_object* v_res_3226_; 
v_includeStar_boxed_3224_ = lean_unbox(v_includeStar_3217_);
v_collectAll_boxed_3225_ = lean_unbox(v_collectAll_3218_);
v_res_3226_ = l_Lean_Meta_LibrarySearch_librarySearch(v_goal_3213_, v_tactic_3214_, v_allowFailure_3215_, v_leavePercentHeartbeats_3216_, v_includeStar_boxed_3224_, v_collectAll_boxed_3225_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_);
lean_dec(v_a_3222_);
lean_dec_ref(v_a_3221_);
lean_dec(v_a_3220_);
lean_dec_ref(v_a_3219_);
return v_res_3226_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_LibrarySearch(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
