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
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_toCtorIdx(uint8_t v_x_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(v_x_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_toCtorIdx___boxed(lean_object* v_x_556_){
_start:
{
uint8_t v_x_4__boxed_557_; lean_object* v_res_558_; 
v_x_4__boxed_557_ = lean_unbox(v_x_556_);
v_res_558_ = l_Lean_Meta_LibrarySearch_DeclMod_toCtorIdx(v_x_4__boxed_557_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___redArg(lean_object* v_k_559_){
_start:
{
lean_inc(v_k_559_);
return v_k_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___redArg___boxed(lean_object* v_k_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___redArg(v_k_560_);
lean_dec(v_k_560_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim(lean_object* v_motive_562_, lean_object* v_ctorIdx_563_, uint8_t v_t_564_, lean_object* v_h_565_, lean_object* v_k_566_){
_start:
{
lean_inc(v_k_566_);
return v_k_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___boxed(lean_object* v_motive_567_, lean_object* v_ctorIdx_568_, lean_object* v_t_569_, lean_object* v_h_570_, lean_object* v_k_571_){
_start:
{
uint8_t v_t_boxed_572_; lean_object* v_res_573_; 
v_t_boxed_572_ = lean_unbox(v_t_569_);
v_res_573_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorElim(v_motive_567_, v_ctorIdx_568_, v_t_boxed_572_, v_h_570_, v_k_571_);
lean_dec(v_k_571_);
lean_dec(v_ctorIdx_568_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim___redArg(lean_object* v_none_574_){
_start:
{
lean_inc(v_none_574_);
return v_none_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim___redArg___boxed(lean_object* v_none_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_Meta_LibrarySearch_DeclMod_none_elim___redArg(v_none_575_);
lean_dec(v_none_575_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim(lean_object* v_motive_577_, uint8_t v_t_578_, lean_object* v_h_579_, lean_object* v_none_580_){
_start:
{
lean_inc(v_none_580_);
return v_none_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim___boxed(lean_object* v_motive_581_, lean_object* v_t_582_, lean_object* v_h_583_, lean_object* v_none_584_){
_start:
{
uint8_t v_t_boxed_585_; lean_object* v_res_586_; 
v_t_boxed_585_ = lean_unbox(v_t_582_);
v_res_586_ = l_Lean_Meta_LibrarySearch_DeclMod_none_elim(v_motive_581_, v_t_boxed_585_, v_h_583_, v_none_584_);
lean_dec(v_none_584_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___redArg(lean_object* v_mp_587_){
_start:
{
lean_inc(v_mp_587_);
return v_mp_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___redArg___boxed(lean_object* v_mp_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___redArg(v_mp_588_);
lean_dec(v_mp_588_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim(lean_object* v_motive_590_, uint8_t v_t_591_, lean_object* v_h_592_, lean_object* v_mp_593_){
_start:
{
lean_inc(v_mp_593_);
return v_mp_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___boxed(lean_object* v_motive_594_, lean_object* v_t_595_, lean_object* v_h_596_, lean_object* v_mp_597_){
_start:
{
uint8_t v_t_boxed_598_; lean_object* v_res_599_; 
v_t_boxed_598_ = lean_unbox(v_t_595_);
v_res_599_ = l_Lean_Meta_LibrarySearch_DeclMod_mp_elim(v_motive_594_, v_t_boxed_598_, v_h_596_, v_mp_597_);
lean_dec(v_mp_597_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___redArg(lean_object* v_mpr_600_){
_start:
{
lean_inc(v_mpr_600_);
return v_mpr_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___redArg___boxed(lean_object* v_mpr_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___redArg(v_mpr_601_);
lean_dec(v_mpr_601_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim(lean_object* v_motive_603_, uint8_t v_t_604_, lean_object* v_h_605_, lean_object* v_mpr_606_){
_start:
{
lean_inc(v_mpr_606_);
return v_mpr_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___boxed(lean_object* v_motive_607_, lean_object* v_t_608_, lean_object* v_h_609_, lean_object* v_mpr_610_){
_start:
{
uint8_t v_t_boxed_611_; lean_object* v_res_612_; 
v_t_boxed_611_ = lean_unbox(v_t_608_);
v_res_612_ = l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim(v_motive_607_, v_t_boxed_611_, v_h_609_, v_mpr_610_);
lean_dec(v_mpr_610_);
return v_res_612_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_DeclMod_ofNat(lean_object* v_n_613_){
_start:
{
lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_614_ = lean_unsigned_to_nat(0u);
v___x_615_ = lean_nat_dec_le(v_n_613_, v___x_614_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_616_ = lean_unsigned_to_nat(1u);
v___x_617_ = lean_nat_dec_le(v_n_613_, v___x_616_);
if (v___x_617_ == 0)
{
uint8_t v___x_618_; 
v___x_618_ = 2;
return v___x_618_;
}
else
{
uint8_t v___x_619_; 
v___x_619_ = 1;
return v___x_619_;
}
}
else
{
uint8_t v___x_620_; 
v___x_620_ = 0;
return v___x_620_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ofNat___boxed(lean_object* v_n_621_){
_start:
{
uint8_t v_res_622_; lean_object* v_r_623_; 
v_res_622_ = l_Lean_Meta_LibrarySearch_DeclMod_ofNat(v_n_621_);
lean_dec(v_n_621_);
v_r_623_ = lean_box(v_res_622_);
return v_r_623_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_instDecidableEqDeclMod(uint8_t v_x_624_, uint8_t v_y_625_){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_626_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(v_x_624_);
v___x_627_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(v_y_625_);
v___x_628_ = lean_nat_dec_eq(v___x_626_, v___x_627_);
lean_dec(v___x_627_);
lean_dec(v___x_626_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_instDecidableEqDeclMod___boxed(lean_object* v_x_629_, lean_object* v_y_630_){
_start:
{
uint8_t v_x_13__boxed_631_; uint8_t v_y_14__boxed_632_; uint8_t v_res_633_; lean_object* v_r_634_; 
v_x_13__boxed_631_ = lean_unbox(v_x_629_);
v_y_14__boxed_632_ = lean_unbox(v_y_630_);
v_res_633_ = l_Lean_Meta_LibrarySearch_instDecidableEqDeclMod(v_x_13__boxed_631_, v_y_14__boxed_632_);
v_r_634_ = lean_box(v_res_633_);
return v_r_634_;
}
}
static uint8_t _init_l_Lean_Meta_LibrarySearch_instInhabitedDeclMod_default(void){
_start:
{
uint8_t v___x_635_; 
v___x_635_ = 0;
return v___x_635_;
}
}
static uint8_t _init_l_Lean_Meta_LibrarySearch_instInhabitedDeclMod(void){
_start:
{
uint8_t v___x_636_; 
v___x_636_ = 0;
return v___x_636_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_instOrdDeclMod_ord(uint8_t v_x_637_, uint8_t v_y_638_){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_639_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(v_x_637_);
v___x_640_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(v_y_638_);
v___x_641_ = lean_nat_dec_lt(v___x_639_, v___x_640_);
if (v___x_641_ == 0)
{
uint8_t v___x_642_; 
v___x_642_ = lean_nat_dec_eq(v___x_639_, v___x_640_);
lean_dec(v___x_640_);
lean_dec(v___x_639_);
if (v___x_642_ == 0)
{
uint8_t v___x_643_; 
v___x_643_ = 2;
return v___x_643_;
}
else
{
uint8_t v___x_644_; 
v___x_644_ = 1;
return v___x_644_;
}
}
else
{
uint8_t v___x_645_; 
lean_dec(v___x_640_);
lean_dec(v___x_639_);
v___x_645_ = 0;
return v___x_645_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_instOrdDeclMod_ord___boxed(lean_object* v_x_646_, lean_object* v_y_647_){
_start:
{
uint8_t v_x_30__boxed_648_; uint8_t v_y_31__boxed_649_; uint8_t v_res_650_; lean_object* v_r_651_; 
v_x_30__boxed_648_ = lean_unbox(v_x_646_);
v_y_31__boxed_649_ = lean_unbox(v_y_647_);
v_res_650_ = l_Lean_Meta_LibrarySearch_instOrdDeclMod_ord(v_x_30__boxed_648_, v_y_31__boxed_649_);
v_r_651_ = lean_box(v_res_650_);
return v_r_651_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_LibrarySearch_instHashableDeclMod_hash(uint8_t v_x_654_){
_start:
{
switch(v_x_654_)
{
case 0:
{
uint64_t v___x_655_; 
v___x_655_ = 0ULL;
return v___x_655_;
}
case 1:
{
uint64_t v___x_656_; 
v___x_656_ = 1ULL;
return v___x_656_;
}
default: 
{
uint64_t v___x_657_; 
v___x_657_ = 2ULL;
return v___x_657_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_instHashableDeclMod_hash___boxed(lean_object* v_x_658_){
_start:
{
uint8_t v_x_40__boxed_659_; uint64_t v_res_660_; lean_object* v_r_661_; 
v_x_40__boxed_659_ = lean_unbox(v_x_658_);
v_res_660_ = l_Lean_Meta_LibrarySearch_instHashableDeclMod_hash(v_x_40__boxed_659_);
v_r_661_ = lean_box_uint64(v_res_660_);
return v_r_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0(lean_object* v_k_664_, lean_object* v_b_665_, lean_object* v_c_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v___x_672_; 
lean_inc(v___y_670_);
lean_inc_ref(v___y_669_);
lean_inc(v___y_668_);
lean_inc_ref(v___y_667_);
v___x_672_ = lean_apply_7(v_k_664_, v_b_665_, v_c_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, lean_box(0));
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0___boxed(lean_object* v_k_673_, lean_object* v_b_674_, lean_object* v_c_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0(v_k_673_, v_b_674_, v_c_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(lean_object* v_type_682_, lean_object* v_k_683_, uint8_t v_cleanupAnnotations_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v___f_690_; uint8_t v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___f_690_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_690_, 0, v_k_683_);
v___x_691_ = 0;
v___x_692_ = lean_box(0);
v___x_693_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_691_, v___x_692_, v_type_682_, v___f_690_, v_cleanupAnnotations_684_, v___x_691_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_701_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_701_ == 0)
{
v___x_696_ = v___x_693_;
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_693_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_694_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
else
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
v_a_702_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___x_693_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_693_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_a_702_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___boxed(lean_object* v_type_710_, lean_object* v_k_711_, lean_object* v_cleanupAnnotations_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_718_; lean_object* v_res_719_; 
v_cleanupAnnotations_boxed_718_ = lean_unbox(v_cleanupAnnotations_712_);
v_res_719_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(v_type_710_, v_k_711_, v_cleanupAnnotations_boxed_718_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0(lean_object* v_00_u03b1_720_, lean_object* v_type_721_, lean_object* v_k_722_, uint8_t v_cleanupAnnotations_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(v_type_721_, v_k_722_, v_cleanupAnnotations_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___boxed(lean_object* v_00_u03b1_730_, lean_object* v_type_731_, lean_object* v_k_732_, lean_object* v_cleanupAnnotations_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_739_; lean_object* v_res_740_; 
v_cleanupAnnotations_boxed_739_ = lean_unbox(v_cleanupAnnotations_733_);
v_res_740_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0(v_00_u03b1_730_, v_type_731_, v_k_732_, v_cleanupAnnotations_boxed_739_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0(lean_object* v_name_747_, lean_object* v_x_748_, lean_object* v_type_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
uint8_t v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_755_ = 0;
v___x_756_ = lean_box(v___x_755_);
lean_inc(v_name_747_);
v___x_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_757_, 0, v_name_747_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v___x_758_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_type_749_, v___x_757_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_808_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_808_ == 0)
{
v___x_761_ = v___x_758_;
v_isShared_762_ = v_isSharedCheck_808_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_758_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_808_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v_key_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; 
v_key_763_ = lean_ctor_get(v_a_759_, 0);
v___x_764_ = lean_unsigned_to_nat(1u);
v___x_765_ = lean_mk_empty_array_with_capacity(v___x_764_);
lean_inc(v_a_759_);
v___x_766_ = lean_array_push(v___x_765_, v_a_759_);
v___x_767_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__2));
v___x_768_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_763_, v___x_767_);
if (v___x_768_ == 0)
{
lean_object* v___x_770_; 
lean_dec(v_a_759_);
lean_dec(v_name_747_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v___x_766_);
v___x_770_ = v___x_761_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_766_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
else
{
lean_object* v___x_772_; uint8_t v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
lean_del_object(v___x_761_);
v___x_772_ = lean_unsigned_to_nat(0u);
v___x_773_ = 1;
v___x_774_ = lean_box(v___x_773_);
lean_inc(v_name_747_);
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v_name_747_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
lean_inc(v_a_759_);
v___x_776_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_a_759_, v___x_772_, v___x_775_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v_a_777_; uint8_t v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v_a_777_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_a_777_);
lean_dec_ref_known(v___x_776_, 1);
v___x_778_ = 2;
v___x_779_ = lean_box(v___x_778_);
v___x_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_780_, 0, v_name_747_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v___x_781_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_a_759_, v___x_764_, v___x_780_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_791_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_791_ == 0)
{
v___x_784_ = v___x_781_;
v_isShared_785_ = v_isSharedCheck_791_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_781_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_791_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_786_ = lean_array_push(v___x_766_, v_a_777_);
v___x_787_ = lean_array_push(v___x_786_, v_a_782_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v___x_787_);
v___x_789_ = v___x_784_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
else
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
lean_dec(v_a_777_);
lean_dec_ref(v___x_766_);
v_a_792_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_781_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_781_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
else
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_dec_ref(v___x_766_);
lean_dec(v_a_759_);
lean_dec(v_name_747_);
v_a_800_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_776_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_776_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_800_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec(v_name_747_);
v_a_809_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_758_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_758_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___boxed(lean_object* v_name_817_, lean_object* v_x_818_, lean_object* v_type_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0(v_name_817_, v_x_818_, v_type_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
lean_dec_ref(v_x_818_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport(lean_object* v_name_828_, lean_object* v_c_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_){
_start:
{
lean_object* v___x_835_; lean_object* v_env_836_; uint8_t v___x_837_; 
v___x_835_ = lean_st_ref_get(v_a_833_);
v_env_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc_ref(v_env_836_);
lean_dec(v___x_835_);
lean_inc(v_name_828_);
v___x_837_ = l_Lean_Linter_isDeprecated(v_env_836_, v_name_828_);
if (v___x_837_ == 0)
{
uint8_t v___x_838_; 
lean_inc(v_name_828_);
v___x_838_ = l_Lean_Name_isMetaprogramming(v_name_828_);
if (v___x_838_ == 0)
{
lean_object* v___x_839_; lean_object* v_type_840_; lean_object* v___f_841_; lean_object* v___x_842_; 
v___x_839_ = l_Lean_AsyncConstantInfo_toConstantVal(v_c_829_);
v_type_840_ = lean_ctor_get(v___x_839_, 2);
lean_inc_ref(v_type_840_);
lean_dec_ref(v___x_839_);
v___f_841_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___boxed), 8, 1);
lean_closure_set(v___f_841_, 0, v_name_828_);
v___x_842_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(v_type_840_, v___f_841_, v___x_838_, v_a_830_, v_a_831_, v_a_832_, v_a_833_);
return v___x_842_;
}
else
{
lean_object* v___x_843_; lean_object* v___x_844_; 
lean_dec_ref(v_c_829_);
lean_dec(v_name_828_);
v___x_843_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___closed__0));
v___x_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_844_, 0, v___x_843_);
return v___x_844_;
}
}
else
{
lean_object* v___x_845_; lean_object* v___x_846_; 
lean_dec_ref(v_c_829_);
lean_dec(v_name_828_);
v___x_845_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___closed__0));
v___x_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
return v___x_846_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___boxed(lean_object* v_name_847_, lean_object* v_c_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport(v_name_847_, v_c_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_);
lean_dec(v_a_852_);
lean_dec_ref(v_a_851_);
lean_dec(v_a_850_);
lean_dec_ref(v_a_849_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_858108106____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_856_ = lean_box(0);
v___x_857_ = lean_st_mk_ref(v___x_856_);
v___x_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_858108106____hygCtx___hyg_2____boxed(lean_object* v_a_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_858108106____hygCtx___hyg_2_();
return v_res_860_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_constantsPerImportTask(void){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = lean_unsigned_to_nat(6500u);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2955776588____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_888_ = lean_box(0);
v___x_889_ = lean_st_mk_ref(v___x_888_);
v___x_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2955776588____hygCtx___hyg_2____boxed(lean_object* v_a_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2955776588____hygCtx___hyg_2_();
return v_res_892_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__1(void){
_start:
{
lean_object* v_droppedRef_894_; lean_object* v___x_895_; 
v_droppedRef_894_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_starLemmasExt;
v___x_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_895_, 0, v_droppedRef_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_libSearchFindDecls(lean_object* v_ty_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_902_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_ext;
v___x_903_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__0));
v___x_904_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_droppedKeys));
v___x_905_ = lean_unsigned_to_nat(6500u);
v___x_906_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__1, &l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__1_once, _init_l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__1);
v___x_907_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v___x_902_, v___x_903_, v___x_904_, v___x_905_, v___x_906_, v_ty_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_libSearchFindDecls___boxed(lean_object* v_ty_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_Meta_LibrarySearch_libSearchFindDecls(v_ty_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
return v_res_914_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2(void){
_start:
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_918_ = lean_box(0);
v___x_919_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_getStarLemmas___closed__1));
v___x_920_ = l_Lean_mkConst(v___x_919_, v___x_918_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_getStarLemmas(lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
lean_object* v_ref_928_; lean_object* v___x_929_; 
v_ref_928_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_starLemmasExt;
v___x_929_ = lean_st_ref_get(v_ref_928_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2, &l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2_once, _init_l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2);
v___x_931_ = l_Lean_Meta_LibrarySearch_libSearchFindDecls(v___x_930_, v_a_923_, v_a_924_, v_a_925_, v_a_926_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_944_; 
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_944_ == 0)
{
lean_object* v_unused_945_; 
v_unused_945_ = lean_ctor_get(v___x_931_, 0);
lean_dec(v_unused_945_);
v___x_933_ = v___x_931_;
v_isShared_934_ = v_isSharedCheck_944_;
goto v_resetjp_932_;
}
else
{
lean_dec(v___x_931_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_944_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_935_; 
v___x_935_ = lean_st_ref_get(v_ref_928_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_936_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_getStarLemmas___closed__3));
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_936_);
v___x_938_ = v___x_933_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
else
{
lean_object* v_val_940_; lean_object* v___x_942_; 
v_val_940_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_val_940_);
lean_dec_ref_known(v___x_935_, 1);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v_val_940_);
v___x_942_ = v___x_933_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_val_940_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
else
{
return v___x_931_;
}
}
else
{
lean_object* v_val_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
v_val_946_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_929_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_val_946_);
lean_dec(v___x_929_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
lean_ctor_set_tag(v___x_948_, 0);
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_val_946_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_getStarLemmas___boxed(lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v_a_954_, v_a_955_, v_a_956_, v_a_957_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0(uint8_t v___x_960_, lean_object* v___x_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
if (v___x_960_ == 0)
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_getRemainingHeartbeats___redArg(v___y_964_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_977_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_977_ == 0)
{
v___x_970_ = v___x_967_;
v_isShared_971_ = v_isSharedCheck_977_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_967_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_977_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
uint8_t v___x_972_; lean_object* v___x_973_; lean_object* v___x_975_; 
v___x_972_ = lean_nat_dec_lt(v_a_968_, v___x_961_);
lean_dec(v_a_968_);
v___x_973_ = lean_box(v___x_972_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v___x_973_);
v___x_975_ = v___x_970_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
else
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
v_a_978_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_967_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_967_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
else
{
uint8_t v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_986_ = 0;
v___x_987_ = lean_box(v___x_986_);
v___x_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
return v___x_988_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0___boxed(lean_object* v___x_989_, lean_object* v___x_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
uint8_t v___x_643__boxed_996_; lean_object* v_res_997_; 
v___x_643__boxed_996_ = lean_unbox(v___x_989_);
v_res_997_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0(v___x_643__boxed_996_, v___x_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___x_990_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(lean_object* v_leavePercent_998_, lean_object* v_a_999_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Lean_getMaxHeartbeats___redArg(v_a_999_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1003_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1002_);
lean_dec_ref_known(v___x_1001_, 1);
v___x_1003_ = l_Lean_getRemainingHeartbeats___redArg(v_a_999_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1018_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1006_ = v___x_1003_;
v_isShared_1007_ = v_isSharedCheck_1018_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_1003_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1018_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; lean_object* v___x_1013_; lean_object* v___y_1014_; lean_object* v___x_1016_; 
v___x_1008_ = lean_nat_mul(v_a_1004_, v_leavePercent_998_);
lean_dec(v_a_1004_);
v___x_1009_ = lean_unsigned_to_nat(100u);
v___x_1010_ = lean_nat_div(v___x_1008_, v___x_1009_);
lean_dec(v___x_1008_);
v___x_1011_ = lean_unsigned_to_nat(0u);
v___x_1012_ = lean_nat_dec_eq(v_a_1002_, v___x_1011_);
lean_dec(v_a_1002_);
v___x_1013_ = lean_box(v___x_1012_);
v___y_1014_ = lean_alloc_closure((void*)(l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___y_1014_, 0, v___x_1013_);
lean_closure_set(v___y_1014_, 1, v___x_1010_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v___y_1014_);
v___x_1016_ = v___x_1006_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___y_1014_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec(v_a_1002_);
v_a_1019_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_1003_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1003_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
v_a_1027_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_1001_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1001_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___boxed(lean_object* v_leavePercent_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercent_1035_, v_a_1036_);
lean_dec_ref(v_a_1036_);
lean_dec(v_leavePercent_1035_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck(lean_object* v_leavePercent_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercent_1039_, v_a_1042_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___boxed(lean_object* v_leavePercent_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck(v_leavePercent_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_);
lean_dec(v_a_1050_);
lean_dec_ref(v_a_1049_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
lean_dec(v_leavePercent_1046_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(lean_object* v_upperBound_1053_, lean_object* v_x_1054_, lean_object* v_f_1055_, lean_object* v_y_1056_, lean_object* v_g_1057_, lean_object* v_a_1058_, lean_object* v_b_1059_){
_start:
{
uint8_t v___x_1060_; 
v___x_1060_ = lean_nat_dec_lt(v_a_1058_, v_upperBound_1053_);
if (v___x_1060_ == 0)
{
lean_dec(v_a_1058_);
lean_dec(v_g_1057_);
lean_dec(v_f_1055_);
return v_b_1059_;
}
else
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1061_ = lean_array_fget_borrowed(v_x_1054_, v_a_1058_);
lean_inc(v_f_1055_);
lean_inc(v___x_1061_);
v___x_1062_ = lean_apply_1(v_f_1055_, v___x_1061_);
v___x_1063_ = lean_array_push(v_b_1059_, v___x_1062_);
v___x_1064_ = lean_array_fget_borrowed(v_y_1056_, v_a_1058_);
lean_inc(v_g_1057_);
lean_inc(v___x_1064_);
v___x_1065_ = lean_apply_1(v_g_1057_, v___x_1064_);
v___x_1066_ = lean_array_push(v___x_1063_, v___x_1065_);
v___x_1067_ = lean_unsigned_to_nat(1u);
v___x_1068_ = lean_nat_add(v_a_1058_, v___x_1067_);
lean_dec(v_a_1058_);
v_a_1058_ = v___x_1068_;
v_b_1059_ = v___x_1066_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg___boxed(lean_object* v_upperBound_1070_, lean_object* v_x_1071_, lean_object* v_f_1072_, lean_object* v_y_1073_, lean_object* v_g_1074_, lean_object* v_a_1075_, lean_object* v_b_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(v_upperBound_1070_, v_x_1071_, v_f_1072_, v_y_1073_, v_g_1074_, v_a_1075_, v_b_1076_);
lean_dec_ref(v_y_1073_);
lean_dec_ref(v_x_1071_);
lean_dec(v_upperBound_1070_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(lean_object* v_g_1078_, size_t v_sz_1079_, size_t v_i_1080_, lean_object* v_bs_1081_){
_start:
{
uint8_t v___x_1082_; 
v___x_1082_ = lean_usize_dec_lt(v_i_1080_, v_sz_1079_);
if (v___x_1082_ == 0)
{
lean_dec(v_g_1078_);
return v_bs_1081_;
}
else
{
lean_object* v_v_1083_; lean_object* v___x_1084_; lean_object* v_bs_x27_1085_; lean_object* v___x_1086_; size_t v___x_1087_; size_t v___x_1088_; lean_object* v___x_1089_; 
v_v_1083_ = lean_array_uget(v_bs_1081_, v_i_1080_);
v___x_1084_ = lean_unsigned_to_nat(0u);
v_bs_x27_1085_ = lean_array_uset(v_bs_1081_, v_i_1080_, v___x_1084_);
lean_inc(v_g_1078_);
v___x_1086_ = lean_apply_1(v_g_1078_, v_v_1083_);
v___x_1087_ = ((size_t)1ULL);
v___x_1088_ = lean_usize_add(v_i_1080_, v___x_1087_);
v___x_1089_ = lean_array_uset(v_bs_x27_1085_, v_i_1080_, v___x_1086_);
v_i_1080_ = v___x_1088_;
v_bs_1081_ = v___x_1089_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg___boxed(lean_object* v_g_1091_, lean_object* v_sz_1092_, lean_object* v_i_1093_, lean_object* v_bs_1094_){
_start:
{
size_t v_sz_boxed_1095_; size_t v_i_boxed_1096_; lean_object* v_res_1097_; 
v_sz_boxed_1095_ = lean_unbox_usize(v_sz_1092_);
lean_dec(v_sz_1092_);
v_i_boxed_1096_ = lean_unbox_usize(v_i_1093_);
lean_dec(v_i_1093_);
v_res_1097_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_g_1091_, v_sz_boxed_1095_, v_i_boxed_1096_, v_bs_1094_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith___redArg(lean_object* v_f_1098_, lean_object* v_x_1099_, lean_object* v_g_1100_, lean_object* v_y_1101_){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v_res_1105_; lean_object* v___y_1107_; uint8_t v___x_1121_; 
v___x_1102_ = lean_array_get_size(v_x_1099_);
v___x_1103_ = lean_array_get_size(v_y_1101_);
v___x_1104_ = lean_nat_add(v___x_1102_, v___x_1103_);
v_res_1105_ = lean_mk_empty_array_with_capacity(v___x_1104_);
lean_dec(v___x_1104_);
v___x_1121_ = lean_nat_dec_le(v___x_1102_, v___x_1103_);
if (v___x_1121_ == 0)
{
v___y_1107_ = v___x_1103_;
goto v___jp_1106_;
}
else
{
v___y_1107_ = v___x_1102_;
goto v___jp_1106_;
}
v___jp_1106_:
{
uint8_t v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1108_ = lean_nat_dec_lt(v___y_1107_, v___x_1102_);
v___x_1109_ = lean_unsigned_to_nat(0u);
lean_inc(v_g_1100_);
lean_inc(v_f_1098_);
v___x_1110_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(v___y_1107_, v_x_1099_, v_f_1098_, v_y_1101_, v_g_1100_, v___x_1109_, v_res_1105_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1111_; size_t v_sz_1112_; size_t v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
lean_dec(v_f_1098_);
v___x_1111_ = l_Array_extract___redArg(v_y_1101_, v___y_1107_, v___x_1103_);
v_sz_1112_ = lean_array_size(v___x_1111_);
v___x_1113_ = ((size_t)0ULL);
v___x_1114_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_g_1100_, v_sz_1112_, v___x_1113_, v___x_1111_);
v___x_1115_ = l_Array_append___redArg(v___x_1110_, v___x_1114_);
lean_dec_ref(v___x_1114_);
return v___x_1115_;
}
else
{
lean_object* v___x_1116_; size_t v_sz_1117_; size_t v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
lean_dec(v_g_1100_);
v___x_1116_ = l_Array_extract___redArg(v_x_1099_, v___y_1107_, v___x_1102_);
v_sz_1117_ = lean_array_size(v___x_1116_);
v___x_1118_ = ((size_t)0ULL);
v___x_1119_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_f_1098_, v_sz_1117_, v___x_1118_, v___x_1116_);
v___x_1120_ = l_Array_append___redArg(v___x_1110_, v___x_1119_);
lean_dec_ref(v___x_1119_);
return v___x_1120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith___redArg___boxed(lean_object* v_f_1122_, lean_object* v_x_1123_, lean_object* v_g_1124_, lean_object* v_y_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Lean_Meta_LibrarySearch_interleaveWith___redArg(v_f_1122_, v_x_1123_, v_g_1124_, v_y_1125_);
lean_dec_ref(v_y_1125_);
lean_dec_ref(v_x_1123_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith(lean_object* v_00_u03b1_1127_, lean_object* v_00_u03b2_1128_, lean_object* v_00_u03b3_1129_, lean_object* v_f_1130_, lean_object* v_x_1131_, lean_object* v_g_1132_, lean_object* v_y_1133_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Lean_Meta_LibrarySearch_interleaveWith___redArg(v_f_1130_, v_x_1131_, v_g_1132_, v_y_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith___boxed(lean_object* v_00_u03b1_1135_, lean_object* v_00_u03b2_1136_, lean_object* v_00_u03b3_1137_, lean_object* v_f_1138_, lean_object* v_x_1139_, lean_object* v_g_1140_, lean_object* v_y_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Lean_Meta_LibrarySearch_interleaveWith(v_00_u03b1_1135_, v_00_u03b2_1136_, v_00_u03b3_1137_, v_f_1138_, v_x_1139_, v_g_1140_, v_y_1141_);
lean_dec_ref(v_y_1141_);
lean_dec_ref(v_x_1139_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0(lean_object* v_00_u03b2_1143_, lean_object* v_00_u03b3_1144_, lean_object* v_g_1145_, size_t v_sz_1146_, size_t v_i_1147_, lean_object* v_bs_1148_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_g_1145_, v_sz_1146_, v_i_1147_, v_bs_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___boxed(lean_object* v_00_u03b2_1150_, lean_object* v_00_u03b3_1151_, lean_object* v_g_1152_, lean_object* v_sz_1153_, lean_object* v_i_1154_, lean_object* v_bs_1155_){
_start:
{
size_t v_sz_boxed_1156_; size_t v_i_boxed_1157_; lean_object* v_res_1158_; 
v_sz_boxed_1156_ = lean_unbox_usize(v_sz_1153_);
lean_dec(v_sz_1153_);
v_i_boxed_1157_ = lean_unbox_usize(v_i_1154_);
lean_dec(v_i_1154_);
v_res_1158_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0(v_00_u03b2_1150_, v_00_u03b3_1151_, v_g_1152_, v_sz_boxed_1156_, v_i_boxed_1157_, v_bs_1155_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1(lean_object* v_00_u03b3_1159_, lean_object* v_upperBound_1160_, lean_object* v_00_u03b1_1161_, lean_object* v_x_1162_, lean_object* v_f_1163_, lean_object* v_00_u03b2_1164_, lean_object* v_y_1165_, lean_object* v_g_1166_, lean_object* v_inst_1167_, lean_object* v_R_1168_, lean_object* v_a_1169_, lean_object* v_b_1170_, lean_object* v_c_1171_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(v_upperBound_1160_, v_x_1162_, v_f_1163_, v_y_1165_, v_g_1166_, v_a_1169_, v_b_1170_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___boxed(lean_object* v_00_u03b3_1173_, lean_object* v_upperBound_1174_, lean_object* v_00_u03b1_1175_, lean_object* v_x_1176_, lean_object* v_f_1177_, lean_object* v_00_u03b2_1178_, lean_object* v_y_1179_, lean_object* v_g_1180_, lean_object* v_inst_1181_, lean_object* v_R_1182_, lean_object* v_a_1183_, lean_object* v_b_1184_, lean_object* v_c_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1(v_00_u03b3_1173_, v_upperBound_1174_, v_00_u03b1_1175_, v_x_1176_, v_f_1177_, v_00_u03b2_1178_, v_y_1179_, v_g_1180_, v_inst_1181_, v_R_1182_, v_a_1183_, v_b_1184_, v_c_1185_);
lean_dec_ref(v_y_1179_);
lean_dec_ref(v_x_1176_);
lean_dec(v_upperBound_1174_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_));
v___x_1195_ = l_Lean_registerInternalExceptionId(v___x_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2____boxed(lean_object* v_a_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_();
return v_res_1197_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0(void){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1198_ = lean_box(0);
v___x_1199_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_abortSpeculationId;
v___x_1200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
lean_ctor_set(v___x_1200_, 1, v___x_1198_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___redArg(lean_object* v_inst_1201_){
_start:
{
lean_object* v_throw_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v_throw_1202_ = lean_ctor_get(v_inst_1201_, 0);
lean_inc(v_throw_1202_);
lean_dec_ref(v_inst_1201_);
v___x_1203_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0, &l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0_once, _init_l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0);
v___x_1204_ = lean_apply_2(v_throw_1202_, lean_box(0), v___x_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation(lean_object* v_m_1205_, lean_object* v_00_u03b1_1206_, lean_object* v_inst_1207_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = l_Lean_Meta_LibrarySearch_abortSpeculation___redArg(v_inst_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_isAbortSpeculation(lean_object* v_x_1209_){
_start:
{
if (lean_obj_tag(v_x_1209_) == 1)
{
lean_object* v_id_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; 
v_id_1210_ = lean_ctor_get(v_x_1209_, 0);
v___x_1211_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_abortSpeculationId;
v___x_1212_ = l_Lean_instBEqInternalExceptionId_beq(v_id_1210_, v___x_1211_);
return v___x_1212_;
}
else
{
uint8_t v___x_1213_; 
v___x_1213_ = 0;
return v___x_1213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_isAbortSpeculation___boxed(lean_object* v_x_1214_){
_start:
{
uint8_t v_res_1215_; lean_object* v_r_1216_; 
v_res_1215_ = l_Lean_Meta_LibrarySearch_isAbortSpeculation(v_x_1214_);
lean_dec_ref(v_x_1214_);
v_r_1216_ = lean_box(v_res_1215_);
return v_r_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(lean_object* v_x_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v___x_1223_; 
v___x_1223_ = l_Lean_Meta_saveState___redArg(v___y_1219_, v___y_1221_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v_a_1224_; lean_object* v___x_1225_; 
v_a_1224_ = lean_ctor_get(v___x_1223_, 0);
lean_inc(v_a_1224_);
lean_dec_ref_known(v___x_1223_, 1);
lean_inc(v___y_1221_);
lean_inc_ref(v___y_1220_);
lean_inc(v___y_1219_);
lean_inc_ref(v___y_1218_);
v___x_1225_ = lean_apply_5(v_x_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, lean_box(0));
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1234_; 
lean_dec(v_a_1224_);
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1228_ = v___x_1225_;
v_isShared_1229_ = v_isSharedCheck_1234_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1225_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1234_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1230_; lean_object* v___x_1232_; 
v___x_1230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1230_, 0, v_a_1226_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 0, v___x_1230_);
v___x_1232_ = v___x_1228_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___x_1230_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
else
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1264_; 
v_a_1235_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1237_ = v___x_1225_;
v_isShared_1238_ = v_isSharedCheck_1264_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1225_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1264_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
uint8_t v___y_1240_; uint8_t v___x_1262_; 
v___x_1262_ = l_Lean_Exception_isInterrupt(v_a_1235_);
if (v___x_1262_ == 0)
{
uint8_t v___x_1263_; 
lean_inc(v_a_1235_);
v___x_1263_ = l_Lean_Exception_isRuntime(v_a_1235_);
v___y_1240_ = v___x_1263_;
goto v___jp_1239_;
}
else
{
v___y_1240_ = v___x_1262_;
goto v___jp_1239_;
}
v___jp_1239_:
{
if (v___y_1240_ == 0)
{
lean_object* v___x_1241_; 
lean_del_object(v___x_1237_);
lean_dec(v_a_1235_);
v___x_1241_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1224_, v___y_1219_, v___y_1221_);
lean_dec(v_a_1224_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1249_; 
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1249_ == 0)
{
lean_object* v_unused_1250_; 
v_unused_1250_ = lean_ctor_get(v___x_1241_, 0);
lean_dec(v_unused_1250_);
v___x_1243_ = v___x_1241_;
v_isShared_1244_ = v_isSharedCheck_1249_;
goto v_resetjp_1242_;
}
else
{
lean_dec(v___x_1241_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1249_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1245_; lean_object* v___x_1247_; 
v___x_1245_ = lean_box(0);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v___x_1245_);
v___x_1247_ = v___x_1243_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1245_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
else
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1258_; 
v_a_1251_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1253_ = v___x_1241_;
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1241_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_a_1251_);
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
else
{
lean_object* v___x_1260_; 
lean_dec(v_a_1224_);
if (v_isShared_1238_ == 0)
{
v___x_1260_ = v___x_1237_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_a_1235_);
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
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
lean_dec_ref(v_x_1217_);
v_a_1265_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1223_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1223_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1265_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg___boxed(lean_object* v_x_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(v_x_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0(lean_object* v_00_u03b1_1280_, lean_object* v_x_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v___x_1287_; 
v___x_1287_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(v_x_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___boxed(lean_object* v_00_u03b1_1288_, lean_object* v_x_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0(v_00_u03b1_1288_, v_x_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(lean_object* v_e_1296_, lean_object* v___y_1297_){
_start:
{
uint8_t v___x_1299_; 
v___x_1299_ = l_Lean_Expr_hasMVar(v_e_1296_);
if (v___x_1299_ == 0)
{
lean_object* v___x_1300_; 
v___x_1300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1300_, 0, v_e_1296_);
return v___x_1300_;
}
else
{
lean_object* v___x_1301_; lean_object* v_mctx_1302_; lean_object* v___x_1303_; lean_object* v_fst_1304_; lean_object* v_snd_1305_; lean_object* v___x_1306_; lean_object* v_cache_1307_; lean_object* v_zetaDeltaFVarIds_1308_; lean_object* v_postponed_1309_; lean_object* v_diag_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1319_; 
v___x_1301_ = lean_st_ref_get(v___y_1297_);
v_mctx_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc_ref(v_mctx_1302_);
lean_dec(v___x_1301_);
v___x_1303_ = l_Lean_instantiateMVarsCore(v_mctx_1302_, v_e_1296_);
v_fst_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_fst_1304_);
v_snd_1305_ = lean_ctor_get(v___x_1303_, 1);
lean_inc(v_snd_1305_);
lean_dec_ref(v___x_1303_);
v___x_1306_ = lean_st_ref_take(v___y_1297_);
v_cache_1307_ = lean_ctor_get(v___x_1306_, 1);
v_zetaDeltaFVarIds_1308_ = lean_ctor_get(v___x_1306_, 2);
v_postponed_1309_ = lean_ctor_get(v___x_1306_, 3);
v_diag_1310_ = lean_ctor_get(v___x_1306_, 4);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1319_ == 0)
{
lean_object* v_unused_1320_; 
v_unused_1320_ = lean_ctor_get(v___x_1306_, 0);
lean_dec(v_unused_1320_);
v___x_1312_ = v___x_1306_;
v_isShared_1313_ = v_isSharedCheck_1319_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_diag_1310_);
lean_inc(v_postponed_1309_);
lean_inc(v_zetaDeltaFVarIds_1308_);
lean_inc(v_cache_1307_);
lean_dec(v___x_1306_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1319_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 0, v_snd_1305_);
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_snd_1305_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v_cache_1307_);
lean_ctor_set(v_reuseFailAlloc_1318_, 2, v_zetaDeltaFVarIds_1308_);
lean_ctor_set(v_reuseFailAlloc_1318_, 3, v_postponed_1309_);
lean_ctor_set(v_reuseFailAlloc_1318_, 4, v_diag_1310_);
v___x_1315_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = lean_st_ref_set(v___y_1297_, v___x_1315_);
v___x_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1317_, 0, v_fst_1304_);
return v___x_1317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg___boxed(lean_object* v_e_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(v_e_1321_, v___y_1322_);
lean_dec(v___y_1322_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1(lean_object* v_e_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(v_e_1325_, v___y_1327_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___boxed(lean_object* v_e_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1(v_e_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0(lean_object* v___x_1339_, lean_object* v_x_1340_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1339_);
lean_ctor_set(v___x_1341_, 1, v_x_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(lean_object* v___x_1342_, size_t v_sz_1343_, size_t v_i_1344_, lean_object* v_bs_1345_){
_start:
{
uint8_t v___x_1346_; 
v___x_1346_ = lean_usize_dec_lt(v_i_1344_, v_sz_1343_);
if (v___x_1346_ == 0)
{
lean_dec_ref(v___x_1342_);
return v_bs_1345_;
}
else
{
lean_object* v_v_1347_; lean_object* v___x_1348_; lean_object* v_bs_x27_1349_; lean_object* v___x_1350_; size_t v___x_1351_; size_t v___x_1352_; lean_object* v___x_1353_; 
v_v_1347_ = lean_array_uget(v_bs_1345_, v_i_1344_);
v___x_1348_ = lean_unsigned_to_nat(0u);
v_bs_x27_1349_ = lean_array_uset(v_bs_1345_, v_i_1344_, v___x_1348_);
lean_inc_ref(v___x_1342_);
v___x_1350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1342_);
lean_ctor_set(v___x_1350_, 1, v_v_1347_);
v___x_1351_ = ((size_t)1ULL);
v___x_1352_ = lean_usize_add(v_i_1344_, v___x_1351_);
v___x_1353_ = lean_array_uset(v_bs_x27_1349_, v_i_1344_, v___x_1350_);
v_i_1344_ = v___x_1352_;
v_bs_1345_ = v___x_1353_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2___boxed(lean_object* v___x_1355_, lean_object* v_sz_1356_, lean_object* v_i_1357_, lean_object* v_bs_1358_){
_start:
{
size_t v_sz_boxed_1359_; size_t v_i_boxed_1360_; lean_object* v_res_1361_; 
v_sz_boxed_1359_ = lean_unbox_usize(v_sz_1356_);
lean_dec(v_sz_1356_);
v_i_boxed_1360_ = lean_unbox_usize(v_i_1357_);
lean_dec(v_i_1357_);
v_res_1361_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(v___x_1355_, v_sz_boxed_1359_, v_i_boxed_1360_, v_bs_1358_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearchSymm(lean_object* v_searchFn_1362_, lean_object* v_goal_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_){
_start:
{
lean_object* v___x_1369_; 
lean_inc(v_goal_1363_);
v___x_1369_ = l_Lean_MVarId_getType(v_goal_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; lean_object* v___x_1371_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1370_);
lean_dec_ref_known(v___x_1369_, 1);
lean_inc_ref(v_searchFn_1362_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
v___x_1371_ = lean_apply_6(v_searchFn_1362_, v_a_1370_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, lean_box(0));
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v_a_1372_; lean_object* v___x_1373_; lean_object* v_mctx_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v_a_1372_ = lean_ctor_get(v___x_1371_, 0);
lean_inc(v_a_1372_);
lean_dec_ref_known(v___x_1371_, 1);
v___x_1373_ = lean_st_ref_get(v_a_1365_);
v_mctx_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc_ref_n(v_mctx_1374_, 2);
lean_dec(v___x_1373_);
lean_inc(v_goal_1363_);
v___x_1375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1375_, 0, v_goal_1363_);
lean_ctor_set(v___x_1375_, 1, v_mctx_1374_);
v___x_1376_ = lean_alloc_closure((void*)(l_Lean_MVarId_applySymm___boxed), 6, 1);
lean_closure_set(v___x_1376_, 0, v_goal_1363_);
v___x_1377_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(v___x_1376_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1438_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1380_ = v___x_1377_;
v_isShared_1381_ = v_isSharedCheck_1438_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1377_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1438_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
if (lean_obj_tag(v_a_1378_) == 1)
{
lean_object* v_val_1382_; lean_object* v___x_1383_; 
lean_del_object(v___x_1380_);
v_val_1382_ = lean_ctor_get(v_a_1378_, 0);
lean_inc_n(v_val_1382_, 2);
lean_dec_ref_known(v_a_1378_, 1);
v___x_1383_ = l_Lean_MVarId_getType(v_val_1382_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1385_; lean_object* v_a_1386_; lean_object* v___x_1387_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
lean_dec_ref_known(v___x_1383_, 1);
v___x_1385_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(v_a_1384_, v_a_1365_);
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_a_1386_);
lean_dec_ref(v___x_1385_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
v___x_1387_ = lean_apply_6(v_searchFn_1362_, v_a_1386_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, lean_box(0));
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1415_; 
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1390_ = v___x_1387_;
v_isShared_1391_ = v_isSharedCheck_1415_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1387_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1415_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v_cache_1394_; lean_object* v_zetaDeltaFVarIds_1395_; lean_object* v_postponed_1396_; lean_object* v_diag_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1413_; 
v___x_1392_ = lean_st_ref_get(v_a_1365_);
v___x_1393_ = lean_st_ref_take(v_a_1365_);
v_cache_1394_ = lean_ctor_get(v___x_1393_, 1);
v_zetaDeltaFVarIds_1395_ = lean_ctor_get(v___x_1393_, 2);
v_postponed_1396_ = lean_ctor_get(v___x_1393_, 3);
v_diag_1397_ = lean_ctor_get(v___x_1393_, 4);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1413_ == 0)
{
lean_object* v_unused_1414_; 
v_unused_1414_ = lean_ctor_get(v___x_1393_, 0);
lean_dec(v_unused_1414_);
v___x_1399_ = v___x_1393_;
v_isShared_1400_ = v_isSharedCheck_1413_;
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
v_isShared_1400_ = v_isSharedCheck_1413_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 0, v_mctx_1374_);
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_mctx_1374_);
lean_ctor_set(v_reuseFailAlloc_1412_, 1, v_cache_1394_);
lean_ctor_set(v_reuseFailAlloc_1412_, 2, v_zetaDeltaFVarIds_1395_);
lean_ctor_set(v_reuseFailAlloc_1412_, 3, v_postponed_1396_);
lean_ctor_set(v_reuseFailAlloc_1412_, 4, v_diag_1397_);
v___x_1402_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
lean_object* v___x_1403_; lean_object* v_mctx_1404_; lean_object* v___f_1405_; lean_object* v___x_1406_; lean_object* v___f_1407_; lean_object* v___x_1408_; lean_object* v___x_1410_; 
v___x_1403_ = lean_st_ref_set(v_a_1365_, v___x_1402_);
v_mctx_1404_ = lean_ctor_get(v___x_1392_, 0);
lean_inc_ref(v_mctx_1404_);
lean_dec(v___x_1392_);
v___f_1405_ = lean_alloc_closure((void*)(l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0), 2, 1);
lean_closure_set(v___f_1405_, 0, v___x_1375_);
v___x_1406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1406_, 0, v_val_1382_);
lean_ctor_set(v___x_1406_, 1, v_mctx_1404_);
v___f_1407_ = lean_alloc_closure((void*)(l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0), 2, 1);
lean_closure_set(v___f_1407_, 0, v___x_1406_);
v___x_1408_ = l_Lean_Meta_LibrarySearch_interleaveWith___redArg(v___f_1405_, v_a_1372_, v___f_1407_, v_a_1388_);
lean_dec(v_a_1388_);
lean_dec(v_a_1372_);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 0, v___x_1408_);
v___x_1410_ = v___x_1390_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1408_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
else
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
lean_dec(v_val_1382_);
lean_dec_ref_known(v___x_1375_, 2);
lean_dec_ref(v_mctx_1374_);
lean_dec(v_a_1372_);
v_a_1416_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1418_ = v___x_1387_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1387_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
else
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1431_; 
lean_dec(v_val_1382_);
lean_dec_ref_known(v___x_1375_, 2);
lean_dec_ref(v_mctx_1374_);
lean_dec(v_a_1372_);
lean_dec_ref(v_searchFn_1362_);
v_a_1424_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1426_ = v___x_1383_;
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1383_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1427_ == 0)
{
v___x_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_a_1424_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
else
{
size_t v_sz_1432_; size_t v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1436_; 
lean_dec(v_a_1378_);
lean_dec_ref(v_mctx_1374_);
lean_dec_ref(v_searchFn_1362_);
v_sz_1432_ = lean_array_size(v_a_1372_);
v___x_1433_ = ((size_t)0ULL);
v___x_1434_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(v___x_1375_, v_sz_1432_, v___x_1433_, v_a_1372_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 0, v___x_1434_);
v___x_1436_ = v___x_1380_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
lean_dec_ref_known(v___x_1375_, 2);
lean_dec_ref(v_mctx_1374_);
lean_dec(v_a_1372_);
lean_dec_ref(v_searchFn_1362_);
v_a_1439_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1377_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1377_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_dec(v_goal_1363_);
lean_dec_ref(v_searchFn_1362_);
v_a_1447_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1371_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1371_);
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
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
lean_dec(v_goal_1363_);
lean_dec_ref(v_searchFn_1362_);
v_a_1455_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1369_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1369_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearchSymm___boxed(lean_object* v_searchFn_1463_, lean_object* v_goal_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v_searchFn_1463_, v_goal_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
lean_dec(v_a_1468_);
lean_dec_ref(v_a_1467_);
lean_dec(v_a_1466_);
lean_dec_ref(v_a_1465_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0(lean_object* v_e_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1481_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___closed__1));
v___x_1482_ = lean_unsigned_to_nat(1u);
v___x_1483_ = lean_mk_empty_array_with_capacity(v___x_1482_);
v___x_1484_ = lean_array_push(v___x_1483_, v_e_1475_);
v___x_1485_ = l_Lean_Meta_mkAppM(v___x_1481_, v___x_1484_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___boxed(lean_object* v_e_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0(v_e_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1(lean_object* v_e_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1503_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___closed__1));
v___x_1504_ = lean_unsigned_to_nat(1u);
v___x_1505_ = lean_mk_empty_array_with_capacity(v___x_1504_);
v___x_1506_ = lean_array_push(v___x_1505_, v_e_1497_);
v___x_1507_ = l_Lean_Meta_mkAppM(v___x_1503_, v___x_1506_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___boxed(lean_object* v_e_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1(v_e_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(lean_object* v_lem_1517_, uint8_t v_mod_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_){
_start:
{
lean_object* v___x_1524_; 
v___x_1524_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_lem_1517_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_);
if (lean_obj_tag(v___x_1524_) == 0)
{
switch(v_mod_1518_)
{
case 0:
{
return v___x_1524_;
}
case 1:
{
lean_object* v_a_1525_; lean_object* v___f_1526_; lean_object* v___x_1527_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1525_);
lean_dec_ref_known(v___x_1524_, 1);
v___f_1526_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__0));
v___x_1527_ = l_Lean_Meta_mapForallTelescope(v___f_1526_, v_a_1525_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_);
return v___x_1527_;
}
default: 
{
lean_object* v_a_1528_; lean_object* v___f_1529_; lean_object* v___x_1530_; 
v_a_1528_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1528_);
lean_dec_ref_known(v___x_1524_, 1);
v___f_1529_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__1));
v___x_1530_ = l_Lean_Meta_mapForallTelescope(v___f_1529_, v_a_1528_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_);
return v___x_1530_;
}
}
}
else
{
return v___x_1524_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___boxed(lean_object* v_lem_1531_, lean_object* v_mod_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_){
_start:
{
uint8_t v_mod_boxed_1538_; lean_object* v_res_1539_; 
v_mod_boxed_1538_ = lean_unbox(v_mod_1532_);
v_res_1539_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_lem_1531_, v_mod_boxed_1538_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
lean_dec(v_a_1536_);
lean_dec_ref(v_a_1535_);
lean_dec(v_a_1534_);
lean_dec_ref(v_a_1533_);
return v_res_1539_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar(lean_object* v_e_1540_){
_start:
{
switch(lean_obj_tag(v_e_1540_))
{
case 0:
{
uint8_t v___x_1541_; 
v___x_1541_ = 1;
return v___x_1541_;
}
case 1:
{
uint8_t v___x_1542_; 
v___x_1542_ = 1;
return v___x_1542_;
}
case 2:
{
uint8_t v___x_1543_; 
v___x_1543_ = 1;
return v___x_1543_;
}
default: 
{
uint8_t v___x_1544_; 
v___x_1544_ = 0;
return v___x_1544_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar___boxed(lean_object* v_e_1545_){
_start:
{
uint8_t v_res_1546_; lean_object* v_r_1547_; 
v_res_1546_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar(v_e_1545_);
lean_dec_ref(v_e_1545_);
v_r_1547_ = lean_box(v_res_1546_);
return v_r_1547_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1548_ = lean_unsigned_to_nat(32u);
v___x_1549_ = lean_mk_empty_array_with_capacity(v___x_1548_);
v___x_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
return v___x_1550_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1551_ = ((size_t)5ULL);
v___x_1552_ = lean_unsigned_to_nat(0u);
v___x_1553_ = lean_unsigned_to_nat(32u);
v___x_1554_ = lean_mk_empty_array_with_capacity(v___x_1553_);
v___x_1555_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0);
v___x_1556_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
lean_ctor_set(v___x_1556_, 1, v___x_1554_);
lean_ctor_set(v___x_1556_, 2, v___x_1552_);
lean_ctor_set(v___x_1556_, 3, v___x_1552_);
lean_ctor_set_usize(v___x_1556_, 4, v___x_1551_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(lean_object* v___y_1557_){
_start:
{
lean_object* v___x_1559_; lean_object* v_traceState_1560_; lean_object* v_traces_1561_; lean_object* v___x_1562_; lean_object* v_traceState_1563_; lean_object* v_env_1564_; lean_object* v_nextMacroScope_1565_; lean_object* v_ngen_1566_; lean_object* v_auxDeclNGen_1567_; lean_object* v_cache_1568_; lean_object* v_messages_1569_; lean_object* v_infoState_1570_; lean_object* v_snapshotTasks_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1590_; 
v___x_1559_ = lean_st_ref_get(v___y_1557_);
v_traceState_1560_ = lean_ctor_get(v___x_1559_, 4);
lean_inc_ref(v_traceState_1560_);
lean_dec(v___x_1559_);
v_traces_1561_ = lean_ctor_get(v_traceState_1560_, 0);
lean_inc_ref(v_traces_1561_);
lean_dec_ref(v_traceState_1560_);
v___x_1562_ = lean_st_ref_take(v___y_1557_);
v_traceState_1563_ = lean_ctor_get(v___x_1562_, 4);
v_env_1564_ = lean_ctor_get(v___x_1562_, 0);
v_nextMacroScope_1565_ = lean_ctor_get(v___x_1562_, 1);
v_ngen_1566_ = lean_ctor_get(v___x_1562_, 2);
v_auxDeclNGen_1567_ = lean_ctor_get(v___x_1562_, 3);
v_cache_1568_ = lean_ctor_get(v___x_1562_, 5);
v_messages_1569_ = lean_ctor_get(v___x_1562_, 6);
v_infoState_1570_ = lean_ctor_get(v___x_1562_, 7);
v_snapshotTasks_1571_ = lean_ctor_get(v___x_1562_, 8);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1573_ = v___x_1562_;
v_isShared_1574_ = v_isSharedCheck_1590_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_snapshotTasks_1571_);
lean_inc(v_infoState_1570_);
lean_inc(v_messages_1569_);
lean_inc(v_cache_1568_);
lean_inc(v_traceState_1563_);
lean_inc(v_auxDeclNGen_1567_);
lean_inc(v_ngen_1566_);
lean_inc(v_nextMacroScope_1565_);
lean_inc(v_env_1564_);
lean_dec(v___x_1562_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1590_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
uint64_t v_tid_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1588_; 
v_tid_1575_ = lean_ctor_get_uint64(v_traceState_1563_, sizeof(void*)*1);
v_isSharedCheck_1588_ = !lean_is_exclusive(v_traceState_1563_);
if (v_isSharedCheck_1588_ == 0)
{
lean_object* v_unused_1589_; 
v_unused_1589_ = lean_ctor_get(v_traceState_1563_, 0);
lean_dec(v_unused_1589_);
v___x_1577_ = v_traceState_1563_;
v_isShared_1578_ = v_isSharedCheck_1588_;
goto v_resetjp_1576_;
}
else
{
lean_dec(v_traceState_1563_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1588_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1579_; lean_object* v___x_1581_; 
v___x_1579_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1);
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 0, v___x_1579_);
v___x_1581_ = v___x_1577_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1579_);
lean_ctor_set_uint64(v_reuseFailAlloc_1587_, sizeof(void*)*1, v_tid_1575_);
v___x_1581_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1583_; 
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 4, v___x_1581_);
v___x_1583_ = v___x_1573_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_env_1564_);
lean_ctor_set(v_reuseFailAlloc_1586_, 1, v_nextMacroScope_1565_);
lean_ctor_set(v_reuseFailAlloc_1586_, 2, v_ngen_1566_);
lean_ctor_set(v_reuseFailAlloc_1586_, 3, v_auxDeclNGen_1567_);
lean_ctor_set(v_reuseFailAlloc_1586_, 4, v___x_1581_);
lean_ctor_set(v_reuseFailAlloc_1586_, 5, v_cache_1568_);
lean_ctor_set(v_reuseFailAlloc_1586_, 6, v_messages_1569_);
lean_ctor_set(v_reuseFailAlloc_1586_, 7, v_infoState_1570_);
lean_ctor_set(v_reuseFailAlloc_1586_, 8, v_snapshotTasks_1571_);
v___x_1583_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = lean_st_ref_set(v___y_1557_, v___x_1583_);
v___x_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1585_, 0, v_traces_1561_);
return v___x_1585_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___boxed(lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v___y_1591_);
lean_dec(v___y_1591_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0(lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v___y_1597_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___boxed(lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0(v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
return v_res_1605_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(lean_object* v_opts_1606_, lean_object* v_opt_1607_){
_start:
{
lean_object* v_name_1608_; lean_object* v_defValue_1609_; lean_object* v_map_1610_; lean_object* v___x_1611_; 
v_name_1608_ = lean_ctor_get(v_opt_1607_, 0);
v_defValue_1609_ = lean_ctor_get(v_opt_1607_, 1);
v_map_1610_ = lean_ctor_get(v_opts_1606_, 0);
v___x_1611_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1610_, v_name_1608_);
if (lean_obj_tag(v___x_1611_) == 0)
{
uint8_t v___x_1612_; 
v___x_1612_ = lean_unbox(v_defValue_1609_);
return v___x_1612_;
}
else
{
lean_object* v_val_1613_; 
v_val_1613_ = lean_ctor_get(v___x_1611_, 0);
lean_inc(v_val_1613_);
lean_dec_ref_known(v___x_1611_, 1);
if (lean_obj_tag(v_val_1613_) == 1)
{
uint8_t v_v_1614_; 
v_v_1614_ = lean_ctor_get_uint8(v_val_1613_, 0);
lean_dec_ref_known(v_val_1613_, 0);
return v_v_1614_;
}
else
{
uint8_t v___x_1615_; 
lean_dec(v_val_1613_);
v___x_1615_ = lean_unbox(v_defValue_1609_);
return v___x_1615_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1___boxed(lean_object* v_opts_1616_, lean_object* v_opt_1617_){
_start:
{
uint8_t v_res_1618_; lean_object* v_r_1619_; 
v_res_1618_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_1616_, v_opt_1617_);
lean_dec_ref(v_opt_1617_);
lean_dec_ref(v_opts_1616_);
v_r_1619_ = lean_box(v_res_1618_);
return v_r_1619_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__0));
v___x_1622_ = l_Lean_stringToMessageData(v___x_1621_);
return v___x_1622_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1624_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__2));
v___x_1625_ = l_Lean_stringToMessageData(v___x_1624_);
return v___x_1625_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__5));
v___x_1630_ = l_Lean_MessageData_ofFormat(v___x_1629_);
return v___x_1630_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__8));
v___x_1635_ = l_Lean_MessageData_ofFormat(v___x_1634_);
return v___x_1635_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12(void){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__11));
v___x_1640_ = l_Lean_MessageData_ofFormat(v___x_1639_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0(lean_object* v_fst_1641_, uint8_t v_snd_1642_, lean_object* v_x_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___y_1653_; 
v___x_1649_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1);
v___x_1650_ = l_Lean_MessageData_ofName(v_fst_1641_);
v___x_1651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1649_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
switch(v_snd_1642_)
{
case 0:
{
lean_object* v___x_1658_; 
v___x_1658_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6);
v___y_1653_ = v___x_1658_;
goto v___jp_1652_;
}
case 1:
{
lean_object* v___x_1659_; 
v___x_1659_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9);
v___y_1653_ = v___x_1659_;
goto v___jp_1652_;
}
default: 
{
lean_object* v___x_1660_; 
v___x_1660_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12);
v___y_1653_ = v___x_1660_;
goto v___jp_1652_;
}
}
v___jp_1652_:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
lean_inc_ref(v___y_1653_);
v___x_1654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1651_);
lean_ctor_set(v___x_1654_, 1, v___y_1653_);
v___x_1655_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3);
v___x_1656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1654_);
lean_ctor_set(v___x_1656_, 1, v___x_1655_);
v___x_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1656_);
return v___x_1657_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___boxed(lean_object* v_fst_1661_, lean_object* v_snd_1662_, lean_object* v_x_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
uint8_t v_snd_11696__boxed_1669_; lean_object* v_res_1670_; 
v_snd_11696__boxed_1669_ = lean_unbox(v_snd_1662_);
v_res_1670_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0(v_fst_1661_, v_snd_11696__boxed_1669_, v_x_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec_ref(v_x_1663_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(lean_object* v_opts_1671_, lean_object* v_opt_1672_){
_start:
{
lean_object* v_name_1673_; lean_object* v_defValue_1674_; lean_object* v_map_1675_; lean_object* v___x_1676_; 
v_name_1673_ = lean_ctor_get(v_opt_1672_, 0);
v_defValue_1674_ = lean_ctor_get(v_opt_1672_, 1);
v_map_1675_ = lean_ctor_get(v_opts_1671_, 0);
v___x_1676_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1675_, v_name_1673_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_inc(v_defValue_1674_);
return v_defValue_1674_;
}
else
{
lean_object* v_val_1677_; 
v_val_1677_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_val_1677_);
lean_dec_ref_known(v___x_1676_, 1);
if (lean_obj_tag(v_val_1677_) == 3)
{
lean_object* v_v_1678_; 
v_v_1678_ = lean_ctor_get(v_val_1677_, 0);
lean_inc(v_v_1678_);
lean_dec_ref_known(v_val_1677_, 1);
return v_v_1678_;
}
else
{
lean_dec(v_val_1677_);
lean_inc(v_defValue_1674_);
return v_defValue_1674_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5___boxed(lean_object* v_opts_1679_, lean_object* v_opt_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_1679_, v_opt_1680_);
lean_dec_ref(v_opt_1680_);
lean_dec_ref(v_opts_1679_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(lean_object* v_x_1682_){
_start:
{
if (lean_obj_tag(v_x_1682_) == 0)
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1691_; 
v_a_1684_ = lean_ctor_get(v_x_1682_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v_x_1682_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1686_ = v_x_1682_;
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v_x_1682_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1689_; 
if (v_isShared_1687_ == 0)
{
lean_ctor_set_tag(v___x_1686_, 1);
v___x_1689_ = v___x_1686_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_a_1684_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
else
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1699_; 
v_a_1692_ = lean_ctor_get(v_x_1682_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v_x_1682_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1694_ = v_x_1682_;
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v_x_1682_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1697_; 
if (v_isShared_1695_ == 0)
{
lean_ctor_set_tag(v___x_1694_, 0);
v___x_1697_ = v___x_1694_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_a_1692_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg___boxed(lean_object* v_x_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_x_1700_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3(size_t v_sz_1703_, size_t v_i_1704_, lean_object* v_bs_1705_){
_start:
{
uint8_t v___x_1706_; 
v___x_1706_ = lean_usize_dec_lt(v_i_1704_, v_sz_1703_);
if (v___x_1706_ == 0)
{
return v_bs_1705_;
}
else
{
lean_object* v_v_1707_; lean_object* v_msg_1708_; lean_object* v___x_1709_; lean_object* v_bs_x27_1710_; size_t v___x_1711_; size_t v___x_1712_; lean_object* v___x_1713_; 
v_v_1707_ = lean_array_uget_borrowed(v_bs_1705_, v_i_1704_);
v_msg_1708_ = lean_ctor_get(v_v_1707_, 1);
lean_inc_ref(v_msg_1708_);
v___x_1709_ = lean_unsigned_to_nat(0u);
v_bs_x27_1710_ = lean_array_uset(v_bs_1705_, v_i_1704_, v___x_1709_);
v___x_1711_ = ((size_t)1ULL);
v___x_1712_ = lean_usize_add(v_i_1704_, v___x_1711_);
v___x_1713_ = lean_array_uset(v_bs_x27_1710_, v_i_1704_, v_msg_1708_);
v_i_1704_ = v___x_1712_;
v_bs_1705_ = v___x_1713_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_1715_, lean_object* v_i_1716_, lean_object* v_bs_1717_){
_start:
{
size_t v_sz_boxed_1718_; size_t v_i_boxed_1719_; lean_object* v_res_1720_; 
v_sz_boxed_1718_ = lean_unbox_usize(v_sz_1715_);
lean_dec(v_sz_1715_);
v_i_boxed_1719_ = lean_unbox_usize(v_i_1716_);
lean_dec(v_i_1716_);
v_res_1720_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3(v_sz_boxed_1718_, v_i_boxed_1719_, v_bs_1717_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(lean_object* v_oldTraces_1721_, lean_object* v_data_1722_, lean_object* v_ref_1723_, lean_object* v_msg_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v_fileName_1730_; lean_object* v_fileMap_1731_; lean_object* v_options_1732_; lean_object* v_currRecDepth_1733_; lean_object* v_maxRecDepth_1734_; lean_object* v_ref_1735_; lean_object* v_currNamespace_1736_; lean_object* v_openDecls_1737_; lean_object* v_initHeartbeats_1738_; lean_object* v_maxHeartbeats_1739_; lean_object* v_quotContext_1740_; lean_object* v_currMacroScope_1741_; uint8_t v_diag_1742_; lean_object* v_cancelTk_x3f_1743_; uint8_t v_suppressElabErrors_1744_; lean_object* v_inheritedTraceOptions_1745_; lean_object* v___x_1746_; lean_object* v_traceState_1747_; lean_object* v_traces_1748_; lean_object* v_ref_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; size_t v_sz_1752_; size_t v___x_1753_; lean_object* v___x_1754_; lean_object* v_msg_1755_; lean_object* v___x_1756_; lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1794_; 
v_fileName_1730_ = lean_ctor_get(v___y_1727_, 0);
v_fileMap_1731_ = lean_ctor_get(v___y_1727_, 1);
v_options_1732_ = lean_ctor_get(v___y_1727_, 2);
v_currRecDepth_1733_ = lean_ctor_get(v___y_1727_, 3);
v_maxRecDepth_1734_ = lean_ctor_get(v___y_1727_, 4);
v_ref_1735_ = lean_ctor_get(v___y_1727_, 5);
v_currNamespace_1736_ = lean_ctor_get(v___y_1727_, 6);
v_openDecls_1737_ = lean_ctor_get(v___y_1727_, 7);
v_initHeartbeats_1738_ = lean_ctor_get(v___y_1727_, 8);
v_maxHeartbeats_1739_ = lean_ctor_get(v___y_1727_, 9);
v_quotContext_1740_ = lean_ctor_get(v___y_1727_, 10);
v_currMacroScope_1741_ = lean_ctor_get(v___y_1727_, 11);
v_diag_1742_ = lean_ctor_get_uint8(v___y_1727_, sizeof(void*)*14);
v_cancelTk_x3f_1743_ = lean_ctor_get(v___y_1727_, 12);
v_suppressElabErrors_1744_ = lean_ctor_get_uint8(v___y_1727_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1745_ = lean_ctor_get(v___y_1727_, 13);
v___x_1746_ = lean_st_ref_get(v___y_1728_);
v_traceState_1747_ = lean_ctor_get(v___x_1746_, 4);
lean_inc_ref(v_traceState_1747_);
lean_dec(v___x_1746_);
v_traces_1748_ = lean_ctor_get(v_traceState_1747_, 0);
lean_inc_ref(v_traces_1748_);
lean_dec_ref(v_traceState_1747_);
v_ref_1749_ = l_Lean_replaceRef(v_ref_1723_, v_ref_1735_);
lean_inc_ref(v_inheritedTraceOptions_1745_);
lean_inc(v_cancelTk_x3f_1743_);
lean_inc(v_currMacroScope_1741_);
lean_inc(v_quotContext_1740_);
lean_inc(v_maxHeartbeats_1739_);
lean_inc(v_initHeartbeats_1738_);
lean_inc(v_openDecls_1737_);
lean_inc(v_currNamespace_1736_);
lean_inc(v_maxRecDepth_1734_);
lean_inc(v_currRecDepth_1733_);
lean_inc_ref(v_options_1732_);
lean_inc_ref(v_fileMap_1731_);
lean_inc_ref(v_fileName_1730_);
v___x_1750_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1750_, 0, v_fileName_1730_);
lean_ctor_set(v___x_1750_, 1, v_fileMap_1731_);
lean_ctor_set(v___x_1750_, 2, v_options_1732_);
lean_ctor_set(v___x_1750_, 3, v_currRecDepth_1733_);
lean_ctor_set(v___x_1750_, 4, v_maxRecDepth_1734_);
lean_ctor_set(v___x_1750_, 5, v_ref_1749_);
lean_ctor_set(v___x_1750_, 6, v_currNamespace_1736_);
lean_ctor_set(v___x_1750_, 7, v_openDecls_1737_);
lean_ctor_set(v___x_1750_, 8, v_initHeartbeats_1738_);
lean_ctor_set(v___x_1750_, 9, v_maxHeartbeats_1739_);
lean_ctor_set(v___x_1750_, 10, v_quotContext_1740_);
lean_ctor_set(v___x_1750_, 11, v_currMacroScope_1741_);
lean_ctor_set(v___x_1750_, 12, v_cancelTk_x3f_1743_);
lean_ctor_set(v___x_1750_, 13, v_inheritedTraceOptions_1745_);
lean_ctor_set_uint8(v___x_1750_, sizeof(void*)*14, v_diag_1742_);
lean_ctor_set_uint8(v___x_1750_, sizeof(void*)*14 + 1, v_suppressElabErrors_1744_);
v___x_1751_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1748_);
lean_dec_ref(v_traces_1748_);
v_sz_1752_ = lean_array_size(v___x_1751_);
v___x_1753_ = ((size_t)0ULL);
v___x_1754_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3(v_sz_1752_, v___x_1753_, v___x_1751_);
v_msg_1755_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1755_, 0, v_data_1722_);
lean_ctor_set(v_msg_1755_, 1, v_msg_1724_);
lean_ctor_set(v_msg_1755_, 2, v___x_1754_);
v___x_1756_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(v_msg_1755_, v___y_1725_, v___y_1726_, v___x_1750_, v___y_1728_);
lean_dec_ref_known(v___x_1750_, 14);
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1759_ = v___x_1756_;
v_isShared_1760_ = v_isSharedCheck_1794_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1756_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1794_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1761_; lean_object* v_traceState_1762_; lean_object* v_env_1763_; lean_object* v_nextMacroScope_1764_; lean_object* v_ngen_1765_; lean_object* v_auxDeclNGen_1766_; lean_object* v_cache_1767_; lean_object* v_messages_1768_; lean_object* v_infoState_1769_; lean_object* v_snapshotTasks_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1793_; 
v___x_1761_ = lean_st_ref_take(v___y_1728_);
v_traceState_1762_ = lean_ctor_get(v___x_1761_, 4);
v_env_1763_ = lean_ctor_get(v___x_1761_, 0);
v_nextMacroScope_1764_ = lean_ctor_get(v___x_1761_, 1);
v_ngen_1765_ = lean_ctor_get(v___x_1761_, 2);
v_auxDeclNGen_1766_ = lean_ctor_get(v___x_1761_, 3);
v_cache_1767_ = lean_ctor_get(v___x_1761_, 5);
v_messages_1768_ = lean_ctor_get(v___x_1761_, 6);
v_infoState_1769_ = lean_ctor_get(v___x_1761_, 7);
v_snapshotTasks_1770_ = lean_ctor_get(v___x_1761_, 8);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1772_ = v___x_1761_;
v_isShared_1773_ = v_isSharedCheck_1793_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_snapshotTasks_1770_);
lean_inc(v_infoState_1769_);
lean_inc(v_messages_1768_);
lean_inc(v_cache_1767_);
lean_inc(v_traceState_1762_);
lean_inc(v_auxDeclNGen_1766_);
lean_inc(v_ngen_1765_);
lean_inc(v_nextMacroScope_1764_);
lean_inc(v_env_1763_);
lean_dec(v___x_1761_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1793_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
uint64_t v_tid_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1791_; 
v_tid_1774_ = lean_ctor_get_uint64(v_traceState_1762_, sizeof(void*)*1);
v_isSharedCheck_1791_ = !lean_is_exclusive(v_traceState_1762_);
if (v_isSharedCheck_1791_ == 0)
{
lean_object* v_unused_1792_; 
v_unused_1792_ = lean_ctor_get(v_traceState_1762_, 0);
lean_dec(v_unused_1792_);
v___x_1776_ = v_traceState_1762_;
v_isShared_1777_ = v_isSharedCheck_1791_;
goto v_resetjp_1775_;
}
else
{
lean_dec(v_traceState_1762_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1791_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1778_, 0, v_ref_1723_);
lean_ctor_set(v___x_1778_, 1, v_a_1757_);
v___x_1779_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1721_, v___x_1778_);
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v___x_1779_);
v___x_1781_ = v___x_1776_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1779_);
lean_ctor_set_uint64(v_reuseFailAlloc_1790_, sizeof(void*)*1, v_tid_1774_);
v___x_1781_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1783_; 
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 4, v___x_1781_);
v___x_1783_ = v___x_1772_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_env_1763_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v_nextMacroScope_1764_);
lean_ctor_set(v_reuseFailAlloc_1789_, 2, v_ngen_1765_);
lean_ctor_set(v_reuseFailAlloc_1789_, 3, v_auxDeclNGen_1766_);
lean_ctor_set(v_reuseFailAlloc_1789_, 4, v___x_1781_);
lean_ctor_set(v_reuseFailAlloc_1789_, 5, v_cache_1767_);
lean_ctor_set(v_reuseFailAlloc_1789_, 6, v_messages_1768_);
lean_ctor_set(v_reuseFailAlloc_1789_, 7, v_infoState_1769_);
lean_ctor_set(v_reuseFailAlloc_1789_, 8, v_snapshotTasks_1770_);
v___x_1783_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1787_; 
v___x_1784_ = lean_st_ref_set(v___y_1728_, v___x_1783_);
v___x_1785_ = lean_box(0);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 0, v___x_1785_);
v___x_1787_ = v___x_1759_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1785_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2___boxed(lean_object* v_oldTraces_1795_, lean_object* v_data_1796_, lean_object* v_ref_1797_, lean_object* v_msg_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(v_oldTraces_1795_, v_data_1796_, v_ref_1797_, v_msg_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
return v_res_1804_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(lean_object* v_e_1805_){
_start:
{
if (lean_obj_tag(v_e_1805_) == 0)
{
uint8_t v___x_1806_; 
v___x_1806_ = 2;
return v___x_1806_;
}
else
{
uint8_t v___x_1807_; 
v___x_1807_ = 0;
return v___x_1807_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4___boxed(lean_object* v_e_1808_){
_start:
{
uint8_t v_res_1809_; lean_object* v_r_1810_; 
v_res_1809_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(v_e_1808_);
lean_dec_ref(v_e_1808_);
v_r_1810_ = lean_box(v_res_1809_);
return v_r_1810_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1811_; double v___x_1812_; 
v___x_1811_ = lean_unsigned_to_nat(0u);
v___x_1812_ = lean_float_of_nat(v___x_1811_);
return v___x_1812_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1814_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__1));
v___x_1815_ = l_Lean_stringToMessageData(v___x_1814_);
return v___x_1815_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1816_; double v___x_1817_; 
v___x_1816_ = lean_unsigned_to_nat(1000u);
v___x_1817_ = lean_float_of_nat(v___x_1816_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(lean_object* v_cls_1818_, uint8_t v_collapsed_1819_, lean_object* v_tag_1820_, lean_object* v_opts_1821_, uint8_t v_clsEnabled_1822_, lean_object* v_oldTraces_1823_, lean_object* v_msg_1824_, lean_object* v_resStartStop_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v_fst_1831_; lean_object* v_snd_1832_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v_data_1836_; lean_object* v_fst_1847_; lean_object* v_snd_1848_; lean_object* v___x_1849_; uint8_t v___x_1850_; lean_object* v___y_1852_; lean_object* v_a_1853_; uint8_t v___y_1868_; double v___y_1899_; 
v_fst_1831_ = lean_ctor_get(v_resStartStop_1825_, 0);
lean_inc(v_fst_1831_);
v_snd_1832_ = lean_ctor_get(v_resStartStop_1825_, 1);
lean_inc(v_snd_1832_);
lean_dec_ref(v_resStartStop_1825_);
v_fst_1847_ = lean_ctor_get(v_snd_1832_, 0);
lean_inc(v_fst_1847_);
v_snd_1848_ = lean_ctor_get(v_snd_1832_, 1);
lean_inc(v_snd_1848_);
lean_dec(v_snd_1832_);
v___x_1849_ = l_Lean_trace_profiler;
v___x_1850_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_1821_, v___x_1849_);
if (v___x_1850_ == 0)
{
v___y_1868_ = v___x_1850_;
goto v___jp_1867_;
}
else
{
lean_object* v___x_1904_; uint8_t v___x_1905_; 
v___x_1904_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1905_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_1821_, v___x_1904_);
if (v___x_1905_ == 0)
{
lean_object* v___x_1906_; lean_object* v___x_1907_; double v___x_1908_; double v___x_1909_; double v___x_1910_; 
v___x_1906_ = l_Lean_trace_profiler_threshold;
v___x_1907_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_1821_, v___x_1906_);
v___x_1908_ = lean_float_of_nat(v___x_1907_);
v___x_1909_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3);
v___x_1910_ = lean_float_div(v___x_1908_, v___x_1909_);
v___y_1899_ = v___x_1910_;
goto v___jp_1898_;
}
else
{
lean_object* v___x_1911_; lean_object* v___x_1912_; double v___x_1913_; 
v___x_1911_ = l_Lean_trace_profiler_threshold;
v___x_1912_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_1821_, v___x_1911_);
v___x_1913_ = lean_float_of_nat(v___x_1912_);
v___y_1899_ = v___x_1913_;
goto v___jp_1898_;
}
}
v___jp_1833_:
{
lean_object* v___x_1837_; 
lean_inc(v___y_1835_);
v___x_1837_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(v_oldTraces_1823_, v_data_1836_, v___y_1835_, v___y_1834_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v___x_1838_; 
lean_dec_ref_known(v___x_1837_, 1);
v___x_1838_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_1831_);
return v___x_1838_;
}
else
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1846_; 
lean_dec(v_fst_1831_);
v_a_1839_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1841_ = v___x_1837_;
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1837_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1844_; 
if (v_isShared_1842_ == 0)
{
v___x_1844_ = v___x_1841_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1839_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
v___jp_1851_:
{
uint8_t v_result_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; double v___x_1857_; lean_object* v_data_1858_; 
v_result_1854_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(v_fst_1831_);
v___x_1855_ = lean_box(v_result_1854_);
v___x_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
v___x_1857_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0);
lean_inc_ref(v_tag_1820_);
lean_inc_ref(v___x_1856_);
lean_inc(v_cls_1818_);
v_data_1858_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1858_, 0, v_cls_1818_);
lean_ctor_set(v_data_1858_, 1, v___x_1856_);
lean_ctor_set(v_data_1858_, 2, v_tag_1820_);
lean_ctor_set_float(v_data_1858_, sizeof(void*)*3, v___x_1857_);
lean_ctor_set_float(v_data_1858_, sizeof(void*)*3 + 8, v___x_1857_);
lean_ctor_set_uint8(v_data_1858_, sizeof(void*)*3 + 16, v_collapsed_1819_);
if (v___x_1850_ == 0)
{
lean_dec_ref_known(v___x_1856_, 1);
lean_dec(v_snd_1848_);
lean_dec(v_fst_1847_);
lean_dec_ref(v_tag_1820_);
lean_dec(v_cls_1818_);
v___y_1834_ = v_a_1853_;
v___y_1835_ = v___y_1852_;
v_data_1836_ = v_data_1858_;
goto v___jp_1833_;
}
else
{
lean_object* v_data_1859_; double v___x_1860_; double v___x_1861_; 
lean_dec_ref_known(v_data_1858_, 3);
v_data_1859_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1859_, 0, v_cls_1818_);
lean_ctor_set(v_data_1859_, 1, v___x_1856_);
lean_ctor_set(v_data_1859_, 2, v_tag_1820_);
v___x_1860_ = lean_unbox_float(v_fst_1847_);
lean_dec(v_fst_1847_);
lean_ctor_set_float(v_data_1859_, sizeof(void*)*3, v___x_1860_);
v___x_1861_ = lean_unbox_float(v_snd_1848_);
lean_dec(v_snd_1848_);
lean_ctor_set_float(v_data_1859_, sizeof(void*)*3 + 8, v___x_1861_);
lean_ctor_set_uint8(v_data_1859_, sizeof(void*)*3 + 16, v_collapsed_1819_);
v___y_1834_ = v_a_1853_;
v___y_1835_ = v___y_1852_;
v_data_1836_ = v_data_1859_;
goto v___jp_1833_;
}
}
v___jp_1862_:
{
lean_object* v_ref_1863_; lean_object* v___x_1864_; 
v_ref_1863_ = lean_ctor_get(v___y_1828_, 5);
lean_inc(v___y_1829_);
lean_inc_ref(v___y_1828_);
lean_inc(v___y_1827_);
lean_inc_ref(v___y_1826_);
lean_inc(v_fst_1831_);
v___x_1864_ = lean_apply_6(v_msg_1824_, v_fst_1831_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, lean_box(0));
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_a_1865_; 
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_a_1865_);
lean_dec_ref_known(v___x_1864_, 1);
v___y_1852_ = v_ref_1863_;
v_a_1853_ = v_a_1865_;
goto v___jp_1851_;
}
else
{
lean_object* v___x_1866_; 
lean_dec_ref_known(v___x_1864_, 1);
v___x_1866_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2);
v___y_1852_ = v_ref_1863_;
v_a_1853_ = v___x_1866_;
goto v___jp_1851_;
}
}
v___jp_1867_:
{
if (v_clsEnabled_1822_ == 0)
{
if (v___y_1868_ == 0)
{
lean_object* v___x_1869_; lean_object* v_traceState_1870_; lean_object* v_env_1871_; lean_object* v_nextMacroScope_1872_; lean_object* v_ngen_1873_; lean_object* v_auxDeclNGen_1874_; lean_object* v_cache_1875_; lean_object* v_messages_1876_; lean_object* v_infoState_1877_; lean_object* v_snapshotTasks_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1897_; 
lean_dec(v_snd_1848_);
lean_dec(v_fst_1847_);
lean_dec_ref(v_msg_1824_);
lean_dec_ref(v_tag_1820_);
lean_dec(v_cls_1818_);
v___x_1869_ = lean_st_ref_take(v___y_1829_);
v_traceState_1870_ = lean_ctor_get(v___x_1869_, 4);
v_env_1871_ = lean_ctor_get(v___x_1869_, 0);
v_nextMacroScope_1872_ = lean_ctor_get(v___x_1869_, 1);
v_ngen_1873_ = lean_ctor_get(v___x_1869_, 2);
v_auxDeclNGen_1874_ = lean_ctor_get(v___x_1869_, 3);
v_cache_1875_ = lean_ctor_get(v___x_1869_, 5);
v_messages_1876_ = lean_ctor_get(v___x_1869_, 6);
v_infoState_1877_ = lean_ctor_get(v___x_1869_, 7);
v_snapshotTasks_1878_ = lean_ctor_get(v___x_1869_, 8);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1880_ = v___x_1869_;
v_isShared_1881_ = v_isSharedCheck_1897_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_snapshotTasks_1878_);
lean_inc(v_infoState_1877_);
lean_inc(v_messages_1876_);
lean_inc(v_cache_1875_);
lean_inc(v_traceState_1870_);
lean_inc(v_auxDeclNGen_1874_);
lean_inc(v_ngen_1873_);
lean_inc(v_nextMacroScope_1872_);
lean_inc(v_env_1871_);
lean_dec(v___x_1869_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1897_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
uint64_t v_tid_1882_; lean_object* v_traces_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1896_; 
v_tid_1882_ = lean_ctor_get_uint64(v_traceState_1870_, sizeof(void*)*1);
v_traces_1883_ = lean_ctor_get(v_traceState_1870_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v_traceState_1870_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1885_ = v_traceState_1870_;
v_isShared_1886_ = v_isSharedCheck_1896_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_traces_1883_);
lean_dec(v_traceState_1870_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1896_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1887_; lean_object* v___x_1889_; 
v___x_1887_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1823_, v_traces_1883_);
lean_dec_ref(v_traces_1883_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v___x_1887_);
v___x_1889_ = v___x_1885_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1887_);
lean_ctor_set_uint64(v_reuseFailAlloc_1895_, sizeof(void*)*1, v_tid_1882_);
v___x_1889_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
lean_object* v___x_1891_; 
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 4, v___x_1889_);
v___x_1891_ = v___x_1880_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_env_1871_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_nextMacroScope_1872_);
lean_ctor_set(v_reuseFailAlloc_1894_, 2, v_ngen_1873_);
lean_ctor_set(v_reuseFailAlloc_1894_, 3, v_auxDeclNGen_1874_);
lean_ctor_set(v_reuseFailAlloc_1894_, 4, v___x_1889_);
lean_ctor_set(v_reuseFailAlloc_1894_, 5, v_cache_1875_);
lean_ctor_set(v_reuseFailAlloc_1894_, 6, v_messages_1876_);
lean_ctor_set(v_reuseFailAlloc_1894_, 7, v_infoState_1877_);
lean_ctor_set(v_reuseFailAlloc_1894_, 8, v_snapshotTasks_1878_);
v___x_1891_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1892_ = lean_st_ref_set(v___y_1829_, v___x_1891_);
v___x_1893_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_1831_);
return v___x_1893_;
}
}
}
}
}
else
{
goto v___jp_1862_;
}
}
else
{
goto v___jp_1862_;
}
}
v___jp_1898_:
{
double v___x_1900_; double v___x_1901_; double v___x_1902_; uint8_t v___x_1903_; 
v___x_1900_ = lean_unbox_float(v_snd_1848_);
v___x_1901_ = lean_unbox_float(v_fst_1847_);
v___x_1902_ = lean_float_sub(v___x_1900_, v___x_1901_);
v___x_1903_ = lean_float_decLt(v___y_1899_, v___x_1902_);
v___y_1868_ = v___x_1903_;
goto v___jp_1867_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___boxed(lean_object* v_cls_1914_, lean_object* v_collapsed_1915_, lean_object* v_tag_1916_, lean_object* v_opts_1917_, lean_object* v_clsEnabled_1918_, lean_object* v_oldTraces_1919_, lean_object* v_msg_1920_, lean_object* v_resStartStop_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
uint8_t v_collapsed_boxed_1927_; uint8_t v_clsEnabled_boxed_1928_; lean_object* v_res_1929_; 
v_collapsed_boxed_1927_ = lean_unbox(v_collapsed_1915_);
v_clsEnabled_boxed_1928_ = lean_unbox(v_clsEnabled_1918_);
v_res_1929_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v_cls_1914_, v_collapsed_boxed_1927_, v_tag_1916_, v_opts_1917_, v_clsEnabled_boxed_1928_, v_oldTraces_1919_, v_msg_1920_, v_resStartStop_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec_ref(v_opts_1917_);
return v_res_1929_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2(void){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1933_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_1934_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__1));
v___x_1935_ = l_Lean_Name_append(v___x_1934_, v___x_1933_);
return v___x_1935_;
}
}
static double _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3(void){
_start:
{
lean_object* v___x_1936_; double v___x_1937_; 
v___x_1936_ = lean_unsigned_to_nat(1000000000u);
v___x_1937_ = lean_float_of_nat(v___x_1936_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(lean_object* v_cfg_1938_, lean_object* v_act_1939_, lean_object* v_allowFailure_1940_, lean_object* v_cand_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_){
_start:
{
lean_object* v_fst_1947_; lean_object* v_snd_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_2234_; 
v_fst_1947_ = lean_ctor_get(v_cand_1941_, 0);
v_snd_1948_ = lean_ctor_get(v_cand_1941_, 1);
v_isSharedCheck_2234_ = !lean_is_exclusive(v_cand_1941_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_1950_ = v_cand_1941_;
v_isShared_1951_ = v_isSharedCheck_2234_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_snd_1948_);
lean_inc(v_fst_1947_);
lean_dec(v_cand_1941_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_2234_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v_options_1952_; uint8_t v_hasTrace_1953_; 
v_options_1952_ = lean_ctor_get(v_a_1944_, 2);
v_hasTrace_1953_ = lean_ctor_get_uint8(v_options_1952_, sizeof(void*)*1);
if (v_hasTrace_1953_ == 0)
{
lean_object* v_fst_1954_; lean_object* v_snd_1955_; lean_object* v_fst_1956_; lean_object* v_snd_1957_; lean_object* v___x_1958_; lean_object* v_cache_1959_; lean_object* v_zetaDeltaFVarIds_1960_; lean_object* v_postponed_1961_; lean_object* v_diag_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_2010_; 
lean_del_object(v___x_1950_);
v_fst_1954_ = lean_ctor_get(v_fst_1947_, 0);
lean_inc(v_fst_1954_);
v_snd_1955_ = lean_ctor_get(v_fst_1947_, 1);
lean_inc(v_snd_1955_);
lean_dec(v_fst_1947_);
v_fst_1956_ = lean_ctor_get(v_snd_1948_, 0);
lean_inc(v_fst_1956_);
v_snd_1957_ = lean_ctor_get(v_snd_1948_, 1);
lean_inc(v_snd_1957_);
lean_dec(v_snd_1948_);
v___x_1958_ = lean_st_ref_take(v_a_1943_);
v_cache_1959_ = lean_ctor_get(v___x_1958_, 1);
v_zetaDeltaFVarIds_1960_ = lean_ctor_get(v___x_1958_, 2);
v_postponed_1961_ = lean_ctor_get(v___x_1958_, 3);
v_diag_1962_ = lean_ctor_get(v___x_1958_, 4);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_2010_ == 0)
{
lean_object* v_unused_2011_; 
v_unused_2011_ = lean_ctor_get(v___x_1958_, 0);
lean_dec(v_unused_2011_);
v___x_1964_ = v___x_1958_;
v_isShared_1965_ = v_isSharedCheck_2010_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_diag_1962_);
lean_inc(v_postponed_1961_);
lean_inc(v_zetaDeltaFVarIds_1960_);
lean_inc(v_cache_1959_);
lean_dec(v___x_1958_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_2010_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 0, v_snd_1955_);
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_snd_1955_);
lean_ctor_set(v_reuseFailAlloc_2009_, 1, v_cache_1959_);
lean_ctor_set(v_reuseFailAlloc_2009_, 2, v_zetaDeltaFVarIds_1960_);
lean_ctor_set(v_reuseFailAlloc_2009_, 3, v_postponed_1961_);
lean_ctor_set(v_reuseFailAlloc_2009_, 4, v_diag_1962_);
v___x_1967_ = v_reuseFailAlloc_2009_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
lean_object* v___x_1968_; uint8_t v___x_1969_; lean_object* v___x_1970_; 
v___x_1968_ = lean_st_ref_set(v_a_1943_, v___x_1967_);
v___x_1969_ = lean_unbox(v_snd_1957_);
lean_dec(v_snd_1957_);
v___x_1970_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_1956_, v___x_1969_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
lean_inc(v_a_1971_);
lean_dec_ref_known(v___x_1970_, 1);
v___x_1972_ = lean_box(0);
lean_inc(v_fst_1954_);
v___x_1973_ = l_Lean_MVarId_apply(v_fst_1954_, v_a_1971_, v_cfg_1938_, v___x_1972_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v___x_1975_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
lean_inc_n(v_a_1974_, 2);
lean_dec_ref_known(v___x_1973_, 1);
lean_inc(v_a_1945_);
lean_inc_ref(v_a_1944_);
lean_inc(v_a_1943_);
lean_inc_ref(v_a_1942_);
v___x_1975_ = lean_apply_6(v_act_1939_, v_a_1974_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, lean_box(0));
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_dec(v_a_1974_);
lean_dec(v_fst_1954_);
lean_dec_ref(v_allowFailure_1940_);
return v___x_1975_;
}
else
{
lean_object* v_a_1976_; uint8_t v___y_1978_; uint8_t v___x_1999_; 
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
lean_inc(v_a_1976_);
v___x_1999_ = l_Lean_Exception_isInterrupt(v_a_1976_);
if (v___x_1999_ == 0)
{
uint8_t v___x_2000_; 
v___x_2000_ = l_Lean_Exception_isRuntime(v_a_1976_);
v___y_1978_ = v___x_2000_;
goto v___jp_1977_;
}
else
{
lean_dec(v_a_1976_);
v___y_1978_ = v___x_1999_;
goto v___jp_1977_;
}
v___jp_1977_:
{
if (v___y_1978_ == 0)
{
lean_object* v___x_1979_; 
lean_dec_ref_known(v___x_1975_, 1);
lean_inc(v_a_1945_);
lean_inc_ref(v_a_1944_);
lean_inc(v_a_1943_);
lean_inc_ref(v_a_1942_);
v___x_1979_ = lean_apply_6(v_allowFailure_1940_, v_fst_1954_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, lean_box(0));
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1990_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1982_ = v___x_1979_;
v_isShared_1983_ = v_isSharedCheck_1990_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1990_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
uint8_t v___x_1984_; 
v___x_1984_ = lean_unbox(v_a_1980_);
lean_dec(v_a_1980_);
if (v___x_1984_ == 0)
{
lean_object* v___x_1985_; lean_object* v___x_1986_; 
lean_del_object(v___x_1982_);
lean_dec(v_a_1974_);
v___x_1985_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1);
v___x_1986_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_1985_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
return v___x_1986_;
}
else
{
lean_object* v___x_1988_; 
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v_a_1974_);
v___x_1988_ = v___x_1982_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1974_);
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
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_1998_; 
lean_dec(v_a_1974_);
v_a_1991_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1993_ = v___x_1979_;
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1979_);
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
else
{
lean_dec(v_a_1974_);
lean_dec(v_fst_1954_);
lean_dec_ref(v_allowFailure_1940_);
return v___x_1975_;
}
}
}
}
else
{
lean_dec(v_fst_1954_);
lean_dec_ref(v_allowFailure_1940_);
lean_dec_ref(v_act_1939_);
return v___x_1973_;
}
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
lean_dec(v_fst_1954_);
lean_dec_ref(v_allowFailure_1940_);
lean_dec_ref(v_act_1939_);
lean_dec_ref(v_cfg_1938_);
v_a_2001_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_1970_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_1970_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
}
}
else
{
lean_object* v_fst_2012_; lean_object* v_snd_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2233_; 
v_fst_2012_ = lean_ctor_get(v_fst_1947_, 0);
v_snd_2013_ = lean_ctor_get(v_fst_1947_, 1);
v_isSharedCheck_2233_ = !lean_is_exclusive(v_fst_1947_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2015_ = v_fst_1947_;
v_isShared_2016_ = v_isSharedCheck_2233_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_snd_2013_);
lean_inc(v_fst_2012_);
lean_dec(v_fst_1947_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2233_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v_fst_2017_; lean_object* v_snd_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2232_; 
v_fst_2017_ = lean_ctor_get(v_snd_1948_, 0);
v_snd_2018_ = lean_ctor_get(v_snd_1948_, 1);
v_isSharedCheck_2232_ = !lean_is_exclusive(v_snd_1948_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2020_ = v_snd_1948_;
v_isShared_2021_ = v_isSharedCheck_2232_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_snd_2018_);
lean_inc(v_fst_2017_);
lean_dec(v_snd_1948_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2232_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v_inheritedTraceOptions_2022_; lean_object* v___f_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; uint8_t v___x_2027_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v_a_2031_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v_a_2050_; lean_object* v___y_2053_; lean_object* v___y_2054_; lean_object* v_a_2055_; lean_object* v___y_2058_; lean_object* v___y_2059_; lean_object* v___y_2060_; lean_object* v___y_2064_; lean_object* v___y_2065_; lean_object* v___y_2066_; lean_object* v___y_2067_; uint8_t v___y_2068_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v_a_2078_; lean_object* v___y_2090_; lean_object* v___y_2091_; lean_object* v_a_2092_; lean_object* v___y_2095_; lean_object* v___y_2096_; lean_object* v_a_2097_; lean_object* v___y_2100_; lean_object* v___y_2101_; lean_object* v___y_2102_; lean_object* v___y_2106_; lean_object* v___y_2107_; lean_object* v___y_2108_; lean_object* v___y_2109_; uint8_t v___y_2110_; 
v_inheritedTraceOptions_2022_ = lean_ctor_get(v_a_1944_, 13);
lean_inc(v_snd_2018_);
lean_inc(v_fst_2017_);
v___f_2023_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2023_, 0, v_fst_2017_);
lean_closure_set(v___f_2023_, 1, v_snd_2018_);
v___x_2024_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_2025_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__4));
v___x_2026_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2);
v___x_2027_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2022_, v_options_1952_, v___x_2026_);
if (v___x_2027_ == 0)
{
lean_object* v___x_2176_; uint8_t v___x_2177_; 
v___x_2176_ = l_Lean_trace_profiler;
v___x_2177_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_1952_, v___x_2176_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; lean_object* v_cache_2179_; lean_object* v_zetaDeltaFVarIds_2180_; lean_object* v_postponed_2181_; lean_object* v_diag_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2230_; 
lean_dec_ref(v___f_2023_);
lean_del_object(v___x_2020_);
lean_del_object(v___x_2015_);
lean_del_object(v___x_1950_);
v___x_2178_ = lean_st_ref_take(v_a_1943_);
v_cache_2179_ = lean_ctor_get(v___x_2178_, 1);
v_zetaDeltaFVarIds_2180_ = lean_ctor_get(v___x_2178_, 2);
v_postponed_2181_ = lean_ctor_get(v___x_2178_, 3);
v_diag_2182_ = lean_ctor_get(v___x_2178_, 4);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2230_ == 0)
{
lean_object* v_unused_2231_; 
v_unused_2231_ = lean_ctor_get(v___x_2178_, 0);
lean_dec(v_unused_2231_);
v___x_2184_ = v___x_2178_;
v_isShared_2185_ = v_isSharedCheck_2230_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_diag_2182_);
lean_inc(v_postponed_2181_);
lean_inc(v_zetaDeltaFVarIds_2180_);
lean_inc(v_cache_2179_);
lean_dec(v___x_2178_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2230_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
lean_ctor_set(v___x_2184_, 0, v_snd_2013_);
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_snd_2013_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v_cache_2179_);
lean_ctor_set(v_reuseFailAlloc_2229_, 2, v_zetaDeltaFVarIds_2180_);
lean_ctor_set(v_reuseFailAlloc_2229_, 3, v_postponed_2181_);
lean_ctor_set(v_reuseFailAlloc_2229_, 4, v_diag_2182_);
v___x_2187_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
lean_object* v___x_2188_; uint8_t v___x_2189_; lean_object* v___x_2190_; 
v___x_2188_ = lean_st_ref_set(v_a_1943_, v___x_2187_);
v___x_2189_ = lean_unbox(v_snd_2018_);
lean_dec(v_snd_2018_);
v___x_2190_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_2017_, v___x_2189_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_a_2191_);
lean_dec_ref_known(v___x_2190_, 1);
v___x_2192_ = lean_box(0);
lean_inc(v_fst_2012_);
v___x_2193_ = l_Lean_MVarId_apply(v_fst_2012_, v_a_2191_, v_cfg_1938_, v___x_2192_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; lean_object* v___x_2195_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
lean_inc_n(v_a_2194_, 2);
lean_dec_ref_known(v___x_2193_, 1);
lean_inc(v_a_1945_);
lean_inc_ref(v_a_1944_);
lean_inc(v_a_1943_);
lean_inc_ref(v_a_1942_);
v___x_2195_ = lean_apply_6(v_act_1939_, v_a_2194_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, lean_box(0));
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_dec(v_a_2194_);
lean_dec(v_fst_2012_);
lean_dec_ref(v_allowFailure_1940_);
return v___x_2195_;
}
else
{
lean_object* v_a_2196_; uint8_t v___y_2198_; uint8_t v___x_2219_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2196_);
v___x_2219_ = l_Lean_Exception_isInterrupt(v_a_2196_);
if (v___x_2219_ == 0)
{
uint8_t v___x_2220_; 
v___x_2220_ = l_Lean_Exception_isRuntime(v_a_2196_);
v___y_2198_ = v___x_2220_;
goto v___jp_2197_;
}
else
{
lean_dec(v_a_2196_);
v___y_2198_ = v___x_2219_;
goto v___jp_2197_;
}
v___jp_2197_:
{
if (v___y_2198_ == 0)
{
lean_object* v___x_2199_; 
lean_dec_ref_known(v___x_2195_, 1);
lean_inc(v_a_1945_);
lean_inc_ref(v_a_1944_);
lean_inc(v_a_1943_);
lean_inc_ref(v_a_1942_);
v___x_2199_ = lean_apply_6(v_allowFailure_1940_, v_fst_2012_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, lean_box(0));
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2210_; 
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2202_ = v___x_2199_;
v_isShared_2203_ = v_isSharedCheck_2210_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2199_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2210_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
uint8_t v___x_2204_; 
v___x_2204_ = lean_unbox(v_a_2200_);
lean_dec(v_a_2200_);
if (v___x_2204_ == 0)
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
lean_del_object(v___x_2202_);
lean_dec(v_a_2194_);
v___x_2205_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1);
v___x_2206_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2205_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
return v___x_2206_;
}
else
{
lean_object* v___x_2208_; 
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 0, v_a_2194_);
v___x_2208_ = v___x_2202_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2194_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
lean_dec(v_a_2194_);
v_a_2211_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___x_2199_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2199_);
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
else
{
lean_dec(v_a_2194_);
lean_dec(v_fst_2012_);
lean_dec_ref(v_allowFailure_1940_);
return v___x_2195_;
}
}
}
}
else
{
lean_dec(v_fst_2012_);
lean_dec_ref(v_allowFailure_1940_);
lean_dec_ref(v_act_1939_);
return v___x_2193_;
}
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2228_; 
lean_dec(v_fst_2012_);
lean_dec_ref(v_allowFailure_1940_);
lean_dec_ref(v_act_1939_);
lean_dec_ref(v_cfg_1938_);
v_a_2221_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2223_ = v___x_2190_;
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2190_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2221_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
}
}
else
{
goto v___jp_2117_;
}
}
else
{
goto v___jp_2117_;
}
v___jp_2028_:
{
lean_object* v___x_2032_; double v___x_2033_; double v___x_2034_; double v___x_2035_; double v___x_2036_; double v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2041_; 
v___x_2032_ = lean_io_mono_nanos_now();
v___x_2033_ = lean_float_of_nat(v___y_2030_);
v___x_2034_ = lean_float_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3);
v___x_2035_ = lean_float_div(v___x_2033_, v___x_2034_);
v___x_2036_ = lean_float_of_nat(v___x_2032_);
v___x_2037_ = lean_float_div(v___x_2036_, v___x_2034_);
v___x_2038_ = lean_box_float(v___x_2035_);
v___x_2039_ = lean_box_float(v___x_2037_);
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 1, v___x_2039_);
lean_ctor_set(v___x_2020_, 0, v___x_2038_);
v___x_2041_ = v___x_2020_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2046_, 1, v___x_2039_);
v___x_2041_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
lean_object* v___x_2043_; 
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 1, v___x_2041_);
lean_ctor_set(v___x_2015_, 0, v_a_2031_);
v___x_2043_ = v___x_2015_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2031_);
lean_ctor_set(v_reuseFailAlloc_2045_, 1, v___x_2041_);
v___x_2043_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
lean_object* v___x_2044_; 
v___x_2044_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v___x_2024_, v_hasTrace_1953_, v___x_2025_, v_options_1952_, v___x_2027_, v___y_2029_, v___f_2023_, v___x_2043_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
return v___x_2044_;
}
}
}
v___jp_2047_:
{
lean_object* v___x_2051_; 
v___x_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2051_, 0, v_a_2050_);
v___y_2029_ = v___y_2048_;
v___y_2030_ = v___y_2049_;
v_a_2031_ = v___x_2051_;
goto v___jp_2028_;
}
v___jp_2052_:
{
lean_object* v___x_2056_; 
v___x_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2056_, 0, v_a_2055_);
v___y_2029_ = v___y_2053_;
v___y_2030_ = v___y_2054_;
v_a_2031_ = v___x_2056_;
goto v___jp_2028_;
}
v___jp_2057_:
{
if (lean_obj_tag(v___y_2060_) == 0)
{
lean_object* v_a_2061_; 
v_a_2061_ = lean_ctor_get(v___y_2060_, 0);
lean_inc(v_a_2061_);
lean_dec_ref_known(v___y_2060_, 1);
v___y_2048_ = v___y_2058_;
v___y_2049_ = v___y_2059_;
v_a_2050_ = v_a_2061_;
goto v___jp_2047_;
}
else
{
lean_object* v_a_2062_; 
v_a_2062_ = lean_ctor_get(v___y_2060_, 0);
lean_inc(v_a_2062_);
lean_dec_ref_known(v___y_2060_, 1);
v___y_2053_ = v___y_2058_;
v___y_2054_ = v___y_2059_;
v_a_2055_ = v_a_2062_;
goto v___jp_2052_;
}
}
v___jp_2063_:
{
if (v___y_2068_ == 0)
{
lean_object* v___x_2069_; 
lean_dec_ref(v___y_2066_);
lean_inc(v_a_1945_);
lean_inc_ref(v_a_1944_);
lean_inc(v_a_1943_);
lean_inc_ref(v_a_1942_);
v___x_2069_ = lean_apply_6(v_allowFailure_1940_, v_fst_2012_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, lean_box(0));
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_a_2070_; uint8_t v___x_2071_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_a_2070_);
lean_dec_ref_known(v___x_2069_, 1);
v___x_2071_ = lean_unbox(v_a_2070_);
lean_dec(v_a_2070_);
if (v___x_2071_ == 0)
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
lean_dec(v___y_2067_);
v___x_2072_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1);
v___x_2073_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2072_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
v___y_2058_ = v___y_2064_;
v___y_2059_ = v___y_2065_;
v___y_2060_ = v___x_2073_;
goto v___jp_2057_;
}
else
{
v___y_2048_ = v___y_2064_;
v___y_2049_ = v___y_2065_;
v_a_2050_ = v___y_2067_;
goto v___jp_2047_;
}
}
else
{
lean_object* v_a_2074_; 
lean_dec(v___y_2067_);
v_a_2074_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_a_2074_);
lean_dec_ref_known(v___x_2069_, 1);
v___y_2053_ = v___y_2064_;
v___y_2054_ = v___y_2065_;
v_a_2055_ = v_a_2074_;
goto v___jp_2052_;
}
}
else
{
lean_dec(v___y_2067_);
lean_dec(v_fst_2012_);
lean_dec_ref(v_allowFailure_1940_);
v___y_2053_ = v___y_2064_;
v___y_2054_ = v___y_2065_;
v_a_2055_ = v___y_2066_;
goto v___jp_2052_;
}
}
v___jp_2075_:
{
lean_object* v___x_2079_; double v___x_2080_; double v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2085_; 
v___x_2079_ = lean_io_get_num_heartbeats();
v___x_2080_ = lean_float_of_nat(v___y_2077_);
v___x_2081_ = lean_float_of_nat(v___x_2079_);
v___x_2082_ = lean_box_float(v___x_2080_);
v___x_2083_ = lean_box_float(v___x_2081_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 1, v___x_2083_);
lean_ctor_set(v___x_1950_, 0, v___x_2082_);
v___x_2085_ = v___x_1950_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2082_);
lean_ctor_set(v_reuseFailAlloc_2088_, 1, v___x_2083_);
v___x_2085_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2086_, 0, v_a_2078_);
lean_ctor_set(v___x_2086_, 1, v___x_2085_);
v___x_2087_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v___x_2024_, v_hasTrace_1953_, v___x_2025_, v_options_1952_, v___x_2027_, v___y_2076_, v___f_2023_, v___x_2086_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
return v___x_2087_;
}
}
v___jp_2089_:
{
lean_object* v___x_2093_; 
v___x_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2093_, 0, v_a_2092_);
v___y_2076_ = v___y_2090_;
v___y_2077_ = v___y_2091_;
v_a_2078_ = v___x_2093_;
goto v___jp_2075_;
}
v___jp_2094_:
{
lean_object* v___x_2098_; 
v___x_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2098_, 0, v_a_2097_);
v___y_2076_ = v___y_2095_;
v___y_2077_ = v___y_2096_;
v_a_2078_ = v___x_2098_;
goto v___jp_2075_;
}
v___jp_2099_:
{
if (lean_obj_tag(v___y_2102_) == 0)
{
lean_object* v_a_2103_; 
v_a_2103_ = lean_ctor_get(v___y_2102_, 0);
lean_inc(v_a_2103_);
lean_dec_ref_known(v___y_2102_, 1);
v___y_2090_ = v___y_2100_;
v___y_2091_ = v___y_2101_;
v_a_2092_ = v_a_2103_;
goto v___jp_2089_;
}
else
{
lean_object* v_a_2104_; 
v_a_2104_ = lean_ctor_get(v___y_2102_, 0);
lean_inc(v_a_2104_);
lean_dec_ref_known(v___y_2102_, 1);
v___y_2095_ = v___y_2100_;
v___y_2096_ = v___y_2101_;
v_a_2097_ = v_a_2104_;
goto v___jp_2094_;
}
}
v___jp_2105_:
{
if (v___y_2110_ == 0)
{
lean_object* v___x_2111_; 
lean_dec_ref(v___y_2106_);
lean_inc(v_a_1945_);
lean_inc_ref(v_a_1944_);
lean_inc(v_a_1943_);
lean_inc_ref(v_a_1942_);
v___x_2111_ = lean_apply_6(v_allowFailure_1940_, v_fst_2012_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, lean_box(0));
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; uint8_t v___x_2113_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_a_2112_);
lean_dec_ref_known(v___x_2111_, 1);
v___x_2113_ = lean_unbox(v_a_2112_);
lean_dec(v_a_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
lean_dec(v___y_2109_);
v___x_2114_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1);
v___x_2115_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2114_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
v___y_2100_ = v___y_2107_;
v___y_2101_ = v___y_2108_;
v___y_2102_ = v___x_2115_;
goto v___jp_2099_;
}
else
{
v___y_2090_ = v___y_2107_;
v___y_2091_ = v___y_2108_;
v_a_2092_ = v___y_2109_;
goto v___jp_2089_;
}
}
else
{
lean_object* v_a_2116_; 
lean_dec(v___y_2109_);
v_a_2116_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_a_2116_);
lean_dec_ref_known(v___x_2111_, 1);
v___y_2095_ = v___y_2107_;
v___y_2096_ = v___y_2108_;
v_a_2097_ = v_a_2116_;
goto v___jp_2094_;
}
}
else
{
lean_dec(v___y_2109_);
lean_dec(v_fst_2012_);
lean_dec_ref(v_allowFailure_1940_);
v___y_2095_ = v___y_2107_;
v___y_2096_ = v___y_2108_;
v_a_2097_ = v___y_2106_;
goto v___jp_2094_;
}
}
v___jp_2117_:
{
lean_object* v___x_2118_; lean_object* v_a_2119_; lean_object* v___x_2120_; uint8_t v___x_2121_; 
v___x_2118_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v_a_1945_);
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2119_);
lean_dec_ref(v___x_2118_);
v___x_2120_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2121_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_1952_, v___x_2120_);
if (v___x_2121_ == 0)
{
lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v_cache_2124_; lean_object* v_zetaDeltaFVarIds_2125_; lean_object* v_postponed_2126_; lean_object* v_diag_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2147_; 
lean_del_object(v___x_1950_);
v___x_2122_ = lean_io_mono_nanos_now();
v___x_2123_ = lean_st_ref_take(v_a_1943_);
v_cache_2124_ = lean_ctor_get(v___x_2123_, 1);
v_zetaDeltaFVarIds_2125_ = lean_ctor_get(v___x_2123_, 2);
v_postponed_2126_ = lean_ctor_get(v___x_2123_, 3);
v_diag_2127_ = lean_ctor_get(v___x_2123_, 4);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2147_ == 0)
{
lean_object* v_unused_2148_; 
v_unused_2148_ = lean_ctor_get(v___x_2123_, 0);
lean_dec(v_unused_2148_);
v___x_2129_ = v___x_2123_;
v_isShared_2130_ = v_isSharedCheck_2147_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_diag_2127_);
lean_inc(v_postponed_2126_);
lean_inc(v_zetaDeltaFVarIds_2125_);
lean_inc(v_cache_2124_);
lean_dec(v___x_2123_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2147_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2132_; 
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 0, v_snd_2013_);
v___x_2132_ = v___x_2129_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_snd_2013_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_cache_2124_);
lean_ctor_set(v_reuseFailAlloc_2146_, 2, v_zetaDeltaFVarIds_2125_);
lean_ctor_set(v_reuseFailAlloc_2146_, 3, v_postponed_2126_);
lean_ctor_set(v_reuseFailAlloc_2146_, 4, v_diag_2127_);
v___x_2132_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
lean_object* v___x_2133_; uint8_t v___x_2134_; lean_object* v___x_2135_; 
v___x_2133_ = lean_st_ref_set(v_a_1943_, v___x_2132_);
v___x_2134_ = lean_unbox(v_snd_2018_);
lean_dec(v_snd_2018_);
v___x_2135_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_2017_, v___x_2134_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2136_);
lean_dec_ref_known(v___x_2135_, 1);
v___x_2137_ = lean_box(0);
lean_inc(v_fst_2012_);
v___x_2138_ = l_Lean_MVarId_apply(v_fst_2012_, v_a_2136_, v_cfg_1938_, v___x_2137_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v___x_2140_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc_n(v_a_2139_, 2);
lean_dec_ref_known(v___x_2138_, 1);
lean_inc(v_a_1945_);
lean_inc_ref(v_a_1944_);
lean_inc(v_a_1943_);
lean_inc_ref(v_a_1942_);
v___x_2140_ = lean_apply_6(v_act_1939_, v_a_2139_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, lean_box(0));
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; 
lean_dec(v_a_2139_);
lean_dec(v_fst_2012_);
lean_dec_ref(v_allowFailure_1940_);
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_a_2141_);
lean_dec_ref_known(v___x_2140_, 1);
v___y_2048_ = v_a_2119_;
v___y_2049_ = v___x_2122_;
v_a_2050_ = v_a_2141_;
goto v___jp_2047_;
}
else
{
lean_object* v_a_2142_; uint8_t v___x_2143_; 
v_a_2142_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_a_2142_);
lean_dec_ref_known(v___x_2140_, 1);
v___x_2143_ = l_Lean_Exception_isInterrupt(v_a_2142_);
if (v___x_2143_ == 0)
{
uint8_t v___x_2144_; 
lean_inc(v_a_2142_);
v___x_2144_ = l_Lean_Exception_isRuntime(v_a_2142_);
v___y_2064_ = v_a_2119_;
v___y_2065_ = v___x_2122_;
v___y_2066_ = v_a_2142_;
v___y_2067_ = v_a_2139_;
v___y_2068_ = v___x_2144_;
goto v___jp_2063_;
}
else
{
v___y_2064_ = v_a_2119_;
v___y_2065_ = v___x_2122_;
v___y_2066_ = v_a_2142_;
v___y_2067_ = v_a_2139_;
v___y_2068_ = v___x_2143_;
goto v___jp_2063_;
}
}
}
else
{
lean_dec(v_fst_2012_);
lean_dec_ref(v_allowFailure_1940_);
lean_dec_ref(v_act_1939_);
v___y_2058_ = v_a_2119_;
v___y_2059_ = v___x_2122_;
v___y_2060_ = v___x_2138_;
goto v___jp_2057_;
}
}
else
{
lean_object* v_a_2145_; 
lean_dec(v_fst_2012_);
lean_dec_ref(v_allowFailure_1940_);
lean_dec_ref(v_act_1939_);
lean_dec_ref(v_cfg_1938_);
v_a_2145_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2135_, 1);
v___y_2053_ = v_a_2119_;
v___y_2054_ = v___x_2122_;
v_a_2055_ = v_a_2145_;
goto v___jp_2052_;
}
}
}
}
else
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v_cache_2151_; lean_object* v_zetaDeltaFVarIds_2152_; lean_object* v_postponed_2153_; lean_object* v_diag_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2174_; 
lean_del_object(v___x_2020_);
lean_del_object(v___x_2015_);
v___x_2149_ = lean_io_get_num_heartbeats();
v___x_2150_ = lean_st_ref_take(v_a_1943_);
v_cache_2151_ = lean_ctor_get(v___x_2150_, 1);
v_zetaDeltaFVarIds_2152_ = lean_ctor_get(v___x_2150_, 2);
v_postponed_2153_ = lean_ctor_get(v___x_2150_, 3);
v_diag_2154_ = lean_ctor_get(v___x_2150_, 4);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2174_ == 0)
{
lean_object* v_unused_2175_; 
v_unused_2175_ = lean_ctor_get(v___x_2150_, 0);
lean_dec(v_unused_2175_);
v___x_2156_ = v___x_2150_;
v_isShared_2157_ = v_isSharedCheck_2174_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_diag_2154_);
lean_inc(v_postponed_2153_);
lean_inc(v_zetaDeltaFVarIds_2152_);
lean_inc(v_cache_2151_);
lean_dec(v___x_2150_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2174_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 0, v_snd_2013_);
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_snd_2013_);
lean_ctor_set(v_reuseFailAlloc_2173_, 1, v_cache_2151_);
lean_ctor_set(v_reuseFailAlloc_2173_, 2, v_zetaDeltaFVarIds_2152_);
lean_ctor_set(v_reuseFailAlloc_2173_, 3, v_postponed_2153_);
lean_ctor_set(v_reuseFailAlloc_2173_, 4, v_diag_2154_);
v___x_2159_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
lean_object* v___x_2160_; uint8_t v___x_2161_; lean_object* v___x_2162_; 
v___x_2160_ = lean_st_ref_set(v_a_1943_, v___x_2159_);
v___x_2161_ = lean_unbox(v_snd_2018_);
lean_dec(v_snd_2018_);
v___x_2162_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_2017_, v___x_2161_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v_a_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_a_2163_);
lean_dec_ref_known(v___x_2162_, 1);
v___x_2164_ = lean_box(0);
lean_inc(v_fst_2012_);
v___x_2165_ = l_Lean_MVarId_apply(v_fst_2012_, v_a_2163_, v_cfg_1938_, v___x_2164_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v_a_2166_; lean_object* v___x_2167_; 
v_a_2166_ = lean_ctor_get(v___x_2165_, 0);
lean_inc_n(v_a_2166_, 2);
lean_dec_ref_known(v___x_2165_, 1);
lean_inc(v_a_1945_);
lean_inc_ref(v_a_1944_);
lean_inc(v_a_1943_);
lean_inc_ref(v_a_1942_);
v___x_2167_ = lean_apply_6(v_act_1939_, v_a_2166_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, lean_box(0));
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; 
lean_dec(v_a_2166_);
lean_dec(v_fst_2012_);
lean_dec_ref(v_allowFailure_1940_);
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_a_2168_);
lean_dec_ref_known(v___x_2167_, 1);
v___y_2090_ = v_a_2119_;
v___y_2091_ = v___x_2149_;
v_a_2092_ = v_a_2168_;
goto v___jp_2089_;
}
else
{
lean_object* v_a_2169_; uint8_t v___x_2170_; 
v_a_2169_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_a_2169_);
lean_dec_ref_known(v___x_2167_, 1);
v___x_2170_ = l_Lean_Exception_isInterrupt(v_a_2169_);
if (v___x_2170_ == 0)
{
uint8_t v___x_2171_; 
lean_inc(v_a_2169_);
v___x_2171_ = l_Lean_Exception_isRuntime(v_a_2169_);
v___y_2106_ = v_a_2169_;
v___y_2107_ = v_a_2119_;
v___y_2108_ = v___x_2149_;
v___y_2109_ = v_a_2166_;
v___y_2110_ = v___x_2171_;
goto v___jp_2105_;
}
else
{
v___y_2106_ = v_a_2169_;
v___y_2107_ = v_a_2119_;
v___y_2108_ = v___x_2149_;
v___y_2109_ = v_a_2166_;
v___y_2110_ = v___x_2170_;
goto v___jp_2105_;
}
}
}
else
{
lean_dec(v_fst_2012_);
lean_dec_ref(v_allowFailure_1940_);
lean_dec_ref(v_act_1939_);
v___y_2100_ = v_a_2119_;
v___y_2101_ = v___x_2149_;
v___y_2102_ = v___x_2165_;
goto v___jp_2099_;
}
}
else
{
lean_object* v_a_2172_; 
lean_dec(v_fst_2012_);
lean_dec_ref(v_allowFailure_1940_);
lean_dec_ref(v_act_1939_);
lean_dec_ref(v_cfg_1938_);
v_a_2172_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_a_2172_);
lean_dec_ref_known(v___x_2162_, 1);
v___y_2095_ = v_a_2119_;
v___y_2096_ = v___x_2149_;
v_a_2097_ = v_a_2172_;
goto v___jp_2094_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___boxed(lean_object* v_cfg_2235_, lean_object* v_act_2236_, lean_object* v_allowFailure_2237_, lean_object* v_cand_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(v_cfg_2235_, v_act_2236_, v_allowFailure_2237_, v_cand_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_);
lean_dec(v_a_2242_);
lean_dec_ref(v_a_2241_);
lean_dec(v_a_2240_);
lean_dec_ref(v_a_2239_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3(lean_object* v_00_u03b1_2245_, lean_object* v_x_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
lean_object* v___x_2252_; 
v___x_2252_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_x_2246_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2253_, lean_object* v_x_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3(v_00_u03b1_2253_, v_x_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(lean_object* v_act_2263_, lean_object* v_a_2264_, uint8_t v_collectAll_2265_, lean_object* v_as_2266_, size_t v_sz_2267_, size_t v_i_2268_, lean_object* v_b_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v_a_2276_; uint8_t v___x_2280_; 
v___x_2280_ = lean_usize_dec_lt(v_i_2268_, v_sz_2267_);
if (v___x_2280_ == 0)
{
lean_object* v___x_2281_; 
lean_dec_ref(v_act_2263_);
v___x_2281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2281_, 0, v_b_2269_);
return v___x_2281_;
}
else
{
lean_object* v_snd_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2355_; 
v_snd_2282_ = lean_ctor_get(v_b_2269_, 1);
v_isSharedCheck_2355_ = !lean_is_exclusive(v_b_2269_);
if (v_isSharedCheck_2355_ == 0)
{
lean_object* v_unused_2356_; 
v_unused_2356_ = lean_ctor_get(v_b_2269_, 0);
lean_dec(v_unused_2356_);
v___x_2284_ = v_b_2269_;
v_isShared_2285_ = v_isSharedCheck_2355_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_snd_2282_);
lean_dec(v_b_2269_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2355_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2286_; lean_object* v_a_2287_; lean_object* v___x_2288_; 
v___x_2286_ = lean_box(0);
v_a_2287_ = lean_array_uget_borrowed(v_as_2266_, v_i_2268_);
lean_inc_ref(v_act_2263_);
lean_inc(v___y_2273_);
lean_inc_ref(v___y_2272_);
lean_inc(v___y_2271_);
lean_inc_ref(v___y_2270_);
lean_inc(v_a_2287_);
v___x_2288_ = lean_apply_6(v_act_2263_, v_a_2287_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, lean_box(0));
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2318_; 
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2291_ = v___x_2288_;
v_isShared_2292_ = v_isSharedCheck_2318_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2288_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2318_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
uint8_t v___y_2311_; uint8_t v___x_2317_; 
v___x_2317_ = l_List_isEmpty___redArg(v_a_2289_);
if (v___x_2317_ == 0)
{
v___y_2311_ = v___x_2317_;
goto v___jp_2310_;
}
else
{
if (v_collectAll_2265_ == 0)
{
v___y_2311_ = v___x_2317_;
goto v___jp_2310_;
}
else
{
lean_del_object(v___x_2291_);
goto v___jp_2293_;
}
}
v___jp_2293_:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2294_ = lean_st_ref_get(v___y_2271_);
v___x_2295_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2264_, v___y_2271_, v___y_2273_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v_mctx_2296_; lean_object* v___x_2298_; 
lean_dec_ref_known(v___x_2295_, 1);
v_mctx_2296_ = lean_ctor_get(v___x_2294_, 0);
lean_inc_ref(v_mctx_2296_);
lean_dec(v___x_2294_);
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 1, v_mctx_2296_);
lean_ctor_set(v___x_2284_, 0, v_a_2289_);
v___x_2298_ = v___x_2284_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2289_);
lean_ctor_set(v_reuseFailAlloc_2301_, 1, v_mctx_2296_);
v___x_2298_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2299_ = lean_array_push(v_snd_2282_, v___x_2298_);
v___x_2300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2286_);
lean_ctor_set(v___x_2300_, 1, v___x_2299_);
v_a_2276_ = v___x_2300_;
goto v___jp_2275_;
}
}
else
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2309_; 
lean_dec(v___x_2294_);
lean_dec(v_a_2289_);
lean_del_object(v___x_2284_);
lean_dec(v_snd_2282_);
lean_dec_ref(v_act_2263_);
v_a_2302_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2304_ = v___x_2295_;
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2295_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2305_ == 0)
{
v___x_2307_ = v___x_2304_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2302_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
v___jp_2310_:
{
if (v___y_2311_ == 0)
{
lean_del_object(v___x_2291_);
goto v___jp_2293_;
}
else
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2315_; 
lean_dec(v_a_2289_);
lean_del_object(v___x_2284_);
lean_dec_ref(v_act_2263_);
v___x_2312_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0___closed__0));
v___x_2313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2312_);
lean_ctor_set(v___x_2313_, 1, v_snd_2282_);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 0, v___x_2313_);
v___x_2315_ = v___x_2291_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2313_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
}
else
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2354_; 
v_a_2319_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2321_ = v___x_2288_;
v_isShared_2322_ = v_isSharedCheck_2354_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2288_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2354_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
uint8_t v___y_2324_; uint8_t v___x_2352_; 
v___x_2352_ = l_Lean_Exception_isInterrupt(v_a_2319_);
if (v___x_2352_ == 0)
{
uint8_t v___x_2353_; 
lean_inc(v_a_2319_);
v___x_2353_ = l_Lean_Exception_isRuntime(v_a_2319_);
v___y_2324_ = v___x_2353_;
goto v___jp_2323_;
}
else
{
v___y_2324_ = v___x_2352_;
goto v___jp_2323_;
}
v___jp_2323_:
{
if (v___y_2324_ == 0)
{
lean_object* v___x_2325_; 
lean_del_object(v___x_2321_);
v___x_2325_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2264_, v___y_2271_, v___y_2273_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2339_; 
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2339_ == 0)
{
lean_object* v_unused_2340_; 
v_unused_2340_ = lean_ctor_get(v___x_2325_, 0);
lean_dec(v_unused_2340_);
v___x_2327_ = v___x_2325_;
v_isShared_2328_ = v_isSharedCheck_2339_;
goto v_resetjp_2326_;
}
else
{
lean_dec(v___x_2325_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2339_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
uint8_t v___x_2329_; 
v___x_2329_ = l_Lean_Meta_LibrarySearch_isAbortSpeculation(v_a_2319_);
lean_dec(v_a_2319_);
if (v___x_2329_ == 0)
{
lean_object* v___x_2331_; 
lean_del_object(v___x_2327_);
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 0, v___x_2286_);
v___x_2331_ = v___x_2284_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2286_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v_snd_2282_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
v_a_2276_ = v___x_2331_;
goto v___jp_2275_;
}
}
else
{
lean_object* v___x_2334_; 
lean_dec_ref(v_act_2263_);
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 0, v___x_2286_);
v___x_2334_ = v___x_2284_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2286_);
lean_ctor_set(v_reuseFailAlloc_2338_, 1, v_snd_2282_);
v___x_2334_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
lean_object* v___x_2336_; 
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 0, v___x_2334_);
v___x_2336_ = v___x_2327_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v___x_2334_);
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
}
else
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
lean_dec(v_a_2319_);
lean_del_object(v___x_2284_);
lean_dec(v_snd_2282_);
lean_dec_ref(v_act_2263_);
v_a_2341_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2325_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2325_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2346_; 
if (v_isShared_2344_ == 0)
{
v___x_2346_ = v___x_2343_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_a_2341_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
}
else
{
lean_object* v___x_2350_; 
lean_del_object(v___x_2284_);
lean_dec(v_snd_2282_);
lean_dec_ref(v_act_2263_);
if (v_isShared_2322_ == 0)
{
v___x_2350_ = v___x_2321_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_a_2319_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
}
}
}
v___jp_2275_:
{
size_t v___x_2277_; size_t v___x_2278_; 
v___x_2277_ = ((size_t)1ULL);
v___x_2278_ = lean_usize_add(v_i_2268_, v___x_2277_);
v_i_2268_ = v___x_2278_;
v_b_2269_ = v_a_2276_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0___boxed(lean_object* v_act_2357_, lean_object* v_a_2358_, lean_object* v_collectAll_2359_, lean_object* v_as_2360_, lean_object* v_sz_2361_, lean_object* v_i_2362_, lean_object* v_b_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
uint8_t v_collectAll_boxed_2369_; size_t v_sz_boxed_2370_; size_t v_i_boxed_2371_; lean_object* v_res_2372_; 
v_collectAll_boxed_2369_ = lean_unbox(v_collectAll_2359_);
v_sz_boxed_2370_ = lean_unbox_usize(v_sz_2361_);
lean_dec(v_sz_2361_);
v_i_boxed_2371_ = lean_unbox_usize(v_i_2362_);
lean_dec(v_i_2362_);
v_res_2372_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(v_act_2357_, v_a_2358_, v_collectAll_boxed_2369_, v_as_2360_, v_sz_boxed_2370_, v_i_boxed_2371_, v_b_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec_ref(v_as_2360_);
lean_dec_ref(v_a_2358_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryOnEach(lean_object* v_act_2378_, lean_object* v_candidates_2379_, uint8_t v_collectAll_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_){
_start:
{
lean_object* v___x_2386_; 
v___x_2386_ = l_Lean_Meta_saveState___redArg(v_a_2382_, v_a_2384_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v_a_2387_; lean_object* v___x_2388_; size_t v_sz_2389_; size_t v___x_2390_; lean_object* v___x_2391_; 
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
lean_inc(v_a_2387_);
lean_dec_ref_known(v___x_2386_, 1);
v___x_2388_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryOnEach___closed__1));
v_sz_2389_ = lean_array_size(v_candidates_2379_);
v___x_2390_ = ((size_t)0ULL);
v___x_2391_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(v_act_2378_, v_a_2387_, v_collectAll_2380_, v_candidates_2379_, v_sz_2389_, v___x_2390_, v___x_2388_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_);
lean_dec(v_a_2387_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2406_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2394_ = v___x_2391_;
v_isShared_2395_ = v_isSharedCheck_2406_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2391_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2406_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v_fst_2396_; 
v_fst_2396_ = lean_ctor_get(v_a_2392_, 0);
if (lean_obj_tag(v_fst_2396_) == 0)
{
lean_object* v_snd_2397_; lean_object* v___x_2398_; lean_object* v___x_2400_; 
v_snd_2397_ = lean_ctor_get(v_a_2392_, 1);
lean_inc(v_snd_2397_);
lean_dec(v_a_2392_);
v___x_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2398_, 0, v_snd_2397_);
if (v_isShared_2395_ == 0)
{
lean_ctor_set(v___x_2394_, 0, v___x_2398_);
v___x_2400_ = v___x_2394_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2398_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
else
{
lean_object* v_val_2402_; lean_object* v___x_2404_; 
lean_inc_ref(v_fst_2396_);
lean_dec(v_a_2392_);
v_val_2402_ = lean_ctor_get(v_fst_2396_, 0);
lean_inc(v_val_2402_);
lean_dec_ref_known(v_fst_2396_, 1);
if (v_isShared_2395_ == 0)
{
lean_ctor_set(v___x_2394_, 0, v_val_2402_);
v___x_2404_ = v___x_2394_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_val_2402_);
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
else
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2414_; 
v_a_2407_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2409_ = v___x_2391_;
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2391_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2412_; 
if (v_isShared_2410_ == 0)
{
v___x_2412_ = v___x_2409_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_a_2407_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
else
{
lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2422_; 
lean_dec_ref(v_act_2378_);
v_a_2415_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2417_ = v___x_2386_;
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___x_2386_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2420_; 
if (v_isShared_2418_ == 0)
{
v___x_2420_ = v___x_2417_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_a_2415_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryOnEach___boxed(lean_object* v_act_2423_, lean_object* v_candidates_2424_, lean_object* v_collectAll_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_){
_start:
{
uint8_t v_collectAll_boxed_2431_; lean_object* v_res_2432_; 
v_collectAll_boxed_2431_ = lean_unbox(v_collectAll_2425_);
v_res_2432_ = l_Lean_Meta_LibrarySearch_tryOnEach(v_act_2423_, v_candidates_2424_, v_collectAll_boxed_2431_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_);
lean_dec(v_a_2429_);
lean_dec_ref(v_a_2428_);
lean_dec(v_a_2427_);
lean_dec_ref(v_a_2426_);
lean_dec_ref(v_candidates_2424_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg(){
_start:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2434_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0, &l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0_once, _init_l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0);
v___x_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2434_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg___boxed(lean_object* v___y_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg();
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0(lean_object* v_00_u03b1_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v___x_2444_; 
v___x_2444_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg();
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___boxed(lean_object* v_00_u03b1_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0(v_00_u03b1_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(lean_object* v_category_2452_, lean_object* v_opts_2453_, lean_object* v_act_2454_, lean_object* v_decl_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_){
_start:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
lean_inc(v___y_2459_);
lean_inc_ref(v___y_2458_);
lean_inc(v___y_2457_);
lean_inc_ref(v___y_2456_);
v___x_2461_ = lean_apply_4(v_act_2454_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
v___x_2462_ = l_Lean_profileitIOUnsafe___redArg(v_category_2452_, v_opts_2453_, v___x_2461_, v_decl_2455_);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg___boxed(lean_object* v_category_2463_, lean_object* v_opts_2464_, lean_object* v_act_2465_, lean_object* v_decl_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v_category_2463_, v_opts_2464_, v_act_2465_, v_decl_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec_ref(v_opts_2464_);
lean_dec_ref(v_category_2463_);
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3(lean_object* v_00_u03b1_2473_, lean_object* v_category_2474_, lean_object* v_opts_2475_, lean_object* v_act_2476_, lean_object* v_decl_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_){
_start:
{
lean_object* v___x_2483_; 
v___x_2483_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v_category_2474_, v_opts_2475_, v_act_2476_, v_decl_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___boxed(lean_object* v_00_u03b1_2484_, lean_object* v_category_2485_, lean_object* v_opts_2486_, lean_object* v_act_2487_, lean_object* v_decl_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v_res_2494_; 
v_res_2494_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3(v_00_u03b1_2484_, v_category_2485_, v_opts_2486_, v_act_2487_, v_decl_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec_ref(v_opts_2486_);
lean_dec_ref(v_category_2485_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0(lean_object* v_a_2495_, lean_object* v___x_2496_, lean_object* v_tactic_2497_, lean_object* v_allowFailure_2498_, lean_object* v_cand_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_){
_start:
{
lean_object* v___x_2505_; 
lean_inc(v___y_2503_);
lean_inc_ref(v___y_2502_);
lean_inc(v___y_2501_);
lean_inc_ref(v___y_2500_);
v___x_2505_ = lean_apply_5(v_a_2495_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, lean_box(0));
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_a_2506_; uint8_t v___x_2507_; 
v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_a_2506_);
lean_dec_ref_known(v___x_2505_, 1);
v___x_2507_ = lean_unbox(v_a_2506_);
lean_dec(v_a_2506_);
if (v___x_2507_ == 0)
{
lean_object* v___x_2508_; 
v___x_2508_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(v___x_2496_, v_tactic_2497_, v_allowFailure_2498_, v_cand_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
return v___x_2508_;
}
else
{
lean_object* v___x_2509_; lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2517_; 
lean_dec_ref(v_cand_2499_);
lean_dec_ref(v_allowFailure_2498_);
lean_dec_ref(v_tactic_2497_);
lean_dec_ref(v___x_2496_);
v___x_2509_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg();
v_a_2510_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2512_ = v___x_2509_;
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_dec(v___x_2509_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2515_; 
if (v_isShared_2513_ == 0)
{
v___x_2515_ = v___x_2512_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_a_2510_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
}
else
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
lean_dec_ref(v_cand_2499_);
lean_dec_ref(v_allowFailure_2498_);
lean_dec_ref(v_tactic_2497_);
lean_dec_ref(v___x_2496_);
v_a_2518_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2520_ = v___x_2505_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2505_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2518_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed(lean_object* v_a_2526_, lean_object* v___x_2527_, lean_object* v_tactic_2528_, lean_object* v_allowFailure_2529_, lean_object* v_cand_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0(v_a_2526_, v___x_2527_, v_tactic_2528_, v_allowFailure_2529_, v_cand_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
return v_res_2536_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(lean_object* v_as_2537_, size_t v_i_2538_, size_t v_stop_2539_){
_start:
{
uint8_t v___x_2540_; 
v___x_2540_ = lean_usize_dec_eq(v_i_2538_, v_stop_2539_);
if (v___x_2540_ == 0)
{
lean_object* v___x_2541_; lean_object* v_fst_2542_; uint8_t v___x_2543_; 
v___x_2541_ = lean_array_uget_borrowed(v_as_2537_, v_i_2538_);
v_fst_2542_ = lean_ctor_get(v___x_2541_, 0);
v___x_2543_ = l_List_isEmpty___redArg(v_fst_2542_);
if (v___x_2543_ == 0)
{
size_t v___x_2544_; size_t v___x_2545_; 
v___x_2544_ = ((size_t)1ULL);
v___x_2545_ = lean_usize_add(v_i_2538_, v___x_2544_);
v_i_2538_ = v___x_2545_;
goto _start;
}
else
{
return v___x_2543_;
}
}
else
{
uint8_t v___x_2547_; 
v___x_2547_ = 0;
return v___x_2547_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2___boxed(lean_object* v_as_2548_, lean_object* v_i_2549_, lean_object* v_stop_2550_){
_start:
{
size_t v_i_boxed_2551_; size_t v_stop_boxed_2552_; uint8_t v_res_2553_; lean_object* v_r_2554_; 
v_i_boxed_2551_ = lean_unbox_usize(v_i_2549_);
lean_dec(v_i_2549_);
v_stop_boxed_2552_ = lean_unbox_usize(v_stop_2550_);
lean_dec(v_stop_2550_);
v_res_2553_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_as_2548_, v_i_boxed_2551_, v_stop_boxed_2552_);
lean_dec_ref(v_as_2548_);
v_r_2554_ = lean_box(v_res_2553_);
return v_r_2554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(lean_object* v_goal_2555_, lean_object* v___x_2556_, size_t v_sz_2557_, size_t v_i_2558_, lean_object* v_bs_2559_){
_start:
{
uint8_t v___x_2560_; 
v___x_2560_ = lean_usize_dec_lt(v_i_2558_, v_sz_2557_);
if (v___x_2560_ == 0)
{
lean_dec_ref(v___x_2556_);
lean_dec(v_goal_2555_);
return v_bs_2559_;
}
else
{
lean_object* v_v_2561_; lean_object* v___x_2562_; lean_object* v_bs_x27_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; size_t v___x_2566_; size_t v___x_2567_; lean_object* v___x_2568_; 
v_v_2561_ = lean_array_uget(v_bs_2559_, v_i_2558_);
v___x_2562_ = lean_unsigned_to_nat(0u);
v_bs_x27_2563_ = lean_array_uset(v_bs_2559_, v_i_2558_, v___x_2562_);
lean_inc_ref(v___x_2556_);
lean_inc(v_goal_2555_);
v___x_2564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2564_, 0, v_goal_2555_);
lean_ctor_set(v___x_2564_, 1, v___x_2556_);
v___x_2565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2564_);
lean_ctor_set(v___x_2565_, 1, v_v_2561_);
v___x_2566_ = ((size_t)1ULL);
v___x_2567_ = lean_usize_add(v_i_2558_, v___x_2566_);
v___x_2568_ = lean_array_uset(v_bs_x27_2563_, v_i_2558_, v___x_2565_);
v_i_2558_ = v___x_2567_;
v_bs_2559_ = v___x_2568_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1___boxed(lean_object* v_goal_2570_, lean_object* v___x_2571_, lean_object* v_sz_2572_, lean_object* v_i_2573_, lean_object* v_bs_2574_){
_start:
{
size_t v_sz_boxed_2575_; size_t v_i_boxed_2576_; lean_object* v_res_2577_; 
v_sz_boxed_2575_ = lean_unbox_usize(v_sz_2572_);
lean_dec(v_sz_2572_);
v_i_boxed_2576_ = lean_unbox_usize(v_i_2573_);
lean_dec(v_i_2573_);
v_res_2577_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2570_, v___x_2571_, v_sz_boxed_2575_, v_i_boxed_2576_, v_bs_2574_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1(lean_object* v_leavePercentHeartbeats_2579_, lean_object* v_goal_2580_, lean_object* v___x_2581_, lean_object* v_tactic_2582_, lean_object* v_allowFailure_2583_, uint8_t v_collectAll_2584_, uint8_t v_includeStar_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
lean_object* v___x_2594_; 
v___x_2594_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercentHeartbeats_2579_, v___y_2588_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v_a_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v_a_2595_ = lean_ctor_get(v___x_2594_, 0);
lean_inc(v_a_2595_);
lean_dec_ref_known(v___x_2594_, 1);
v___x_2596_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___closed__0));
lean_inc(v_goal_2580_);
v___x_2597_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v___x_2596_, v_goal_2580_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v___f_2599_; lean_object* v___x_2600_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_a_2598_);
lean_dec_ref_known(v___x_2597_, 1);
v___f_2599_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2599_, 0, v_a_2595_);
lean_closure_set(v___f_2599_, 1, v___x_2581_);
lean_closure_set(v___f_2599_, 2, v_tactic_2582_);
lean_closure_set(v___f_2599_, 3, v_allowFailure_2583_);
lean_inc_ref(v___f_2599_);
v___x_2600_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2599_, v_a_2598_, v_collectAll_2584_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_);
lean_dec(v_a_2598_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_a_2601_; 
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_a_2601_);
if (lean_obj_tag(v_a_2601_) == 0)
{
lean_dec_ref_known(v___x_2600_, 1);
lean_dec_ref(v___f_2599_);
lean_dec(v_goal_2580_);
goto v___jp_2591_;
}
else
{
lean_object* v_val_2602_; lean_object* v___x_2651_; lean_object* v___x_2652_; uint8_t v___x_2653_; 
v_val_2602_ = lean_ctor_get(v_a_2601_, 0);
v___x_2651_ = lean_unsigned_to_nat(0u);
v___x_2652_ = lean_array_get_size(v_val_2602_);
v___x_2653_ = lean_nat_dec_lt(v___x_2651_, v___x_2652_);
if (v___x_2653_ == 0)
{
goto v___jp_2647_;
}
else
{
if (v___x_2653_ == 0)
{
goto v___jp_2647_;
}
else
{
size_t v___x_2654_; size_t v___x_2655_; uint8_t v___x_2656_; 
v___x_2654_ = ((size_t)0ULL);
v___x_2655_ = lean_usize_of_nat(v___x_2652_);
v___x_2656_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_val_2602_, v___x_2654_, v___x_2655_);
if (v___x_2656_ == 0)
{
goto v___jp_2647_;
}
else
{
lean_dec_ref_known(v_a_2601_, 1);
lean_dec_ref(v___f_2599_);
lean_dec(v_goal_2580_);
return v___x_2600_;
}
}
}
v___jp_2603_:
{
if (v_includeStar_2585_ == 0)
{
lean_dec_ref_known(v_a_2601_, 1);
lean_dec_ref(v___f_2599_);
lean_dec(v_goal_2580_);
return v___x_2600_;
}
else
{
lean_object* v___x_2604_; 
lean_dec_ref_known(v___x_2600_, 1);
v___x_2604_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2638_; 
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2607_ = v___x_2604_;
v_isShared_2608_ = v_isSharedCheck_2638_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2604_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2638_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; uint8_t v___x_2611_; 
v___x_2609_ = lean_array_get_size(v_a_2605_);
v___x_2610_ = lean_unsigned_to_nat(0u);
v___x_2611_ = lean_nat_dec_eq(v___x_2609_, v___x_2610_);
if (v___x_2611_ == 0)
{
lean_object* v___x_2612_; lean_object* v_mctx_2613_; size_t v_sz_2614_; size_t v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
lean_inc(v_val_2602_);
lean_del_object(v___x_2607_);
lean_dec_ref_known(v_a_2601_, 1);
v___x_2612_ = lean_st_ref_get(v___y_2587_);
v_mctx_2613_ = lean_ctor_get(v___x_2612_, 0);
lean_inc_ref(v_mctx_2613_);
lean_dec(v___x_2612_);
v_sz_2614_ = lean_array_size(v_a_2605_);
v___x_2615_ = ((size_t)0ULL);
v___x_2616_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2580_, v_mctx_2613_, v_sz_2614_, v___x_2615_, v_a_2605_);
v___x_2617_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2599_, v___x_2616_, v_collectAll_2584_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_);
lean_dec_ref(v___x_2616_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2634_; 
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2620_ = v___x_2617_;
v_isShared_2621_ = v_isSharedCheck_2634_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2617_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2634_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
if (lean_obj_tag(v_a_2618_) == 0)
{
lean_del_object(v___x_2620_);
lean_dec(v_val_2602_);
goto v___jp_2591_;
}
else
{
lean_object* v_val_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2633_; 
v_val_2622_ = lean_ctor_get(v_a_2618_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v_a_2618_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2624_ = v_a_2618_;
v_isShared_2625_ = v_isSharedCheck_2633_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_val_2622_);
lean_dec(v_a_2618_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2633_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2626_; lean_object* v___x_2628_; 
v___x_2626_ = l_Array_append___redArg(v_val_2602_, v_val_2622_);
lean_dec(v_val_2622_);
if (v_isShared_2625_ == 0)
{
lean_ctor_set(v___x_2624_, 0, v___x_2626_);
v___x_2628_ = v___x_2624_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v___x_2626_);
v___x_2628_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
lean_object* v___x_2630_; 
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 0, v___x_2628_);
v___x_2630_ = v___x_2620_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v___x_2628_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
}
}
else
{
lean_dec(v_val_2602_);
return v___x_2617_;
}
}
else
{
lean_object* v___x_2636_; 
lean_dec(v_a_2605_);
lean_dec_ref(v___f_2599_);
lean_dec(v_goal_2580_);
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 0, v_a_2601_);
v___x_2636_ = v___x_2607_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2601_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
else
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2646_; 
lean_dec_ref_known(v_a_2601_, 1);
lean_dec_ref(v___f_2599_);
lean_dec(v_goal_2580_);
v_a_2639_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2641_ = v___x_2604_;
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2604_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2644_; 
if (v_isShared_2642_ == 0)
{
v___x_2644_ = v___x_2641_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_a_2639_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
}
v___jp_2647_:
{
if (v_collectAll_2584_ == 0)
{
lean_object* v___x_2648_; lean_object* v___x_2649_; uint8_t v___x_2650_; 
v___x_2648_ = lean_array_get_size(v_val_2602_);
v___x_2649_ = lean_unsigned_to_nat(0u);
v___x_2650_ = lean_nat_dec_eq(v___x_2648_, v___x_2649_);
if (v___x_2650_ == 0)
{
lean_dec_ref_known(v_a_2601_, 1);
lean_dec_ref(v___f_2599_);
lean_dec(v_goal_2580_);
return v___x_2600_;
}
else
{
goto v___jp_2603_;
}
}
else
{
goto v___jp_2603_;
}
}
}
}
else
{
lean_dec_ref(v___f_2599_);
lean_dec(v_goal_2580_);
return v___x_2600_;
}
}
else
{
lean_object* v_a_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2664_; 
lean_dec(v_a_2595_);
lean_dec_ref(v_allowFailure_2583_);
lean_dec_ref(v_tactic_2582_);
lean_dec_ref(v___x_2581_);
lean_dec(v_goal_2580_);
v_a_2657_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2659_ = v___x_2597_;
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_a_2657_);
lean_dec(v___x_2597_);
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
else
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2672_; 
lean_dec_ref(v_allowFailure_2583_);
lean_dec_ref(v_tactic_2582_);
lean_dec_ref(v___x_2581_);
lean_dec(v_goal_2580_);
v_a_2665_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2667_ = v___x_2594_;
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2594_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2670_; 
if (v_isShared_2668_ == 0)
{
v___x_2670_ = v___x_2667_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2665_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
v___jp_2591_:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2592_ = lean_box(0);
v___x_2593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2592_);
return v___x_2593_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed(lean_object* v_leavePercentHeartbeats_2673_, lean_object* v_goal_2674_, lean_object* v___x_2675_, lean_object* v_tactic_2676_, lean_object* v_allowFailure_2677_, lean_object* v_collectAll_2678_, lean_object* v_includeStar_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
uint8_t v_collectAll_boxed_2685_; uint8_t v_includeStar_boxed_2686_; lean_object* v_res_2687_; 
v_collectAll_boxed_2685_ = lean_unbox(v_collectAll_2678_);
v_includeStar_boxed_2686_ = lean_unbox(v_includeStar_2679_);
v_res_2687_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1(v_leavePercentHeartbeats_2673_, v_goal_2674_, v___x_2675_, v_tactic_2676_, v_allowFailure_2677_, v_collectAll_boxed_2685_, v_includeStar_boxed_2686_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v_leavePercentHeartbeats_2673_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2(lean_object* v_goal_2688_, lean_object* v_x_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_){
_start:
{
lean_object* v___x_2695_; 
v___x_2695_ = l_Lean_MVarId_getType(v_goal_2688_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2704_; 
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2698_ = v___x_2695_;
v_isShared_2699_ = v_isSharedCheck_2704_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2695_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2704_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2700_; lean_object* v___x_2702_; 
v___x_2700_ = l_Lean_MessageData_ofExpr(v_a_2696_);
if (v_isShared_2699_ == 0)
{
lean_ctor_set(v___x_2698_, 0, v___x_2700_);
v___x_2702_ = v___x_2698_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2700_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
else
{
lean_object* v_a_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2712_; 
v_a_2705_ = lean_ctor_get(v___x_2695_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2707_ = v___x_2695_;
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_a_2705_);
lean_dec(v___x_2695_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2710_; 
if (v_isShared_2708_ == 0)
{
v___x_2710_ = v___x_2707_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_a_2705_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2___boxed(lean_object* v_goal_2713_, lean_object* v_x_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2(v_goal_2713_, v_x_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec_ref(v_x_2714_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4(lean_object* v_leavePercentHeartbeats_2721_, lean_object* v_goal_2722_, lean_object* v___x_2723_, lean_object* v_tactic_2724_, lean_object* v_allowFailure_2725_, uint8_t v_collectAll_2726_, uint8_t v_includeStar_2727_, uint8_t v___x_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
lean_object* v___x_2737_; 
v___x_2737_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercentHeartbeats_2721_, v___y_2731_);
if (lean_obj_tag(v___x_2737_) == 0)
{
lean_object* v_a_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; 
v_a_2738_ = lean_ctor_get(v___x_2737_, 0);
lean_inc(v_a_2738_);
lean_dec_ref_known(v___x_2737_, 1);
v___x_2739_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___closed__0));
lean_inc(v_goal_2722_);
v___x_2740_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v___x_2739_, v_goal_2722_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_object* v_a_2741_; lean_object* v___f_2742_; lean_object* v___x_2743_; 
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_a_2741_);
lean_dec_ref_known(v___x_2740_, 1);
v___f_2742_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2742_, 0, v_a_2738_);
lean_closure_set(v___f_2742_, 1, v___x_2723_);
lean_closure_set(v___f_2742_, 2, v_tactic_2724_);
lean_closure_set(v___f_2742_, 3, v_allowFailure_2725_);
lean_inc_ref(v___f_2742_);
v___x_2743_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2742_, v_a_2741_, v_collectAll_2726_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
lean_dec(v_a_2741_);
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_object* v_a_2744_; 
v_a_2744_ = lean_ctor_get(v___x_2743_, 0);
lean_inc(v_a_2744_);
if (lean_obj_tag(v_a_2744_) == 0)
{
lean_dec_ref_known(v___x_2743_, 1);
lean_dec_ref(v___f_2742_);
lean_dec(v_goal_2722_);
goto v___jp_2734_;
}
else
{
lean_object* v_val_2745_; uint8_t v___y_2791_; lean_object* v___x_2795_; lean_object* v___x_2796_; uint8_t v___x_2797_; 
v_val_2745_ = lean_ctor_get(v_a_2744_, 0);
v___x_2795_ = lean_unsigned_to_nat(0u);
v___x_2796_ = lean_array_get_size(v_val_2745_);
v___x_2797_ = lean_nat_dec_lt(v___x_2795_, v___x_2796_);
if (v___x_2797_ == 0)
{
v___y_2791_ = v___x_2728_;
goto v___jp_2790_;
}
else
{
if (v___x_2797_ == 0)
{
v___y_2791_ = v___x_2728_;
goto v___jp_2790_;
}
else
{
size_t v___x_2798_; size_t v___x_2799_; uint8_t v___x_2800_; 
v___x_2798_ = ((size_t)0ULL);
v___x_2799_ = lean_usize_of_nat(v___x_2796_);
v___x_2800_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_val_2745_, v___x_2798_, v___x_2799_);
v___y_2791_ = v___x_2800_;
goto v___jp_2790_;
}
}
v___jp_2746_:
{
if (v_includeStar_2727_ == 0)
{
lean_dec_ref_known(v_a_2744_, 1);
lean_dec_ref(v___f_2742_);
lean_dec(v_goal_2722_);
return v___x_2743_;
}
else
{
lean_object* v___x_2747_; 
lean_dec_ref_known(v___x_2743_, 1);
v___x_2747_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2781_; 
v_a_2748_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2750_ = v___x_2747_;
v_isShared_2751_ = v_isSharedCheck_2781_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___x_2747_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2781_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; uint8_t v___x_2754_; 
v___x_2752_ = lean_array_get_size(v_a_2748_);
v___x_2753_ = lean_unsigned_to_nat(0u);
v___x_2754_ = lean_nat_dec_eq(v___x_2752_, v___x_2753_);
if (v___x_2754_ == 0)
{
lean_object* v___x_2755_; lean_object* v_mctx_2756_; size_t v_sz_2757_; size_t v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; 
lean_inc(v_val_2745_);
lean_del_object(v___x_2750_);
lean_dec_ref_known(v_a_2744_, 1);
v___x_2755_ = lean_st_ref_get(v___y_2730_);
v_mctx_2756_ = lean_ctor_get(v___x_2755_, 0);
lean_inc_ref(v_mctx_2756_);
lean_dec(v___x_2755_);
v_sz_2757_ = lean_array_size(v_a_2748_);
v___x_2758_ = ((size_t)0ULL);
v___x_2759_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2722_, v_mctx_2756_, v_sz_2757_, v___x_2758_, v_a_2748_);
v___x_2760_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2742_, v___x_2759_, v_collectAll_2726_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
lean_dec_ref(v___x_2759_);
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2777_; 
v_a_2761_ = lean_ctor_get(v___x_2760_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2763_ = v___x_2760_;
v_isShared_2764_ = v_isSharedCheck_2777_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2760_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2777_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
if (lean_obj_tag(v_a_2761_) == 0)
{
lean_del_object(v___x_2763_);
lean_dec(v_val_2745_);
goto v___jp_2734_;
}
else
{
lean_object* v_val_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2776_; 
v_val_2765_ = lean_ctor_get(v_a_2761_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v_a_2761_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2767_ = v_a_2761_;
v_isShared_2768_ = v_isSharedCheck_2776_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_val_2765_);
lean_dec(v_a_2761_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2776_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2769_; lean_object* v___x_2771_; 
v___x_2769_ = l_Array_append___redArg(v_val_2745_, v_val_2765_);
lean_dec(v_val_2765_);
if (v_isShared_2768_ == 0)
{
lean_ctor_set(v___x_2767_, 0, v___x_2769_);
v___x_2771_ = v___x_2767_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v___x_2769_);
v___x_2771_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
lean_object* v___x_2773_; 
if (v_isShared_2764_ == 0)
{
lean_ctor_set(v___x_2763_, 0, v___x_2771_);
v___x_2773_ = v___x_2763_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v___x_2771_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
}
}
else
{
lean_dec(v_val_2745_);
return v___x_2760_;
}
}
else
{
lean_object* v___x_2779_; 
lean_dec(v_a_2748_);
lean_dec_ref(v___f_2742_);
lean_dec(v_goal_2722_);
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 0, v_a_2744_);
v___x_2779_ = v___x_2750_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_a_2744_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
lean_dec_ref_known(v_a_2744_, 1);
lean_dec_ref(v___f_2742_);
lean_dec(v_goal_2722_);
v_a_2782_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2747_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2747_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
}
v___jp_2790_:
{
if (v___y_2791_ == 0)
{
if (v_collectAll_2726_ == 0)
{
lean_object* v___x_2792_; lean_object* v___x_2793_; uint8_t v___x_2794_; 
v___x_2792_ = lean_array_get_size(v_val_2745_);
v___x_2793_ = lean_unsigned_to_nat(0u);
v___x_2794_ = lean_nat_dec_eq(v___x_2792_, v___x_2793_);
if (v___x_2794_ == 0)
{
lean_dec_ref_known(v_a_2744_, 1);
lean_dec_ref(v___f_2742_);
lean_dec(v_goal_2722_);
return v___x_2743_;
}
else
{
goto v___jp_2746_;
}
}
else
{
goto v___jp_2746_;
}
}
else
{
lean_dec_ref_known(v_a_2744_, 1);
lean_dec_ref(v___f_2742_);
lean_dec(v_goal_2722_);
return v___x_2743_;
}
}
}
}
else
{
lean_dec_ref(v___f_2742_);
lean_dec(v_goal_2722_);
return v___x_2743_;
}
}
else
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
lean_dec(v_a_2738_);
lean_dec_ref(v_allowFailure_2725_);
lean_dec_ref(v_tactic_2724_);
lean_dec_ref(v___x_2723_);
lean_dec(v_goal_2722_);
v_a_2801_ = lean_ctor_get(v___x_2740_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___x_2740_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2740_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2801_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
}
else
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
lean_dec_ref(v_allowFailure_2725_);
lean_dec_ref(v_tactic_2724_);
lean_dec_ref(v___x_2723_);
lean_dec(v_goal_2722_);
v_a_2809_ = lean_ctor_get(v___x_2737_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2811_ = v___x_2737_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___x_2737_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
v___jp_2734_:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; 
v___x_2735_ = lean_box(0);
v___x_2736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2735_);
return v___x_2736_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4___boxed(lean_object* v_leavePercentHeartbeats_2817_, lean_object* v_goal_2818_, lean_object* v___x_2819_, lean_object* v_tactic_2820_, lean_object* v_allowFailure_2821_, lean_object* v_collectAll_2822_, lean_object* v_includeStar_2823_, lean_object* v___x_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
uint8_t v_collectAll_boxed_2830_; uint8_t v_includeStar_boxed_2831_; uint8_t v___x_15813__boxed_2832_; lean_object* v_res_2833_; 
v_collectAll_boxed_2830_ = lean_unbox(v_collectAll_2822_);
v_includeStar_boxed_2831_ = lean_unbox(v_includeStar_2823_);
v___x_15813__boxed_2832_ = lean_unbox(v___x_2824_);
v_res_2833_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4(v_leavePercentHeartbeats_2817_, v_goal_2818_, v___x_2819_, v_tactic_2820_, v_allowFailure_2821_, v_collectAll_boxed_2830_, v_includeStar_boxed_2831_, v___x_15813__boxed_2832_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v_leavePercentHeartbeats_2817_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__5(lean_object* v_leavePercentHeartbeats_2834_, lean_object* v_goal_2835_, lean_object* v___x_2836_, lean_object* v_tactic_2837_, lean_object* v_allowFailure_2838_, uint8_t v_collectAll_2839_, uint8_t v_includeStar_2840_, uint8_t v___x_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_){
_start:
{
lean_object* v___x_2850_; 
v___x_2850_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercentHeartbeats_2834_, v___y_2844_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_a_2851_);
lean_dec_ref_known(v___x_2850_, 1);
v___x_2852_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___closed__0));
lean_inc(v_goal_2835_);
v___x_2853_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v___x_2852_, v_goal_2835_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v_a_2854_; lean_object* v___f_2855_; lean_object* v___x_2856_; 
v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
lean_inc(v_a_2854_);
lean_dec_ref_known(v___x_2853_, 1);
v___f_2855_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2855_, 0, v_a_2851_);
lean_closure_set(v___f_2855_, 1, v___x_2836_);
lean_closure_set(v___f_2855_, 2, v_tactic_2837_);
lean_closure_set(v___f_2855_, 3, v_allowFailure_2838_);
lean_inc_ref(v___f_2855_);
v___x_2856_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2855_, v_a_2854_, v_collectAll_2839_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
lean_dec(v_a_2854_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_object* v_a_2857_; 
v_a_2857_ = lean_ctor_get(v___x_2856_, 0);
lean_inc(v_a_2857_);
if (lean_obj_tag(v_a_2857_) == 0)
{
lean_dec_ref_known(v___x_2856_, 1);
lean_dec_ref(v___f_2855_);
lean_dec(v_goal_2835_);
goto v___jp_2847_;
}
else
{
lean_object* v_val_2858_; lean_object* v___x_2908_; lean_object* v___x_2909_; uint8_t v___x_2910_; 
v_val_2858_ = lean_ctor_get(v_a_2857_, 0);
v___x_2908_ = lean_unsigned_to_nat(0u);
v___x_2909_ = lean_array_get_size(v_val_2858_);
v___x_2910_ = lean_nat_dec_lt(v___x_2908_, v___x_2909_);
if (v___x_2910_ == 0)
{
goto v___jp_2904_;
}
else
{
if (v___x_2910_ == 0)
{
goto v___jp_2904_;
}
else
{
size_t v___x_2911_; size_t v___x_2912_; uint8_t v___x_2913_; 
v___x_2911_ = ((size_t)0ULL);
v___x_2912_ = lean_usize_of_nat(v___x_2909_);
v___x_2913_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_val_2858_, v___x_2911_, v___x_2912_);
if (v___x_2913_ == 0)
{
goto v___jp_2904_;
}
else
{
if (v___x_2841_ == 0)
{
goto v___jp_2903_;
}
else
{
lean_dec_ref_known(v_a_2857_, 1);
lean_dec_ref(v___f_2855_);
lean_dec(v_goal_2835_);
return v___x_2856_;
}
}
}
}
v___jp_2859_:
{
lean_object* v___x_2860_; 
v___x_2860_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2894_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2863_ = v___x_2860_;
v_isShared_2864_ = v_isSharedCheck_2894_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v___x_2860_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2894_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; uint8_t v___x_2867_; 
v___x_2865_ = lean_array_get_size(v_a_2861_);
v___x_2866_ = lean_unsigned_to_nat(0u);
v___x_2867_ = lean_nat_dec_eq(v___x_2865_, v___x_2866_);
if (v___x_2867_ == 0)
{
lean_object* v___x_2868_; lean_object* v_mctx_2869_; size_t v_sz_2870_; size_t v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
lean_inc(v_val_2858_);
lean_del_object(v___x_2863_);
lean_dec_ref_known(v_a_2857_, 1);
v___x_2868_ = lean_st_ref_get(v___y_2843_);
v_mctx_2869_ = lean_ctor_get(v___x_2868_, 0);
lean_inc_ref(v_mctx_2869_);
lean_dec(v___x_2868_);
v_sz_2870_ = lean_array_size(v_a_2861_);
v___x_2871_ = ((size_t)0ULL);
v___x_2872_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2835_, v_mctx_2869_, v_sz_2870_, v___x_2871_, v_a_2861_);
v___x_2873_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2855_, v___x_2872_, v_collectAll_2839_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
lean_dec_ref(v___x_2872_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2890_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2876_ = v___x_2873_;
v_isShared_2877_ = v_isSharedCheck_2890_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2873_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2890_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
if (lean_obj_tag(v_a_2874_) == 0)
{
lean_del_object(v___x_2876_);
lean_dec(v_val_2858_);
goto v___jp_2847_;
}
else
{
lean_object* v_val_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2889_; 
v_val_2878_ = lean_ctor_get(v_a_2874_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v_a_2874_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2880_ = v_a_2874_;
v_isShared_2881_ = v_isSharedCheck_2889_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_val_2878_);
lean_dec(v_a_2874_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2889_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2882_; lean_object* v___x_2884_; 
v___x_2882_ = l_Array_append___redArg(v_val_2858_, v_val_2878_);
lean_dec(v_val_2878_);
if (v_isShared_2881_ == 0)
{
lean_ctor_set(v___x_2880_, 0, v___x_2882_);
v___x_2884_ = v___x_2880_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v___x_2882_);
v___x_2884_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
lean_object* v___x_2886_; 
if (v_isShared_2877_ == 0)
{
lean_ctor_set(v___x_2876_, 0, v___x_2884_);
v___x_2886_ = v___x_2876_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v___x_2884_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
}
}
}
}
else
{
lean_dec(v_val_2858_);
return v___x_2873_;
}
}
else
{
lean_object* v___x_2892_; 
lean_dec(v_a_2861_);
lean_dec_ref(v___f_2855_);
lean_dec(v_goal_2835_);
if (v_isShared_2864_ == 0)
{
lean_ctor_set(v___x_2863_, 0, v_a_2857_);
v___x_2892_ = v___x_2863_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_a_2857_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
}
else
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2902_; 
lean_dec_ref_known(v_a_2857_, 1);
lean_dec_ref(v___f_2855_);
lean_dec(v_goal_2835_);
v_a_2895_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2897_ = v___x_2860_;
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2860_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2900_; 
if (v_isShared_2898_ == 0)
{
v___x_2900_ = v___x_2897_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_a_2895_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
}
v___jp_2903_:
{
if (v_includeStar_2840_ == 0)
{
if (v___x_2841_ == 0)
{
lean_dec_ref_known(v___x_2856_, 1);
goto v___jp_2859_;
}
else
{
lean_dec_ref_known(v_a_2857_, 1);
lean_dec_ref(v___f_2855_);
lean_dec(v_goal_2835_);
return v___x_2856_;
}
}
else
{
lean_dec_ref_known(v___x_2856_, 1);
goto v___jp_2859_;
}
}
v___jp_2904_:
{
if (v_collectAll_2839_ == 0)
{
if (v___x_2841_ == 0)
{
goto v___jp_2903_;
}
else
{
lean_object* v___x_2905_; lean_object* v___x_2906_; uint8_t v___x_2907_; 
v___x_2905_ = lean_array_get_size(v_val_2858_);
v___x_2906_ = lean_unsigned_to_nat(0u);
v___x_2907_ = lean_nat_dec_eq(v___x_2905_, v___x_2906_);
if (v___x_2907_ == 0)
{
lean_dec_ref_known(v_a_2857_, 1);
lean_dec_ref(v___f_2855_);
lean_dec(v_goal_2835_);
return v___x_2856_;
}
else
{
goto v___jp_2903_;
}
}
}
else
{
goto v___jp_2903_;
}
}
}
}
else
{
lean_dec_ref(v___f_2855_);
lean_dec(v_goal_2835_);
return v___x_2856_;
}
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
lean_dec(v_a_2851_);
lean_dec_ref(v_allowFailure_2838_);
lean_dec_ref(v_tactic_2837_);
lean_dec_ref(v___x_2836_);
lean_dec(v_goal_2835_);
v_a_2914_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2853_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2853_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2914_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
}
else
{
lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
lean_dec_ref(v_allowFailure_2838_);
lean_dec_ref(v_tactic_2837_);
lean_dec_ref(v___x_2836_);
lean_dec(v_goal_2835_);
v_a_2922_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2924_ = v___x_2850_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2850_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2922_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
v___jp_2847_:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2848_ = lean_box(0);
v___x_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2848_);
return v___x_2849_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__5___boxed(lean_object* v_leavePercentHeartbeats_2930_, lean_object* v_goal_2931_, lean_object* v___x_2932_, lean_object* v_tactic_2933_, lean_object* v_allowFailure_2934_, lean_object* v_collectAll_2935_, lean_object* v_includeStar_2936_, lean_object* v___x_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
uint8_t v_collectAll_boxed_2943_; uint8_t v_includeStar_boxed_2944_; uint8_t v___x_16002__boxed_2945_; lean_object* v_res_2946_; 
v_collectAll_boxed_2943_ = lean_unbox(v_collectAll_2935_);
v_includeStar_boxed_2944_ = lean_unbox(v_includeStar_2936_);
v___x_16002__boxed_2945_ = lean_unbox(v___x_2937_);
v_res_2946_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__5(v_leavePercentHeartbeats_2930_, v_goal_2931_, v___x_2932_, v_tactic_2933_, v_allowFailure_2934_, v_collectAll_boxed_2943_, v_includeStar_boxed_2944_, v___x_16002__boxed_2945_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec(v_leavePercentHeartbeats_2930_);
return v_res_2946_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(lean_object* v_e_2947_){
_start:
{
if (lean_obj_tag(v_e_2947_) == 0)
{
uint8_t v___x_2948_; 
v___x_2948_ = 2;
return v___x_2948_;
}
else
{
lean_object* v_a_2949_; 
v_a_2949_ = lean_ctor_get(v_e_2947_, 0);
if (lean_obj_tag(v_a_2949_) == 0)
{
uint8_t v___x_2950_; 
v___x_2950_ = 1;
return v___x_2950_;
}
else
{
uint8_t v___x_2951_; 
v___x_2951_ = 0;
return v___x_2951_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4___boxed(lean_object* v_e_2952_){
_start:
{
uint8_t v_res_2953_; lean_object* v_r_2954_; 
v_res_2953_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(v_e_2952_);
lean_dec_ref(v_e_2952_);
v_r_2954_ = lean_box(v_res_2953_);
return v_r_2954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(lean_object* v_cls_2955_, uint8_t v_collapsed_2956_, lean_object* v_tag_2957_, lean_object* v_opts_2958_, uint8_t v_clsEnabled_2959_, lean_object* v_oldTraces_2960_, lean_object* v_msg_2961_, lean_object* v_resStartStop_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
lean_object* v_fst_2968_; lean_object* v_snd_2969_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v_data_2973_; lean_object* v_fst_2984_; lean_object* v_snd_2985_; lean_object* v___x_2986_; uint8_t v___x_2987_; lean_object* v___y_2989_; lean_object* v_a_2990_; uint8_t v___y_3005_; double v___y_3036_; 
v_fst_2968_ = lean_ctor_get(v_resStartStop_2962_, 0);
lean_inc(v_fst_2968_);
v_snd_2969_ = lean_ctor_get(v_resStartStop_2962_, 1);
lean_inc(v_snd_2969_);
lean_dec_ref(v_resStartStop_2962_);
v_fst_2984_ = lean_ctor_get(v_snd_2969_, 0);
lean_inc(v_fst_2984_);
v_snd_2985_ = lean_ctor_get(v_snd_2969_, 1);
lean_inc(v_snd_2985_);
lean_dec(v_snd_2969_);
v___x_2986_ = l_Lean_trace_profiler;
v___x_2987_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_2958_, v___x_2986_);
if (v___x_2987_ == 0)
{
v___y_3005_ = v___x_2987_;
goto v___jp_3004_;
}
else
{
lean_object* v___x_3041_; uint8_t v___x_3042_; 
v___x_3041_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3042_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_2958_, v___x_3041_);
if (v___x_3042_ == 0)
{
lean_object* v___x_3043_; lean_object* v___x_3044_; double v___x_3045_; double v___x_3046_; double v___x_3047_; 
v___x_3043_ = l_Lean_trace_profiler_threshold;
v___x_3044_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_2958_, v___x_3043_);
v___x_3045_ = lean_float_of_nat(v___x_3044_);
v___x_3046_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3);
v___x_3047_ = lean_float_div(v___x_3045_, v___x_3046_);
v___y_3036_ = v___x_3047_;
goto v___jp_3035_;
}
else
{
lean_object* v___x_3048_; lean_object* v___x_3049_; double v___x_3050_; 
v___x_3048_ = l_Lean_trace_profiler_threshold;
v___x_3049_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_2958_, v___x_3048_);
v___x_3050_ = lean_float_of_nat(v___x_3049_);
v___y_3036_ = v___x_3050_;
goto v___jp_3035_;
}
}
v___jp_2970_:
{
lean_object* v___x_2974_; 
lean_inc(v___y_2972_);
v___x_2974_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(v_oldTraces_2960_, v_data_2973_, v___y_2972_, v___y_2971_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v___x_2975_; 
lean_dec_ref_known(v___x_2974_, 1);
v___x_2975_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_2968_);
return v___x_2975_;
}
else
{
lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2983_; 
lean_dec(v_fst_2968_);
v_a_2976_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2978_ = v___x_2974_;
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_dec(v___x_2974_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2981_; 
if (v_isShared_2979_ == 0)
{
v___x_2981_ = v___x_2978_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_a_2976_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
return v___x_2981_;
}
}
}
}
v___jp_2988_:
{
uint8_t v_result_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; double v___x_2994_; lean_object* v_data_2995_; 
v_result_2991_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(v_fst_2968_);
v___x_2992_ = lean_box(v_result_2991_);
v___x_2993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2992_);
v___x_2994_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0);
lean_inc_ref(v_tag_2957_);
lean_inc_ref(v___x_2993_);
lean_inc(v_cls_2955_);
v_data_2995_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2995_, 0, v_cls_2955_);
lean_ctor_set(v_data_2995_, 1, v___x_2993_);
lean_ctor_set(v_data_2995_, 2, v_tag_2957_);
lean_ctor_set_float(v_data_2995_, sizeof(void*)*3, v___x_2994_);
lean_ctor_set_float(v_data_2995_, sizeof(void*)*3 + 8, v___x_2994_);
lean_ctor_set_uint8(v_data_2995_, sizeof(void*)*3 + 16, v_collapsed_2956_);
if (v___x_2987_ == 0)
{
lean_dec_ref_known(v___x_2993_, 1);
lean_dec(v_snd_2985_);
lean_dec(v_fst_2984_);
lean_dec_ref(v_tag_2957_);
lean_dec(v_cls_2955_);
v___y_2971_ = v_a_2990_;
v___y_2972_ = v___y_2989_;
v_data_2973_ = v_data_2995_;
goto v___jp_2970_;
}
else
{
lean_object* v_data_2996_; double v___x_2997_; double v___x_2998_; 
lean_dec_ref_known(v_data_2995_, 3);
v_data_2996_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2996_, 0, v_cls_2955_);
lean_ctor_set(v_data_2996_, 1, v___x_2993_);
lean_ctor_set(v_data_2996_, 2, v_tag_2957_);
v___x_2997_ = lean_unbox_float(v_fst_2984_);
lean_dec(v_fst_2984_);
lean_ctor_set_float(v_data_2996_, sizeof(void*)*3, v___x_2997_);
v___x_2998_ = lean_unbox_float(v_snd_2985_);
lean_dec(v_snd_2985_);
lean_ctor_set_float(v_data_2996_, sizeof(void*)*3 + 8, v___x_2998_);
lean_ctor_set_uint8(v_data_2996_, sizeof(void*)*3 + 16, v_collapsed_2956_);
v___y_2971_ = v_a_2990_;
v___y_2972_ = v___y_2989_;
v_data_2973_ = v_data_2996_;
goto v___jp_2970_;
}
}
v___jp_2999_:
{
lean_object* v_ref_3000_; lean_object* v___x_3001_; 
v_ref_3000_ = lean_ctor_get(v___y_2965_, 5);
lean_inc(v___y_2966_);
lean_inc_ref(v___y_2965_);
lean_inc(v___y_2964_);
lean_inc_ref(v___y_2963_);
lean_inc(v_fst_2968_);
v___x_3001_ = lean_apply_6(v_msg_2961_, v_fst_2968_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, lean_box(0));
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v_a_3002_; 
v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
lean_inc(v_a_3002_);
lean_dec_ref_known(v___x_3001_, 1);
v___y_2989_ = v_ref_3000_;
v_a_2990_ = v_a_3002_;
goto v___jp_2988_;
}
else
{
lean_object* v___x_3003_; 
lean_dec_ref_known(v___x_3001_, 1);
v___x_3003_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2);
v___y_2989_ = v_ref_3000_;
v_a_2990_ = v___x_3003_;
goto v___jp_2988_;
}
}
v___jp_3004_:
{
if (v_clsEnabled_2959_ == 0)
{
if (v___y_3005_ == 0)
{
lean_object* v___x_3006_; lean_object* v_traceState_3007_; lean_object* v_env_3008_; lean_object* v_nextMacroScope_3009_; lean_object* v_ngen_3010_; lean_object* v_auxDeclNGen_3011_; lean_object* v_cache_3012_; lean_object* v_messages_3013_; lean_object* v_infoState_3014_; lean_object* v_snapshotTasks_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3034_; 
lean_dec(v_snd_2985_);
lean_dec(v_fst_2984_);
lean_dec_ref(v_msg_2961_);
lean_dec_ref(v_tag_2957_);
lean_dec(v_cls_2955_);
v___x_3006_ = lean_st_ref_take(v___y_2966_);
v_traceState_3007_ = lean_ctor_get(v___x_3006_, 4);
v_env_3008_ = lean_ctor_get(v___x_3006_, 0);
v_nextMacroScope_3009_ = lean_ctor_get(v___x_3006_, 1);
v_ngen_3010_ = lean_ctor_get(v___x_3006_, 2);
v_auxDeclNGen_3011_ = lean_ctor_get(v___x_3006_, 3);
v_cache_3012_ = lean_ctor_get(v___x_3006_, 5);
v_messages_3013_ = lean_ctor_get(v___x_3006_, 6);
v_infoState_3014_ = lean_ctor_get(v___x_3006_, 7);
v_snapshotTasks_3015_ = lean_ctor_get(v___x_3006_, 8);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3017_ = v___x_3006_;
v_isShared_3018_ = v_isSharedCheck_3034_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_snapshotTasks_3015_);
lean_inc(v_infoState_3014_);
lean_inc(v_messages_3013_);
lean_inc(v_cache_3012_);
lean_inc(v_traceState_3007_);
lean_inc(v_auxDeclNGen_3011_);
lean_inc(v_ngen_3010_);
lean_inc(v_nextMacroScope_3009_);
lean_inc(v_env_3008_);
lean_dec(v___x_3006_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3034_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
uint64_t v_tid_3019_; lean_object* v_traces_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3033_; 
v_tid_3019_ = lean_ctor_get_uint64(v_traceState_3007_, sizeof(void*)*1);
v_traces_3020_ = lean_ctor_get(v_traceState_3007_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v_traceState_3007_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3022_ = v_traceState_3007_;
v_isShared_3023_ = v_isSharedCheck_3033_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_traces_3020_);
lean_dec(v_traceState_3007_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3033_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3024_; lean_object* v___x_3026_; 
v___x_3024_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2960_, v_traces_3020_);
lean_dec_ref(v_traces_3020_);
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 0, v___x_3024_);
v___x_3026_ = v___x_3022_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v___x_3024_);
lean_ctor_set_uint64(v_reuseFailAlloc_3032_, sizeof(void*)*1, v_tid_3019_);
v___x_3026_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
lean_object* v___x_3028_; 
if (v_isShared_3018_ == 0)
{
lean_ctor_set(v___x_3017_, 4, v___x_3026_);
v___x_3028_ = v___x_3017_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_env_3008_);
lean_ctor_set(v_reuseFailAlloc_3031_, 1, v_nextMacroScope_3009_);
lean_ctor_set(v_reuseFailAlloc_3031_, 2, v_ngen_3010_);
lean_ctor_set(v_reuseFailAlloc_3031_, 3, v_auxDeclNGen_3011_);
lean_ctor_set(v_reuseFailAlloc_3031_, 4, v___x_3026_);
lean_ctor_set(v_reuseFailAlloc_3031_, 5, v_cache_3012_);
lean_ctor_set(v_reuseFailAlloc_3031_, 6, v_messages_3013_);
lean_ctor_set(v_reuseFailAlloc_3031_, 7, v_infoState_3014_);
lean_ctor_set(v_reuseFailAlloc_3031_, 8, v_snapshotTasks_3015_);
v___x_3028_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3029_ = lean_st_ref_set(v___y_2966_, v___x_3028_);
v___x_3030_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_2968_);
return v___x_3030_;
}
}
}
}
}
else
{
goto v___jp_2999_;
}
}
else
{
goto v___jp_2999_;
}
}
v___jp_3035_:
{
double v___x_3037_; double v___x_3038_; double v___x_3039_; uint8_t v___x_3040_; 
v___x_3037_ = lean_unbox_float(v_snd_2985_);
v___x_3038_ = lean_unbox_float(v_fst_2984_);
v___x_3039_ = lean_float_sub(v___x_3037_, v___x_3038_);
v___x_3040_ = lean_float_decLt(v___y_3036_, v___x_3039_);
v___y_3005_ = v___x_3040_;
goto v___jp_3004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4___boxed(lean_object* v_cls_3051_, lean_object* v_collapsed_3052_, lean_object* v_tag_3053_, lean_object* v_opts_3054_, lean_object* v_clsEnabled_3055_, lean_object* v_oldTraces_3056_, lean_object* v_msg_3057_, lean_object* v_resStartStop_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
uint8_t v_collapsed_boxed_3064_; uint8_t v_clsEnabled_boxed_3065_; lean_object* v_res_3066_; 
v_collapsed_boxed_3064_ = lean_unbox(v_collapsed_3052_);
v_clsEnabled_boxed_3065_ = lean_unbox(v_clsEnabled_3055_);
v_res_3066_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v_cls_3051_, v_collapsed_boxed_3064_, v_tag_3053_, v_opts_3054_, v_clsEnabled_boxed_3065_, v_oldTraces_3056_, v_msg_3057_, v_resStartStop_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec_ref(v_opts_3054_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(lean_object* v_goal_3070_, lean_object* v_tactic_3071_, lean_object* v_allowFailure_3072_, lean_object* v_leavePercentHeartbeats_3073_, uint8_t v_includeStar_3074_, uint8_t v_collectAll_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_){
_start:
{
lean_object* v_options_3081_; lean_object* v_inheritedTraceOptions_3082_; uint8_t v_hasTrace_3083_; lean_object* v___x_3084_; 
v_options_3081_ = lean_ctor_get(v_a_3078_, 2);
v_inheritedTraceOptions_3082_ = lean_ctor_get(v_a_3078_, 13);
v_hasTrace_3083_ = lean_ctor_get_uint8(v_options_3081_, sizeof(void*)*1);
v___x_3084_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
if (v_hasTrace_3083_ == 0)
{
lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___f_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3085_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___closed__0));
v___x_3086_ = lean_box(v_collectAll_3075_);
v___x_3087_ = lean_box(v_includeStar_3074_);
v___f_3088_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed), 12, 7);
lean_closure_set(v___f_3088_, 0, v_leavePercentHeartbeats_3073_);
lean_closure_set(v___f_3088_, 1, v_goal_3070_);
lean_closure_set(v___f_3088_, 2, v___x_3085_);
lean_closure_set(v___f_3088_, 3, v_tactic_3071_);
lean_closure_set(v___f_3088_, 4, v_allowFailure_3072_);
lean_closure_set(v___f_3088_, 5, v___x_3086_);
lean_closure_set(v___f_3088_, 6, v___x_3087_);
v___x_3089_ = lean_box(0);
v___x_3090_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_3084_, v_options_3081_, v___f_3088_, v___x_3089_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
return v___x_3090_;
}
else
{
lean_object* v___f_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; uint8_t v___x_3095_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v_a_3099_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v_a_3114_; 
lean_inc(v_goal_3070_);
v___f_3091_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2___boxed), 7, 1);
lean_closure_set(v___f_3091_, 0, v_goal_3070_);
v___x_3092_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_3093_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__4));
v___x_3094_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2);
v___x_3095_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3082_, v_options_3081_, v___x_3094_);
if (v___x_3095_ == 0)
{
lean_object* v___x_3178_; uint8_t v___x_3179_; 
v___x_3178_ = l_Lean_trace_profiler;
v___x_3179_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_3081_, v___x_3178_);
if (v___x_3179_ == 0)
{
uint8_t v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___f_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
lean_dec_ref(v___f_3091_);
v___x_3180_ = 0;
v___x_3181_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3181_, 0, v___x_3180_);
lean_ctor_set_uint8(v___x_3181_, 1, v_hasTrace_3083_);
lean_ctor_set_uint8(v___x_3181_, 2, v_hasTrace_3083_);
lean_ctor_set_uint8(v___x_3181_, 3, v_hasTrace_3083_);
v___x_3182_ = lean_box(v_collectAll_3075_);
v___x_3183_ = lean_box(v_includeStar_3074_);
v___x_3184_ = lean_box(v___x_3179_);
v___f_3185_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4___boxed), 13, 8);
lean_closure_set(v___f_3185_, 0, v_leavePercentHeartbeats_3073_);
lean_closure_set(v___f_3185_, 1, v_goal_3070_);
lean_closure_set(v___f_3185_, 2, v___x_3181_);
lean_closure_set(v___f_3185_, 3, v_tactic_3071_);
lean_closure_set(v___f_3185_, 4, v_allowFailure_3072_);
lean_closure_set(v___f_3185_, 5, v___x_3182_);
lean_closure_set(v___f_3185_, 6, v___x_3183_);
lean_closure_set(v___f_3185_, 7, v___x_3184_);
v___x_3186_ = lean_box(0);
v___x_3187_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_3084_, v_options_3081_, v___f_3185_, v___x_3186_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
return v___x_3187_;
}
else
{
goto v___jp_3123_;
}
}
else
{
goto v___jp_3123_;
}
v___jp_3096_:
{
lean_object* v___x_3100_; double v___x_3101_; double v___x_3102_; double v___x_3103_; double v___x_3104_; double v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___x_3100_ = lean_io_mono_nanos_now();
v___x_3101_ = lean_float_of_nat(v___y_3098_);
v___x_3102_ = lean_float_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3);
v___x_3103_ = lean_float_div(v___x_3101_, v___x_3102_);
v___x_3104_ = lean_float_of_nat(v___x_3100_);
v___x_3105_ = lean_float_div(v___x_3104_, v___x_3102_);
v___x_3106_ = lean_box_float(v___x_3103_);
v___x_3107_ = lean_box_float(v___x_3105_);
v___x_3108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3106_);
lean_ctor_set(v___x_3108_, 1, v___x_3107_);
v___x_3109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3109_, 0, v_a_3099_);
lean_ctor_set(v___x_3109_, 1, v___x_3108_);
v___x_3110_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v___x_3092_, v_hasTrace_3083_, v___x_3093_, v_options_3081_, v___x_3095_, v___y_3097_, v___f_3091_, v___x_3109_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
return v___x_3110_;
}
v___jp_3111_:
{
lean_object* v___x_3115_; double v___x_3116_; double v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3115_ = lean_io_get_num_heartbeats();
v___x_3116_ = lean_float_of_nat(v___y_3112_);
v___x_3117_ = lean_float_of_nat(v___x_3115_);
v___x_3118_ = lean_box_float(v___x_3116_);
v___x_3119_ = lean_box_float(v___x_3117_);
v___x_3120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3120_, 0, v___x_3118_);
lean_ctor_set(v___x_3120_, 1, v___x_3119_);
v___x_3121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3121_, 0, v_a_3114_);
lean_ctor_set(v___x_3121_, 1, v___x_3120_);
v___x_3122_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v___x_3092_, v_hasTrace_3083_, v___x_3093_, v_options_3081_, v___x_3095_, v___y_3113_, v___f_3091_, v___x_3121_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
return v___x_3122_;
}
v___jp_3123_:
{
lean_object* v___x_3124_; lean_object* v_a_3125_; lean_object* v___x_3126_; uint8_t v___x_3127_; 
v___x_3124_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v_a_3079_);
v_a_3125_ = lean_ctor_get(v___x_3124_, 0);
lean_inc(v_a_3125_);
lean_dec_ref(v___x_3124_);
v___x_3126_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3127_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_3081_, v___x_3126_);
if (v___x_3127_ == 0)
{
lean_object* v___x_3128_; uint8_t v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___f_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3128_ = lean_io_mono_nanos_now();
v___x_3129_ = 0;
v___x_3130_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3130_, 0, v___x_3129_);
lean_ctor_set_uint8(v___x_3130_, 1, v_hasTrace_3083_);
lean_ctor_set_uint8(v___x_3130_, 2, v_hasTrace_3083_);
lean_ctor_set_uint8(v___x_3130_, 3, v_hasTrace_3083_);
v___x_3131_ = lean_box(v_collectAll_3075_);
v___x_3132_ = lean_box(v_includeStar_3074_);
v___x_3133_ = lean_box(v___x_3127_);
v___f_3134_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4___boxed), 13, 8);
lean_closure_set(v___f_3134_, 0, v_leavePercentHeartbeats_3073_);
lean_closure_set(v___f_3134_, 1, v_goal_3070_);
lean_closure_set(v___f_3134_, 2, v___x_3130_);
lean_closure_set(v___f_3134_, 3, v_tactic_3071_);
lean_closure_set(v___f_3134_, 4, v_allowFailure_3072_);
lean_closure_set(v___f_3134_, 5, v___x_3131_);
lean_closure_set(v___f_3134_, 6, v___x_3132_);
lean_closure_set(v___f_3134_, 7, v___x_3133_);
v___x_3135_ = lean_box(0);
v___x_3136_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_3084_, v_options_3081_, v___f_3134_, v___x_3135_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
if (lean_obj_tag(v___x_3136_) == 0)
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3144_; 
v_a_3137_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3139_ = v___x_3136_;
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3136_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3142_; 
if (v_isShared_3140_ == 0)
{
lean_ctor_set_tag(v___x_3139_, 1);
v___x_3142_ = v___x_3139_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_a_3137_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
v___y_3097_ = v_a_3125_;
v___y_3098_ = v___x_3128_;
v_a_3099_ = v___x_3142_;
goto v___jp_3096_;
}
}
}
else
{
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3152_; 
v_a_3145_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3147_ = v___x_3136_;
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_3136_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3150_; 
if (v_isShared_3148_ == 0)
{
lean_ctor_set_tag(v___x_3147_, 0);
v___x_3150_ = v___x_3147_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_a_3145_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
v___y_3097_ = v_a_3125_;
v___y_3098_ = v___x_3128_;
v_a_3099_ = v___x_3150_;
goto v___jp_3096_;
}
}
}
}
else
{
lean_object* v___x_3153_; uint8_t v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___f_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___x_3153_ = lean_io_get_num_heartbeats();
v___x_3154_ = 0;
v___x_3155_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3155_, 0, v___x_3154_);
lean_ctor_set_uint8(v___x_3155_, 1, v___x_3127_);
lean_ctor_set_uint8(v___x_3155_, 2, v___x_3127_);
lean_ctor_set_uint8(v___x_3155_, 3, v___x_3127_);
v___x_3156_ = lean_box(v_collectAll_3075_);
v___x_3157_ = lean_box(v_includeStar_3074_);
v___x_3158_ = lean_box(v___x_3127_);
v___f_3159_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__5___boxed), 13, 8);
lean_closure_set(v___f_3159_, 0, v_leavePercentHeartbeats_3073_);
lean_closure_set(v___f_3159_, 1, v_goal_3070_);
lean_closure_set(v___f_3159_, 2, v___x_3155_);
lean_closure_set(v___f_3159_, 3, v_tactic_3071_);
lean_closure_set(v___f_3159_, 4, v_allowFailure_3072_);
lean_closure_set(v___f_3159_, 5, v___x_3156_);
lean_closure_set(v___f_3159_, 6, v___x_3157_);
lean_closure_set(v___f_3159_, 7, v___x_3158_);
v___x_3160_ = lean_box(0);
v___x_3161_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_3084_, v_options_3081_, v___f_3159_, v___x_3160_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
if (lean_obj_tag(v___x_3161_) == 0)
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
v_a_3162_ = lean_ctor_get(v___x_3161_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_3161_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3161_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
lean_ctor_set_tag(v___x_3164_, 1);
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_a_3162_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
v___y_3112_ = v___x_3153_;
v___y_3113_ = v_a_3125_;
v_a_3114_ = v___x_3167_;
goto v___jp_3111_;
}
}
}
else
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3177_; 
v_a_3170_ = lean_ctor_get(v___x_3161_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3172_ = v___x_3161_;
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3161_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3175_; 
if (v_isShared_3173_ == 0)
{
lean_ctor_set_tag(v___x_3172_, 0);
v___x_3175_ = v___x_3172_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_a_3170_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
v___y_3112_ = v___x_3153_;
v___y_3113_ = v_a_3125_;
v_a_3114_ = v___x_3175_;
goto v___jp_3111_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___boxed(lean_object* v_goal_3188_, lean_object* v_tactic_3189_, lean_object* v_allowFailure_3190_, lean_object* v_leavePercentHeartbeats_3191_, lean_object* v_includeStar_3192_, lean_object* v_collectAll_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_){
_start:
{
uint8_t v_includeStar_boxed_3199_; uint8_t v_collectAll_boxed_3200_; lean_object* v_res_3201_; 
v_includeStar_boxed_3199_ = lean_unbox(v_includeStar_3192_);
v_collectAll_boxed_3200_ = lean_unbox(v_collectAll_3193_);
v_res_3201_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(v_goal_3188_, v_tactic_3189_, v_allowFailure_3190_, v_leavePercentHeartbeats_3191_, v_includeStar_boxed_3199_, v_collectAll_boxed_3200_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_);
lean_dec(v_a_3197_);
lean_dec_ref(v_a_3196_);
lean_dec(v_a_3195_);
lean_dec_ref(v_a_3194_);
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearch(lean_object* v_goal_3202_, lean_object* v_tactic_3203_, lean_object* v_allowFailure_3204_, lean_object* v_leavePercentHeartbeats_3205_, uint8_t v_includeStar_3206_, uint8_t v_collectAll_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_){
_start:
{
lean_object* v___x_3213_; 
v___x_3213_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(v_goal_3202_, v_tactic_3203_, v_allowFailure_3204_, v_leavePercentHeartbeats_3205_, v_includeStar_3206_, v_collectAll_3207_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_);
return v___x_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearch___boxed(lean_object* v_goal_3214_, lean_object* v_tactic_3215_, lean_object* v_allowFailure_3216_, lean_object* v_leavePercentHeartbeats_3217_, lean_object* v_includeStar_3218_, lean_object* v_collectAll_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_){
_start:
{
uint8_t v_includeStar_boxed_3225_; uint8_t v_collectAll_boxed_3226_; lean_object* v_res_3227_; 
v_includeStar_boxed_3225_ = lean_unbox(v_includeStar_3218_);
v_collectAll_boxed_3226_ = lean_unbox(v_collectAll_3219_);
v_res_3227_ = l_Lean_Meta_LibrarySearch_librarySearch(v_goal_3214_, v_tactic_3215_, v_allowFailure_3216_, v_leavePercentHeartbeats_3217_, v_includeStar_boxed_3225_, v_collectAll_boxed_3226_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_);
lean_dec(v_a_3223_);
lean_dec_ref(v_a_3222_);
lean_dec(v_a_3221_);
lean_dec_ref(v_a_3220_);
return v_res_3227_;
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
