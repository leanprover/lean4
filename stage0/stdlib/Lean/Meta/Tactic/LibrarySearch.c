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
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withSuppressedMessages___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_3813__boxed_226_; uint8_t v_res_227_; lean_object* v_r_228_; 
v___x_3813__boxed_226_ = lean_unbox(v___x_224_);
v_res_227_ = l_Lean_Meta_LibrarySearch_tryDischarger___lam__1(v___x_3813__boxed_226_, v_x_225_);
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
lean_object* v_a_773_; uint8_t v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_a_773_);
lean_dec_ref_known(v___x_772_, 1);
v___x_774_ = 2;
v___x_775_ = lean_box(v___x_774_);
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v_name_743_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_a_755_, v___x_760_, v___x_776_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_787_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_787_ == 0)
{
v___x_780_ = v___x_777_;
v_isShared_781_ = v_isSharedCheck_787_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_777_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_787_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_782_ = lean_array_push(v___x_762_, v_a_773_);
v___x_783_ = lean_array_push(v___x_782_, v_a_778_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_783_);
v___x_785_ = v___x_780_;
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
lean_dec(v_a_773_);
lean_dec_ref(v___x_762_);
v_a_788_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_777_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_777_);
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
lean_object* v___x_831_; lean_object* v_env_832_; uint8_t v___x_833_; 
v___x_831_ = lean_st_ref_get(v_a_829_);
v_env_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc_ref(v_env_832_);
lean_dec(v___x_831_);
lean_inc(v_name_824_);
v___x_833_ = l_Lean_Linter_isDeprecated(v_env_832_, v_name_824_);
if (v___x_833_ == 0)
{
uint8_t v___x_834_; 
lean_inc(v_name_824_);
v___x_834_ = l_Lean_Name_isMetaprogramming(v_name_824_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; lean_object* v_type_836_; lean_object* v___f_837_; lean_object* v___x_838_; 
v___x_835_ = l_Lean_AsyncConstantInfo_toConstantVal(v_c_825_);
v_type_836_ = lean_ctor_get(v___x_835_, 2);
lean_inc_ref(v_type_836_);
lean_dec_ref(v___x_835_);
v___f_837_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___boxed), 8, 1);
lean_closure_set(v___f_837_, 0, v_name_824_);
v___x_838_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(v_type_836_, v___f_837_, v___x_834_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
return v___x_838_;
}
else
{
lean_object* v___x_839_; lean_object* v___x_840_; 
lean_dec_ref(v_c_825_);
lean_dec(v_name_824_);
v___x_839_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___closed__0));
v___x_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
return v___x_840_;
}
}
else
{
lean_object* v___x_841_; lean_object* v___x_842_; 
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
uint8_t v___x_646__boxed_992_; lean_object* v_res_993_; 
v___x_646__boxed_992_ = lean_unbox(v___x_985_);
v_res_993_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0(v___x_646__boxed_992_, v___x_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
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
uint8_t v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1104_ = lean_nat_dec_lt(v___y_1103_, v___x_1098_);
v___x_1105_ = lean_unsigned_to_nat(0u);
lean_inc(v_g_1096_);
lean_inc(v_f_1094_);
v___x_1106_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(v___y_1103_, v_x_1095_, v_f_1094_, v_y_1097_, v_g_1096_, v___x_1105_, v_res_1101_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1107_; size_t v_sz_1108_; size_t v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
lean_dec(v_f_1094_);
v___x_1107_ = l_Array_extract___redArg(v_y_1097_, v___y_1103_, v___x_1099_);
v_sz_1108_ = lean_array_size(v___x_1107_);
v___x_1109_ = ((size_t)0ULL);
v___x_1110_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_g_1096_, v_sz_1108_, v___x_1109_, v___x_1107_);
v___x_1111_ = l_Array_append___redArg(v___x_1106_, v___x_1110_);
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
v___x_1116_ = l_Array_append___redArg(v___x_1106_, v___x_1115_);
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
lean_object* v_a_1368_; lean_object* v___x_1369_; lean_object* v_mctx_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
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
v___x_1372_ = lean_alloc_closure((void*)(l_Lean_MVarId_applySymm___boxed), 6, 1);
lean_closure_set(v___x_1372_, 0, v_goal_1359_);
v___x_1373_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(v___x_1372_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1434_; 
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1376_ = v___x_1373_;
v_isShared_1377_ = v_isSharedCheck_1434_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1373_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1434_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
if (lean_obj_tag(v_a_1374_) == 1)
{
lean_object* v_val_1378_; lean_object* v___x_1379_; 
lean_del_object(v___x_1376_);
v_val_1378_ = lean_ctor_get(v_a_1374_, 0);
lean_inc_n(v_val_1378_, 2);
lean_dec_ref_known(v_a_1374_, 1);
v___x_1379_ = l_Lean_MVarId_getType(v_val_1378_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1381_; lean_object* v_a_1382_; lean_object* v___x_1383_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_a_1380_);
lean_dec_ref_known(v___x_1379_, 1);
v___x_1381_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(v_a_1380_, v_a_1361_);
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1382_);
lean_dec_ref(v___x_1381_);
lean_inc(v_a_1363_);
lean_inc_ref(v_a_1362_);
lean_inc(v_a_1361_);
lean_inc_ref(v_a_1360_);
v___x_1383_ = lean_apply_6(v_searchFn_1358_, v_a_1382_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, lean_box(0));
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1411_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1386_ = v___x_1383_;
v_isShared_1387_ = v_isSharedCheck_1411_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1383_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1411_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v_cache_1390_; lean_object* v_zetaDeltaFVarIds_1391_; lean_object* v_postponed_1392_; lean_object* v_diag_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1409_; 
v___x_1388_ = lean_st_ref_get(v_a_1361_);
v___x_1389_ = lean_st_ref_take(v_a_1361_);
v_cache_1390_ = lean_ctor_get(v___x_1389_, 1);
v_zetaDeltaFVarIds_1391_ = lean_ctor_get(v___x_1389_, 2);
v_postponed_1392_ = lean_ctor_get(v___x_1389_, 3);
v_diag_1393_ = lean_ctor_get(v___x_1389_, 4);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1409_ == 0)
{
lean_object* v_unused_1410_; 
v_unused_1410_ = lean_ctor_get(v___x_1389_, 0);
lean_dec(v_unused_1410_);
v___x_1395_ = v___x_1389_;
v_isShared_1396_ = v_isSharedCheck_1409_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_diag_1393_);
lean_inc(v_postponed_1392_);
lean_inc(v_zetaDeltaFVarIds_1391_);
lean_inc(v_cache_1390_);
lean_dec(v___x_1389_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1409_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 0, v_mctx_1370_);
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_mctx_1370_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_cache_1390_);
lean_ctor_set(v_reuseFailAlloc_1408_, 2, v_zetaDeltaFVarIds_1391_);
lean_ctor_set(v_reuseFailAlloc_1408_, 3, v_postponed_1392_);
lean_ctor_set(v_reuseFailAlloc_1408_, 4, v_diag_1393_);
v___x_1398_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
lean_object* v___x_1399_; lean_object* v_mctx_1400_; lean_object* v___f_1401_; lean_object* v___x_1402_; lean_object* v___f_1403_; lean_object* v___x_1404_; lean_object* v___x_1406_; 
v___x_1399_ = lean_st_ref_put(v_a_1361_, v___x_1398_);
v_mctx_1400_ = lean_ctor_get(v___x_1388_, 0);
lean_inc_ref(v_mctx_1400_);
lean_dec(v___x_1388_);
v___f_1401_ = lean_alloc_closure((void*)(l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0), 2, 1);
lean_closure_set(v___f_1401_, 0, v___x_1371_);
v___x_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1402_, 0, v_val_1378_);
lean_ctor_set(v___x_1402_, 1, v_mctx_1400_);
v___f_1403_ = lean_alloc_closure((void*)(l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0), 2, 1);
lean_closure_set(v___f_1403_, 0, v___x_1402_);
v___x_1404_ = l_Lean_Meta_LibrarySearch_interleaveWith___redArg(v___f_1401_, v_a_1368_, v___f_1403_, v_a_1384_);
lean_dec(v_a_1384_);
lean_dec(v_a_1368_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 0, v___x_1404_);
v___x_1406_ = v___x_1386_;
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
lean_dec(v_val_1378_);
lean_dec_ref_known(v___x_1371_, 2);
lean_dec_ref(v_mctx_1370_);
lean_dec(v_a_1368_);
v_a_1412_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___x_1383_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1383_);
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
lean_dec(v_val_1378_);
lean_dec_ref_known(v___x_1371_, 2);
lean_dec_ref(v_mctx_1370_);
lean_dec(v_a_1368_);
lean_dec_ref(v_searchFn_1358_);
v_a_1420_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v___x_1379_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1379_);
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
lean_dec(v_a_1374_);
lean_dec_ref(v_mctx_1370_);
lean_dec_ref(v_searchFn_1358_);
v_sz_1428_ = lean_array_size(v_a_1368_);
v___x_1429_ = ((size_t)0ULL);
v___x_1430_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(v___x_1371_, v_sz_1428_, v___x_1429_, v_a_1368_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 0, v___x_1430_);
v___x_1432_ = v___x_1376_;
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
lean_dec_ref_known(v___x_1371_, 2);
lean_dec_ref(v_mctx_1370_);
lean_dec(v_a_1368_);
lean_dec_ref(v_searchFn_1358_);
v_a_1435_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1437_ = v___x_1373_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1373_);
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
lean_object* v___x_1520_; 
v___x_1520_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_lem_1513_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
if (lean_obj_tag(v___x_1520_) == 0)
{
switch(v_mod_1514_)
{
case 0:
{
return v___x_1520_;
}
case 1:
{
lean_object* v_a_1521_; lean_object* v___f_1522_; lean_object* v___x_1523_; 
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_a_1521_);
lean_dec_ref_known(v___x_1520_, 1);
v___f_1522_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__0));
v___x_1523_ = l_Lean_Meta_mapForallTelescope(v___f_1522_, v_a_1521_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
return v___x_1523_;
}
default: 
{
lean_object* v_a_1524_; lean_object* v___f_1525_; lean_object* v___x_1526_; 
v_a_1524_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_a_1524_);
lean_dec_ref_known(v___x_1520_, 1);
v___f_1525_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__1));
v___x_1526_ = l_Lean_Meta_mapForallTelescope(v___f_1525_, v_a_1524_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
return v___x_1526_;
}
}
}
else
{
return v___x_1520_;
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
lean_object* v___x_1555_; lean_object* v_traceState_1556_; lean_object* v_traces_1557_; lean_object* v___x_1558_; lean_object* v_traceState_1559_; lean_object* v_env_1560_; lean_object* v_nextMacroScope_1561_; lean_object* v_ngen_1562_; lean_object* v_auxDeclNGen_1563_; lean_object* v_cache_1564_; lean_object* v_messages_1565_; lean_object* v_infoState_1566_; lean_object* v_snapshotTasks_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1586_; 
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
v_messages_1565_ = lean_ctor_get(v___x_1558_, 6);
v_infoState_1566_ = lean_ctor_get(v___x_1558_, 7);
v_snapshotTasks_1567_ = lean_ctor_get(v___x_1558_, 8);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1569_ = v___x_1558_;
v_isShared_1570_ = v_isSharedCheck_1586_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_snapshotTasks_1567_);
lean_inc(v_infoState_1566_);
lean_inc(v_messages_1565_);
lean_inc(v_cache_1564_);
lean_inc(v_traceState_1559_);
lean_inc(v_auxDeclNGen_1563_);
lean_inc(v_ngen_1562_);
lean_inc(v_nextMacroScope_1561_);
lean_inc(v_env_1560_);
lean_dec(v___x_1558_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1586_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
uint64_t v_tid_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1584_; 
v_tid_1571_ = lean_ctor_get_uint64(v_traceState_1559_, sizeof(void*)*1);
v_isSharedCheck_1584_ = !lean_is_exclusive(v_traceState_1559_);
if (v_isSharedCheck_1584_ == 0)
{
lean_object* v_unused_1585_; 
v_unused_1585_ = lean_ctor_get(v_traceState_1559_, 0);
lean_dec(v_unused_1585_);
v___x_1573_ = v_traceState_1559_;
v_isShared_1574_ = v_isSharedCheck_1584_;
goto v_resetjp_1572_;
}
else
{
lean_dec(v_traceState_1559_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1584_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1575_; lean_object* v___x_1577_; 
v___x_1575_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 0, v___x_1575_);
v___x_1577_ = v___x_1573_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1575_);
lean_ctor_set_uint64(v_reuseFailAlloc_1583_, sizeof(void*)*1, v_tid_1571_);
v___x_1577_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
lean_object* v___x_1579_; 
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 4, v___x_1577_);
v___x_1579_ = v___x_1569_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_env_1560_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v_nextMacroScope_1561_);
lean_ctor_set(v_reuseFailAlloc_1582_, 2, v_ngen_1562_);
lean_ctor_set(v_reuseFailAlloc_1582_, 3, v_auxDeclNGen_1563_);
lean_ctor_set(v_reuseFailAlloc_1582_, 4, v___x_1577_);
lean_ctor_set(v_reuseFailAlloc_1582_, 5, v_cache_1564_);
lean_ctor_set(v_reuseFailAlloc_1582_, 6, v_messages_1565_);
lean_ctor_set(v_reuseFailAlloc_1582_, 7, v_infoState_1566_);
lean_ctor_set(v_reuseFailAlloc_1582_, 8, v_snapshotTasks_1567_);
v___x_1579_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = lean_st_ref_put(v___y_1553_, v___x_1579_);
v___x_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1581_, 0, v_traces_1557_);
return v___x_1581_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___boxed(lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v___y_1587_);
lean_dec(v___y_1587_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0(lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v___y_1593_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___boxed(lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0(v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
return v_res_1601_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(lean_object* v_opts_1602_, lean_object* v_opt_1603_){
_start:
{
lean_object* v_name_1604_; lean_object* v_defValue_1605_; lean_object* v_map_1606_; lean_object* v___x_1607_; 
v_name_1604_ = lean_ctor_get(v_opt_1603_, 0);
v_defValue_1605_ = lean_ctor_get(v_opt_1603_, 1);
v_map_1606_ = lean_ctor_get(v_opts_1602_, 0);
v___x_1607_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1606_, v_name_1604_);
if (lean_obj_tag(v___x_1607_) == 0)
{
uint8_t v___x_1608_; 
v___x_1608_ = lean_unbox(v_defValue_1605_);
return v___x_1608_;
}
else
{
lean_object* v_val_1609_; 
v_val_1609_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_val_1609_);
lean_dec_ref_known(v___x_1607_, 1);
if (lean_obj_tag(v_val_1609_) == 1)
{
uint8_t v_v_1610_; 
v_v_1610_ = lean_ctor_get_uint8(v_val_1609_, 0);
lean_dec_ref_known(v_val_1609_, 0);
return v_v_1610_;
}
else
{
uint8_t v___x_1611_; 
lean_dec(v_val_1609_);
v___x_1611_ = lean_unbox(v_defValue_1605_);
return v___x_1611_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1___boxed(lean_object* v_opts_1612_, lean_object* v_opt_1613_){
_start:
{
uint8_t v_res_1614_; lean_object* v_r_1615_; 
v_res_1614_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_1612_, v_opt_1613_);
lean_dec_ref(v_opt_1613_);
lean_dec_ref(v_opts_1612_);
v_r_1615_ = lean_box(v_res_1614_);
return v_r_1615_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1617_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__0));
v___x_1618_ = l_Lean_stringToMessageData(v___x_1617_);
return v___x_1618_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__2));
v___x_1621_ = l_Lean_stringToMessageData(v___x_1620_);
return v___x_1621_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1625_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__5));
v___x_1626_ = l_Lean_MessageData_ofFormat(v___x_1625_);
return v___x_1626_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1630_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__8));
v___x_1631_ = l_Lean_MessageData_ofFormat(v___x_1630_);
return v___x_1631_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12(void){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__11));
v___x_1636_ = l_Lean_MessageData_ofFormat(v___x_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0(lean_object* v_fst_1637_, uint8_t v_snd_1638_, lean_object* v_x_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___y_1649_; 
v___x_1645_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1);
v___x_1646_ = l_Lean_MessageData_ofName(v_fst_1637_);
v___x_1647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1645_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
switch(v_snd_1638_)
{
case 0:
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6);
v___y_1649_ = v___x_1654_;
goto v___jp_1648_;
}
case 1:
{
lean_object* v___x_1655_; 
v___x_1655_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9);
v___y_1649_ = v___x_1655_;
goto v___jp_1648_;
}
default: 
{
lean_object* v___x_1656_; 
v___x_1656_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12);
v___y_1649_ = v___x_1656_;
goto v___jp_1648_;
}
}
v___jp_1648_:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
lean_inc_ref(v___y_1649_);
v___x_1650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1647_);
lean_ctor_set(v___x_1650_, 1, v___y_1649_);
v___x_1651_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3);
v___x_1652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1650_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
v___x_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
return v___x_1653_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___boxed(lean_object* v_fst_1657_, lean_object* v_snd_1658_, lean_object* v_x_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
uint8_t v_snd_10990__boxed_1665_; lean_object* v_res_1666_; 
v_snd_10990__boxed_1665_ = lean_unbox(v_snd_1658_);
v_res_1666_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0(v_fst_1657_, v_snd_10990__boxed_1665_, v_x_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec_ref(v_x_1659_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(lean_object* v_opts_1667_, lean_object* v_opt_1668_){
_start:
{
lean_object* v_name_1669_; lean_object* v_defValue_1670_; lean_object* v_map_1671_; lean_object* v___x_1672_; 
v_name_1669_ = lean_ctor_get(v_opt_1668_, 0);
v_defValue_1670_ = lean_ctor_get(v_opt_1668_, 1);
v_map_1671_ = lean_ctor_get(v_opts_1667_, 0);
v___x_1672_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1671_, v_name_1669_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_inc(v_defValue_1670_);
return v_defValue_1670_;
}
else
{
lean_object* v_val_1673_; 
v_val_1673_ = lean_ctor_get(v___x_1672_, 0);
lean_inc(v_val_1673_);
lean_dec_ref_known(v___x_1672_, 1);
if (lean_obj_tag(v_val_1673_) == 3)
{
lean_object* v_v_1674_; 
v_v_1674_ = lean_ctor_get(v_val_1673_, 0);
lean_inc(v_v_1674_);
lean_dec_ref_known(v_val_1673_, 1);
return v_v_1674_;
}
else
{
lean_dec(v_val_1673_);
lean_inc(v_defValue_1670_);
return v_defValue_1670_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5___boxed(lean_object* v_opts_1675_, lean_object* v_opt_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_1675_, v_opt_1676_);
lean_dec_ref(v_opt_1676_);
lean_dec_ref(v_opts_1675_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(lean_object* v_x_1678_){
_start:
{
if (lean_obj_tag(v_x_1678_) == 0)
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1687_; 
v_a_1680_ = lean_ctor_get(v_x_1678_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v_x_1678_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1682_ = v_x_1678_;
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v_x_1678_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1685_; 
if (v_isShared_1683_ == 0)
{
lean_ctor_set_tag(v___x_1682_, 1);
v___x_1685_ = v___x_1682_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1680_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
else
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
v_a_1688_ = lean_ctor_get(v_x_1678_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v_x_1678_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1690_ = v_x_1678_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v_x_1678_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
lean_ctor_set_tag(v___x_1690_, 0);
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg___boxed(lean_object* v_x_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_x_1696_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3(size_t v_sz_1699_, size_t v_i_1700_, lean_object* v_bs_1701_){
_start:
{
uint8_t v___x_1702_; 
v___x_1702_ = lean_usize_dec_lt(v_i_1700_, v_sz_1699_);
if (v___x_1702_ == 0)
{
return v_bs_1701_;
}
else
{
lean_object* v_v_1703_; lean_object* v_msg_1704_; lean_object* v___x_1705_; lean_object* v_bs_x27_1706_; size_t v___x_1707_; size_t v___x_1708_; lean_object* v___x_1709_; 
v_v_1703_ = lean_array_uget_borrowed(v_bs_1701_, v_i_1700_);
v_msg_1704_ = lean_ctor_get(v_v_1703_, 1);
lean_inc_ref(v_msg_1704_);
v___x_1705_ = lean_unsigned_to_nat(0u);
v_bs_x27_1706_ = lean_array_uset(v_bs_1701_, v_i_1700_, v___x_1705_);
v___x_1707_ = ((size_t)1ULL);
v___x_1708_ = lean_usize_add(v_i_1700_, v___x_1707_);
v___x_1709_ = lean_array_uset(v_bs_x27_1706_, v_i_1700_, v_msg_1704_);
v_i_1700_ = v___x_1708_;
v_bs_1701_ = v___x_1709_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_1711_, lean_object* v_i_1712_, lean_object* v_bs_1713_){
_start:
{
size_t v_sz_boxed_1714_; size_t v_i_boxed_1715_; lean_object* v_res_1716_; 
v_sz_boxed_1714_ = lean_unbox_usize(v_sz_1711_);
lean_dec(v_sz_1711_);
v_i_boxed_1715_ = lean_unbox_usize(v_i_1712_);
lean_dec(v_i_1712_);
v_res_1716_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3(v_sz_boxed_1714_, v_i_boxed_1715_, v_bs_1713_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(lean_object* v_oldTraces_1717_, lean_object* v_data_1718_, lean_object* v_ref_1719_, lean_object* v_msg_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v_toCold_1726_; lean_object* v_currRecDepth_1727_; lean_object* v_ref_1728_; uint8_t v_diag_1729_; uint8_t v_suppressElabErrors_1730_; lean_object* v___x_1731_; lean_object* v_traceState_1732_; lean_object* v_traces_1733_; lean_object* v_ref_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; size_t v_sz_1737_; size_t v___x_1738_; lean_object* v___x_1739_; lean_object* v_msg_1740_; lean_object* v___x_1741_; lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1779_; 
v_toCold_1726_ = lean_ctor_get(v___y_1723_, 0);
v_currRecDepth_1727_ = lean_ctor_get(v___y_1723_, 1);
v_ref_1728_ = lean_ctor_get(v___y_1723_, 2);
v_diag_1729_ = lean_ctor_get_uint8(v___y_1723_, sizeof(void*)*3);
v_suppressElabErrors_1730_ = lean_ctor_get_uint8(v___y_1723_, sizeof(void*)*3 + 1);
v___x_1731_ = lean_st_ref_get(v___y_1724_);
v_traceState_1732_ = lean_ctor_get(v___x_1731_, 4);
lean_inc_ref(v_traceState_1732_);
lean_dec(v___x_1731_);
v_traces_1733_ = lean_ctor_get(v_traceState_1732_, 0);
lean_inc_ref(v_traces_1733_);
lean_dec_ref(v_traceState_1732_);
v_ref_1734_ = l_Lean_replaceRef(v_ref_1719_, v_ref_1728_);
lean_inc(v_currRecDepth_1727_);
lean_inc_ref(v_toCold_1726_);
v___x_1735_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1735_, 0, v_toCold_1726_);
lean_ctor_set(v___x_1735_, 1, v_currRecDepth_1727_);
lean_ctor_set(v___x_1735_, 2, v_ref_1734_);
lean_ctor_set_uint8(v___x_1735_, sizeof(void*)*3, v_diag_1729_);
lean_ctor_set_uint8(v___x_1735_, sizeof(void*)*3 + 1, v_suppressElabErrors_1730_);
v___x_1736_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1733_);
lean_dec_ref(v_traces_1733_);
v_sz_1737_ = lean_array_size(v___x_1736_);
v___x_1738_ = ((size_t)0ULL);
v___x_1739_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3(v_sz_1737_, v___x_1738_, v___x_1736_);
v_msg_1740_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1740_, 0, v_data_1718_);
lean_ctor_set(v_msg_1740_, 1, v_msg_1720_);
lean_ctor_set(v_msg_1740_, 2, v___x_1739_);
v___x_1741_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(v_msg_1740_, v___y_1721_, v___y_1722_, v___x_1735_, v___y_1724_);
lean_dec_ref_known(v___x_1735_, 3);
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1744_ = v___x_1741_;
v_isShared_1745_ = v_isSharedCheck_1779_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1741_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1779_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1746_; lean_object* v_traceState_1747_; lean_object* v_env_1748_; lean_object* v_nextMacroScope_1749_; lean_object* v_ngen_1750_; lean_object* v_auxDeclNGen_1751_; lean_object* v_cache_1752_; lean_object* v_messages_1753_; lean_object* v_infoState_1754_; lean_object* v_snapshotTasks_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1778_; 
v___x_1746_ = lean_st_ref_take(v___y_1724_);
v_traceState_1747_ = lean_ctor_get(v___x_1746_, 4);
v_env_1748_ = lean_ctor_get(v___x_1746_, 0);
v_nextMacroScope_1749_ = lean_ctor_get(v___x_1746_, 1);
v_ngen_1750_ = lean_ctor_get(v___x_1746_, 2);
v_auxDeclNGen_1751_ = lean_ctor_get(v___x_1746_, 3);
v_cache_1752_ = lean_ctor_get(v___x_1746_, 5);
v_messages_1753_ = lean_ctor_get(v___x_1746_, 6);
v_infoState_1754_ = lean_ctor_get(v___x_1746_, 7);
v_snapshotTasks_1755_ = lean_ctor_get(v___x_1746_, 8);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1757_ = v___x_1746_;
v_isShared_1758_ = v_isSharedCheck_1778_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_snapshotTasks_1755_);
lean_inc(v_infoState_1754_);
lean_inc(v_messages_1753_);
lean_inc(v_cache_1752_);
lean_inc(v_traceState_1747_);
lean_inc(v_auxDeclNGen_1751_);
lean_inc(v_ngen_1750_);
lean_inc(v_nextMacroScope_1749_);
lean_inc(v_env_1748_);
lean_dec(v___x_1746_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1778_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
uint64_t v_tid_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1776_; 
v_tid_1759_ = lean_ctor_get_uint64(v_traceState_1747_, sizeof(void*)*1);
v_isSharedCheck_1776_ = !lean_is_exclusive(v_traceState_1747_);
if (v_isSharedCheck_1776_ == 0)
{
lean_object* v_unused_1777_; 
v_unused_1777_ = lean_ctor_get(v_traceState_1747_, 0);
lean_dec(v_unused_1777_);
v___x_1761_ = v_traceState_1747_;
v_isShared_1762_ = v_isSharedCheck_1776_;
goto v_resetjp_1760_;
}
else
{
lean_dec(v_traceState_1747_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1776_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1766_; 
v___x_1763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1763_, 0, v_ref_1719_);
lean_ctor_set(v___x_1763_, 1, v_a_1742_);
v___x_1764_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1717_, v___x_1763_);
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 0, v___x_1764_);
v___x_1766_ = v___x_1761_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1764_);
lean_ctor_set_uint64(v_reuseFailAlloc_1775_, sizeof(void*)*1, v_tid_1759_);
v___x_1766_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
lean_object* v___x_1768_; 
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 4, v___x_1766_);
v___x_1768_ = v___x_1757_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_env_1748_);
lean_ctor_set(v_reuseFailAlloc_1774_, 1, v_nextMacroScope_1749_);
lean_ctor_set(v_reuseFailAlloc_1774_, 2, v_ngen_1750_);
lean_ctor_set(v_reuseFailAlloc_1774_, 3, v_auxDeclNGen_1751_);
lean_ctor_set(v_reuseFailAlloc_1774_, 4, v___x_1766_);
lean_ctor_set(v_reuseFailAlloc_1774_, 5, v_cache_1752_);
lean_ctor_set(v_reuseFailAlloc_1774_, 6, v_messages_1753_);
lean_ctor_set(v_reuseFailAlloc_1774_, 7, v_infoState_1754_);
lean_ctor_set(v_reuseFailAlloc_1774_, 8, v_snapshotTasks_1755_);
v___x_1768_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1772_; 
v___x_1769_ = lean_st_ref_put(v___y_1724_, v___x_1768_);
v___x_1770_ = lean_box(0);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 0, v___x_1770_);
v___x_1772_ = v___x_1744_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1770_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2___boxed(lean_object* v_oldTraces_1780_, lean_object* v_data_1781_, lean_object* v_ref_1782_, lean_object* v_msg_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(v_oldTraces_1780_, v_data_1781_, v_ref_1782_, v_msg_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
return v_res_1789_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(lean_object* v_e_1790_){
_start:
{
if (lean_obj_tag(v_e_1790_) == 0)
{
uint8_t v___x_1791_; 
v___x_1791_ = 2;
return v___x_1791_;
}
else
{
uint8_t v___x_1792_; 
v___x_1792_ = 0;
return v___x_1792_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4___boxed(lean_object* v_e_1793_){
_start:
{
uint8_t v_res_1794_; lean_object* v_r_1795_; 
v_res_1794_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(v_e_1793_);
lean_dec_ref(v_e_1793_);
v_r_1795_ = lean_box(v_res_1794_);
return v_r_1795_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1796_; double v___x_1797_; 
v___x_1796_ = lean_unsigned_to_nat(0u);
v___x_1797_ = lean_float_of_nat(v___x_1796_);
return v___x_1797_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1799_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__1));
v___x_1800_ = l_Lean_stringToMessageData(v___x_1799_);
return v___x_1800_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1801_; double v___x_1802_; 
v___x_1801_ = lean_unsigned_to_nat(1000u);
v___x_1802_ = lean_float_of_nat(v___x_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(lean_object* v_cls_1803_, uint8_t v_collapsed_1804_, lean_object* v_tag_1805_, lean_object* v_opts_1806_, uint8_t v_clsEnabled_1807_, lean_object* v_oldTraces_1808_, lean_object* v_msg_1809_, lean_object* v_resStartStop_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v_fst_1816_; lean_object* v_snd_1817_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v_data_1821_; lean_object* v_fst_1832_; lean_object* v_snd_1833_; lean_object* v___x_1834_; uint8_t v___x_1835_; lean_object* v___y_1837_; lean_object* v_a_1838_; uint8_t v___y_1853_; double v___y_1884_; 
v_fst_1816_ = lean_ctor_get(v_resStartStop_1810_, 0);
lean_inc(v_fst_1816_);
v_snd_1817_ = lean_ctor_get(v_resStartStop_1810_, 1);
lean_inc(v_snd_1817_);
lean_dec_ref(v_resStartStop_1810_);
v_fst_1832_ = lean_ctor_get(v_snd_1817_, 0);
lean_inc(v_fst_1832_);
v_snd_1833_ = lean_ctor_get(v_snd_1817_, 1);
lean_inc(v_snd_1833_);
lean_dec(v_snd_1817_);
v___x_1834_ = l_Lean_trace_profiler;
v___x_1835_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_1806_, v___x_1834_);
if (v___x_1835_ == 0)
{
v___y_1853_ = v___x_1835_;
goto v___jp_1852_;
}
else
{
lean_object* v___x_1889_; uint8_t v___x_1890_; 
v___x_1889_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1890_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_1806_, v___x_1889_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; lean_object* v___x_1892_; double v___x_1893_; double v___x_1894_; double v___x_1895_; 
v___x_1891_ = l_Lean_trace_profiler_threshold;
v___x_1892_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_1806_, v___x_1891_);
v___x_1893_ = lean_float_of_nat(v___x_1892_);
v___x_1894_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3);
v___x_1895_ = lean_float_div(v___x_1893_, v___x_1894_);
v___y_1884_ = v___x_1895_;
goto v___jp_1883_;
}
else
{
lean_object* v___x_1896_; lean_object* v___x_1897_; double v___x_1898_; 
v___x_1896_ = l_Lean_trace_profiler_threshold;
v___x_1897_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_1806_, v___x_1896_);
v___x_1898_ = lean_float_of_nat(v___x_1897_);
v___y_1884_ = v___x_1898_;
goto v___jp_1883_;
}
}
v___jp_1818_:
{
lean_object* v___x_1822_; 
lean_inc(v___y_1820_);
v___x_1822_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(v_oldTraces_1808_, v_data_1821_, v___y_1820_, v___y_1819_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v___x_1823_; 
lean_dec_ref_known(v___x_1822_, 1);
v___x_1823_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_1816_);
return v___x_1823_;
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
lean_dec(v_fst_1816_);
v_a_1824_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1822_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1822_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
v___jp_1836_:
{
uint8_t v_result_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; double v___x_1842_; lean_object* v_data_1843_; 
v_result_1839_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(v_fst_1816_);
v___x_1840_ = lean_box(v_result_1839_);
v___x_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1840_);
v___x_1842_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0);
lean_inc_ref(v_tag_1805_);
lean_inc_ref(v___x_1841_);
lean_inc(v_cls_1803_);
v_data_1843_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1843_, 0, v_cls_1803_);
lean_ctor_set(v_data_1843_, 1, v___x_1841_);
lean_ctor_set(v_data_1843_, 2, v_tag_1805_);
lean_ctor_set_float(v_data_1843_, sizeof(void*)*3, v___x_1842_);
lean_ctor_set_float(v_data_1843_, sizeof(void*)*3 + 8, v___x_1842_);
lean_ctor_set_uint8(v_data_1843_, sizeof(void*)*3 + 16, v_collapsed_1804_);
if (v___x_1835_ == 0)
{
lean_dec_ref_known(v___x_1841_, 1);
lean_dec(v_snd_1833_);
lean_dec(v_fst_1832_);
lean_dec_ref(v_tag_1805_);
lean_dec(v_cls_1803_);
v___y_1819_ = v_a_1838_;
v___y_1820_ = v___y_1837_;
v_data_1821_ = v_data_1843_;
goto v___jp_1818_;
}
else
{
lean_object* v_data_1844_; double v___x_1845_; double v___x_1846_; 
lean_dec_ref_known(v_data_1843_, 3);
v_data_1844_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1844_, 0, v_cls_1803_);
lean_ctor_set(v_data_1844_, 1, v___x_1841_);
lean_ctor_set(v_data_1844_, 2, v_tag_1805_);
v___x_1845_ = lean_unbox_float(v_fst_1832_);
lean_dec(v_fst_1832_);
lean_ctor_set_float(v_data_1844_, sizeof(void*)*3, v___x_1845_);
v___x_1846_ = lean_unbox_float(v_snd_1833_);
lean_dec(v_snd_1833_);
lean_ctor_set_float(v_data_1844_, sizeof(void*)*3 + 8, v___x_1846_);
lean_ctor_set_uint8(v_data_1844_, sizeof(void*)*3 + 16, v_collapsed_1804_);
v___y_1819_ = v_a_1838_;
v___y_1820_ = v___y_1837_;
v_data_1821_ = v_data_1844_;
goto v___jp_1818_;
}
}
v___jp_1847_:
{
lean_object* v_ref_1848_; lean_object* v___x_1849_; 
v_ref_1848_ = lean_ctor_get(v___y_1813_, 2);
lean_inc(v___y_1814_);
lean_inc_ref(v___y_1813_);
lean_inc(v___y_1812_);
lean_inc_ref(v___y_1811_);
lean_inc(v_fst_1816_);
v___x_1849_ = lean_apply_6(v_msg_1809_, v_fst_1816_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, lean_box(0));
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; 
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc(v_a_1850_);
lean_dec_ref_known(v___x_1849_, 1);
v___y_1837_ = v_ref_1848_;
v_a_1838_ = v_a_1850_;
goto v___jp_1836_;
}
else
{
lean_object* v___x_1851_; 
lean_dec_ref_known(v___x_1849_, 1);
v___x_1851_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2);
v___y_1837_ = v_ref_1848_;
v_a_1838_ = v___x_1851_;
goto v___jp_1836_;
}
}
v___jp_1852_:
{
if (v_clsEnabled_1807_ == 0)
{
if (v___y_1853_ == 0)
{
lean_object* v___x_1854_; lean_object* v_traceState_1855_; lean_object* v_env_1856_; lean_object* v_nextMacroScope_1857_; lean_object* v_ngen_1858_; lean_object* v_auxDeclNGen_1859_; lean_object* v_cache_1860_; lean_object* v_messages_1861_; lean_object* v_infoState_1862_; lean_object* v_snapshotTasks_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1882_; 
lean_dec(v_snd_1833_);
lean_dec(v_fst_1832_);
lean_dec_ref(v_msg_1809_);
lean_dec_ref(v_tag_1805_);
lean_dec(v_cls_1803_);
v___x_1854_ = lean_st_ref_take(v___y_1814_);
v_traceState_1855_ = lean_ctor_get(v___x_1854_, 4);
v_env_1856_ = lean_ctor_get(v___x_1854_, 0);
v_nextMacroScope_1857_ = lean_ctor_get(v___x_1854_, 1);
v_ngen_1858_ = lean_ctor_get(v___x_1854_, 2);
v_auxDeclNGen_1859_ = lean_ctor_get(v___x_1854_, 3);
v_cache_1860_ = lean_ctor_get(v___x_1854_, 5);
v_messages_1861_ = lean_ctor_get(v___x_1854_, 6);
v_infoState_1862_ = lean_ctor_get(v___x_1854_, 7);
v_snapshotTasks_1863_ = lean_ctor_get(v___x_1854_, 8);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1865_ = v___x_1854_;
v_isShared_1866_ = v_isSharedCheck_1882_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_snapshotTasks_1863_);
lean_inc(v_infoState_1862_);
lean_inc(v_messages_1861_);
lean_inc(v_cache_1860_);
lean_inc(v_traceState_1855_);
lean_inc(v_auxDeclNGen_1859_);
lean_inc(v_ngen_1858_);
lean_inc(v_nextMacroScope_1857_);
lean_inc(v_env_1856_);
lean_dec(v___x_1854_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1882_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
uint64_t v_tid_1867_; lean_object* v_traces_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1881_; 
v_tid_1867_ = lean_ctor_get_uint64(v_traceState_1855_, sizeof(void*)*1);
v_traces_1868_ = lean_ctor_get(v_traceState_1855_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v_traceState_1855_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1870_ = v_traceState_1855_;
v_isShared_1871_ = v_isSharedCheck_1881_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_traces_1868_);
lean_dec(v_traceState_1855_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1881_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1872_; lean_object* v___x_1874_; 
v___x_1872_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1808_, v_traces_1868_);
lean_dec_ref(v_traces_1868_);
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 0, v___x_1872_);
v___x_1874_ = v___x_1870_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1872_);
lean_ctor_set_uint64(v_reuseFailAlloc_1880_, sizeof(void*)*1, v_tid_1867_);
v___x_1874_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
lean_object* v___x_1876_; 
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 4, v___x_1874_);
v___x_1876_ = v___x_1865_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_env_1856_);
lean_ctor_set(v_reuseFailAlloc_1879_, 1, v_nextMacroScope_1857_);
lean_ctor_set(v_reuseFailAlloc_1879_, 2, v_ngen_1858_);
lean_ctor_set(v_reuseFailAlloc_1879_, 3, v_auxDeclNGen_1859_);
lean_ctor_set(v_reuseFailAlloc_1879_, 4, v___x_1874_);
lean_ctor_set(v_reuseFailAlloc_1879_, 5, v_cache_1860_);
lean_ctor_set(v_reuseFailAlloc_1879_, 6, v_messages_1861_);
lean_ctor_set(v_reuseFailAlloc_1879_, 7, v_infoState_1862_);
lean_ctor_set(v_reuseFailAlloc_1879_, 8, v_snapshotTasks_1863_);
v___x_1876_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1877_ = lean_st_ref_put(v___y_1814_, v___x_1876_);
v___x_1878_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_1816_);
return v___x_1878_;
}
}
}
}
}
else
{
goto v___jp_1847_;
}
}
else
{
goto v___jp_1847_;
}
}
v___jp_1883_:
{
double v___x_1885_; double v___x_1886_; double v___x_1887_; uint8_t v___x_1888_; 
v___x_1885_ = lean_unbox_float(v_snd_1833_);
v___x_1886_ = lean_unbox_float(v_fst_1832_);
v___x_1887_ = lean_float_sub(v___x_1885_, v___x_1886_);
v___x_1888_ = lean_float_decLt(v___y_1884_, v___x_1887_);
v___y_1853_ = v___x_1888_;
goto v___jp_1852_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___boxed(lean_object* v_cls_1899_, lean_object* v_collapsed_1900_, lean_object* v_tag_1901_, lean_object* v_opts_1902_, lean_object* v_clsEnabled_1903_, lean_object* v_oldTraces_1904_, lean_object* v_msg_1905_, lean_object* v_resStartStop_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
uint8_t v_collapsed_boxed_1912_; uint8_t v_clsEnabled_boxed_1913_; lean_object* v_res_1914_; 
v_collapsed_boxed_1912_ = lean_unbox(v_collapsed_1900_);
v_clsEnabled_boxed_1913_ = lean_unbox(v_clsEnabled_1903_);
v_res_1914_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v_cls_1899_, v_collapsed_boxed_1912_, v_tag_1901_, v_opts_1902_, v_clsEnabled_boxed_1913_, v_oldTraces_1904_, v_msg_1905_, v_resStartStop_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec_ref(v_opts_1902_);
return v_res_1914_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2(void){
_start:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1918_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_1919_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__1));
v___x_1920_ = l_Lean_Name_append(v___x_1919_, v___x_1918_);
return v___x_1920_;
}
}
static double _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3(void){
_start:
{
lean_object* v___x_1921_; double v___x_1922_; 
v___x_1921_ = lean_unsigned_to_nat(1000000000u);
v___x_1922_ = lean_float_of_nat(v___x_1921_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(lean_object* v_cfg_1923_, lean_object* v_act_1924_, lean_object* v_allowFailure_1925_, lean_object* v_cand_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_){
_start:
{
lean_object* v_fst_1932_; lean_object* v_snd_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_2220_; 
v_fst_1932_ = lean_ctor_get(v_cand_1926_, 0);
v_snd_1933_ = lean_ctor_get(v_cand_1926_, 1);
v_isSharedCheck_2220_ = !lean_is_exclusive(v_cand_1926_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_1935_ = v_cand_1926_;
v_isShared_1936_ = v_isSharedCheck_2220_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_snd_1933_);
lean_inc(v_fst_1932_);
lean_dec(v_cand_1926_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_2220_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v_toCold_1937_; lean_object* v_options_1938_; uint8_t v_hasTrace_1939_; 
v_toCold_1937_ = lean_ctor_get(v_a_1929_, 0);
v_options_1938_ = lean_ctor_get(v_toCold_1937_, 2);
v_hasTrace_1939_ = lean_ctor_get_uint8(v_options_1938_, sizeof(void*)*1);
if (v_hasTrace_1939_ == 0)
{
lean_object* v_fst_1940_; lean_object* v_snd_1941_; lean_object* v_fst_1942_; lean_object* v_snd_1943_; lean_object* v___x_1944_; lean_object* v_cache_1945_; lean_object* v_zetaDeltaFVarIds_1946_; lean_object* v_postponed_1947_; lean_object* v_diag_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1996_; 
lean_del_object(v___x_1935_);
v_fst_1940_ = lean_ctor_get(v_fst_1932_, 0);
lean_inc(v_fst_1940_);
v_snd_1941_ = lean_ctor_get(v_fst_1932_, 1);
lean_inc(v_snd_1941_);
lean_dec(v_fst_1932_);
v_fst_1942_ = lean_ctor_get(v_snd_1933_, 0);
lean_inc(v_fst_1942_);
v_snd_1943_ = lean_ctor_get(v_snd_1933_, 1);
lean_inc(v_snd_1943_);
lean_dec(v_snd_1933_);
v___x_1944_ = lean_st_ref_take(v_a_1928_);
v_cache_1945_ = lean_ctor_get(v___x_1944_, 1);
v_zetaDeltaFVarIds_1946_ = lean_ctor_get(v___x_1944_, 2);
v_postponed_1947_ = lean_ctor_get(v___x_1944_, 3);
v_diag_1948_ = lean_ctor_get(v___x_1944_, 4);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1996_ == 0)
{
lean_object* v_unused_1997_; 
v_unused_1997_ = lean_ctor_get(v___x_1944_, 0);
lean_dec(v_unused_1997_);
v___x_1950_ = v___x_1944_;
v_isShared_1951_ = v_isSharedCheck_1996_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_diag_1948_);
lean_inc(v_postponed_1947_);
lean_inc(v_zetaDeltaFVarIds_1946_);
lean_inc(v_cache_1945_);
lean_dec(v___x_1944_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1996_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 0, v_snd_1941_);
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_snd_1941_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v_cache_1945_);
lean_ctor_set(v_reuseFailAlloc_1995_, 2, v_zetaDeltaFVarIds_1946_);
lean_ctor_set(v_reuseFailAlloc_1995_, 3, v_postponed_1947_);
lean_ctor_set(v_reuseFailAlloc_1995_, 4, v_diag_1948_);
v___x_1953_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
lean_object* v___x_1954_; uint8_t v___x_1955_; lean_object* v___x_1956_; 
v___x_1954_ = lean_st_ref_put(v_a_1928_, v___x_1953_);
v___x_1955_ = lean_unbox(v_snd_1943_);
lean_dec(v_snd_1943_);
v___x_1956_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_1942_, v___x_1955_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_a_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_a_1957_);
lean_dec_ref_known(v___x_1956_, 1);
v___x_1958_ = lean_box(0);
lean_inc(v_fst_1940_);
v___x_1959_ = l_Lean_MVarId_apply(v_fst_1940_, v_a_1957_, v_cfg_1923_, v___x_1958_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v_a_1960_; lean_object* v___x_1961_; 
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc_n(v_a_1960_, 2);
lean_dec_ref_known(v___x_1959_, 1);
lean_inc(v_a_1930_);
lean_inc_ref(v_a_1929_);
lean_inc(v_a_1928_);
lean_inc_ref(v_a_1927_);
v___x_1961_ = lean_apply_6(v_act_1924_, v_a_1960_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, lean_box(0));
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_dec(v_a_1960_);
lean_dec(v_fst_1940_);
lean_dec_ref(v_allowFailure_1925_);
return v___x_1961_;
}
else
{
lean_object* v_a_1962_; uint8_t v___y_1964_; uint8_t v___x_1985_; 
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_a_1962_);
v___x_1985_ = l_Lean_Exception_isInterrupt(v_a_1962_);
if (v___x_1985_ == 0)
{
uint8_t v___x_1986_; 
v___x_1986_ = l_Lean_Exception_isRuntime(v_a_1962_);
v___y_1964_ = v___x_1986_;
goto v___jp_1963_;
}
else
{
lean_dec(v_a_1962_);
v___y_1964_ = v___x_1985_;
goto v___jp_1963_;
}
v___jp_1963_:
{
if (v___y_1964_ == 0)
{
lean_object* v___x_1965_; 
lean_dec_ref_known(v___x_1961_, 1);
lean_inc(v_a_1930_);
lean_inc_ref(v_a_1929_);
lean_inc(v_a_1928_);
lean_inc_ref(v_a_1927_);
v___x_1965_ = lean_apply_6(v_allowFailure_1925_, v_fst_1940_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, lean_box(0));
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1976_; 
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1968_ = v___x_1965_;
v_isShared_1969_ = v_isSharedCheck_1976_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1965_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1976_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
uint8_t v___x_1970_; 
v___x_1970_ = lean_unbox(v_a_1966_);
lean_dec(v_a_1966_);
if (v___x_1970_ == 0)
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
lean_del_object(v___x_1968_);
lean_dec(v_a_1960_);
v___x_1971_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1);
v___x_1972_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_1971_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_);
return v___x_1972_;
}
else
{
lean_object* v___x_1974_; 
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 0, v_a_1960_);
v___x_1974_ = v___x_1968_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1960_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
else
{
lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1984_; 
lean_dec(v_a_1960_);
v_a_1977_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1979_ = v___x_1965_;
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v___x_1965_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1982_; 
if (v_isShared_1980_ == 0)
{
v___x_1982_ = v___x_1979_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_a_1977_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
}
else
{
lean_dec(v_a_1960_);
lean_dec(v_fst_1940_);
lean_dec_ref(v_allowFailure_1925_);
return v___x_1961_;
}
}
}
}
else
{
lean_dec(v_fst_1940_);
lean_dec_ref(v_allowFailure_1925_);
lean_dec_ref(v_act_1924_);
return v___x_1959_;
}
}
else
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
lean_dec(v_fst_1940_);
lean_dec_ref(v_allowFailure_1925_);
lean_dec_ref(v_act_1924_);
lean_dec_ref(v_cfg_1923_);
v_a_1987_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___x_1956_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1956_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_a_1987_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
}
}
else
{
lean_object* v_fst_1998_; lean_object* v_snd_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2219_; 
v_fst_1998_ = lean_ctor_get(v_fst_1932_, 0);
v_snd_1999_ = lean_ctor_get(v_fst_1932_, 1);
v_isSharedCheck_2219_ = !lean_is_exclusive(v_fst_1932_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2001_ = v_fst_1932_;
v_isShared_2002_ = v_isSharedCheck_2219_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_snd_1999_);
lean_inc(v_fst_1998_);
lean_dec(v_fst_1932_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2219_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v_fst_2003_; lean_object* v_snd_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2218_; 
v_fst_2003_ = lean_ctor_get(v_snd_1933_, 0);
v_snd_2004_ = lean_ctor_get(v_snd_1933_, 1);
v_isSharedCheck_2218_ = !lean_is_exclusive(v_snd_1933_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2006_ = v_snd_1933_;
v_isShared_2007_ = v_isSharedCheck_2218_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_snd_2004_);
lean_inc(v_fst_2003_);
lean_dec(v_snd_1933_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2218_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v_inheritedTraceOptions_2008_; lean_object* v___f_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; uint8_t v___x_2013_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v_a_2017_; lean_object* v___y_2034_; lean_object* v___y_2035_; lean_object* v_a_2036_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v_a_2041_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2050_; lean_object* v___y_2051_; lean_object* v___y_2052_; lean_object* v___y_2053_; uint8_t v___y_2054_; lean_object* v___y_2062_; lean_object* v___y_2063_; lean_object* v_a_2064_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v_a_2078_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v_a_2083_; lean_object* v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2088_; lean_object* v___y_2092_; lean_object* v___y_2093_; lean_object* v___y_2094_; lean_object* v___y_2095_; uint8_t v___y_2096_; 
v_inheritedTraceOptions_2008_ = lean_ctor_get(v_toCold_1937_, 11);
lean_inc(v_snd_2004_);
lean_inc(v_fst_2003_);
v___f_2009_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2009_, 0, v_fst_2003_);
lean_closure_set(v___f_2009_, 1, v_snd_2004_);
v___x_2010_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_2011_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__4));
v___x_2012_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2);
v___x_2013_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2008_, v_options_1938_, v___x_2012_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2162_; uint8_t v___x_2163_; 
v___x_2162_ = l_Lean_trace_profiler;
v___x_2163_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_1938_, v___x_2162_);
if (v___x_2163_ == 0)
{
lean_object* v___x_2164_; lean_object* v_cache_2165_; lean_object* v_zetaDeltaFVarIds_2166_; lean_object* v_postponed_2167_; lean_object* v_diag_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2216_; 
lean_dec_ref(v___f_2009_);
lean_del_object(v___x_2006_);
lean_del_object(v___x_2001_);
lean_del_object(v___x_1935_);
v___x_2164_ = lean_st_ref_take(v_a_1928_);
v_cache_2165_ = lean_ctor_get(v___x_2164_, 1);
v_zetaDeltaFVarIds_2166_ = lean_ctor_get(v___x_2164_, 2);
v_postponed_2167_ = lean_ctor_get(v___x_2164_, 3);
v_diag_2168_ = lean_ctor_get(v___x_2164_, 4);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2216_ == 0)
{
lean_object* v_unused_2217_; 
v_unused_2217_ = lean_ctor_get(v___x_2164_, 0);
lean_dec(v_unused_2217_);
v___x_2170_ = v___x_2164_;
v_isShared_2171_ = v_isSharedCheck_2216_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_diag_2168_);
lean_inc(v_postponed_2167_);
lean_inc(v_zetaDeltaFVarIds_2166_);
lean_inc(v_cache_2165_);
lean_dec(v___x_2164_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2216_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 0, v_snd_1999_);
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_snd_1999_);
lean_ctor_set(v_reuseFailAlloc_2215_, 1, v_cache_2165_);
lean_ctor_set(v_reuseFailAlloc_2215_, 2, v_zetaDeltaFVarIds_2166_);
lean_ctor_set(v_reuseFailAlloc_2215_, 3, v_postponed_2167_);
lean_ctor_set(v_reuseFailAlloc_2215_, 4, v_diag_2168_);
v___x_2173_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
lean_object* v___x_2174_; uint8_t v___x_2175_; lean_object* v___x_2176_; 
v___x_2174_ = lean_st_ref_put(v_a_1928_, v___x_2173_);
v___x_2175_ = lean_unbox(v_snd_2004_);
lean_dec(v_snd_2004_);
v___x_2176_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_2003_, v___x_2175_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_a_2177_);
lean_dec_ref_known(v___x_2176_, 1);
v___x_2178_ = lean_box(0);
lean_inc(v_fst_1998_);
v___x_2179_ = l_Lean_MVarId_apply(v_fst_1998_, v_a_2177_, v_cfg_1923_, v___x_2178_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; lean_object* v___x_2181_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc_n(v_a_2180_, 2);
lean_dec_ref_known(v___x_2179_, 1);
lean_inc(v_a_1930_);
lean_inc_ref(v_a_1929_);
lean_inc(v_a_1928_);
lean_inc_ref(v_a_1927_);
v___x_2181_ = lean_apply_6(v_act_1924_, v_a_2180_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, lean_box(0));
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_dec(v_a_2180_);
lean_dec(v_fst_1998_);
lean_dec_ref(v_allowFailure_1925_);
return v___x_2181_;
}
else
{
lean_object* v_a_2182_; uint8_t v___y_2184_; uint8_t v___x_2205_; 
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_a_2182_);
v___x_2205_ = l_Lean_Exception_isInterrupt(v_a_2182_);
if (v___x_2205_ == 0)
{
uint8_t v___x_2206_; 
v___x_2206_ = l_Lean_Exception_isRuntime(v_a_2182_);
v___y_2184_ = v___x_2206_;
goto v___jp_2183_;
}
else
{
lean_dec(v_a_2182_);
v___y_2184_ = v___x_2205_;
goto v___jp_2183_;
}
v___jp_2183_:
{
if (v___y_2184_ == 0)
{
lean_object* v___x_2185_; 
lean_dec_ref_known(v___x_2181_, 1);
lean_inc(v_a_1930_);
lean_inc_ref(v_a_1929_);
lean_inc(v_a_1928_);
lean_inc_ref(v_a_1927_);
v___x_2185_ = lean_apply_6(v_allowFailure_1925_, v_fst_1998_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, lean_box(0));
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2196_; 
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2188_ = v___x_2185_;
v_isShared_2189_ = v_isSharedCheck_2196_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2185_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2196_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
uint8_t v___x_2190_; 
v___x_2190_ = lean_unbox(v_a_2186_);
lean_dec(v_a_2186_);
if (v___x_2190_ == 0)
{
lean_object* v___x_2191_; lean_object* v___x_2192_; 
lean_del_object(v___x_2188_);
lean_dec(v_a_2180_);
v___x_2191_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1);
v___x_2192_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2191_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_);
return v___x_2192_;
}
else
{
lean_object* v___x_2194_; 
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 0, v_a_2180_);
v___x_2194_ = v___x_2188_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_a_2180_);
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
else
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
lean_dec(v_a_2180_);
v_a_2197_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2199_ = v___x_2185_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2185_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2197_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
else
{
lean_dec(v_a_2180_);
lean_dec(v_fst_1998_);
lean_dec_ref(v_allowFailure_1925_);
return v___x_2181_;
}
}
}
}
else
{
lean_dec(v_fst_1998_);
lean_dec_ref(v_allowFailure_1925_);
lean_dec_ref(v_act_1924_);
return v___x_2179_;
}
}
else
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
lean_dec(v_fst_1998_);
lean_dec_ref(v_allowFailure_1925_);
lean_dec_ref(v_act_1924_);
lean_dec_ref(v_cfg_1923_);
v_a_2207_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2176_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2176_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
}
}
else
{
goto v___jp_2103_;
}
}
else
{
goto v___jp_2103_;
}
v___jp_2014_:
{
lean_object* v___x_2018_; double v___x_2019_; double v___x_2020_; double v___x_2021_; double v___x_2022_; double v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2027_; 
v___x_2018_ = lean_io_mono_nanos_now();
v___x_2019_ = lean_float_of_nat(v___y_2016_);
v___x_2020_ = lean_float_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3);
v___x_2021_ = lean_float_div(v___x_2019_, v___x_2020_);
v___x_2022_ = lean_float_of_nat(v___x_2018_);
v___x_2023_ = lean_float_div(v___x_2022_, v___x_2020_);
v___x_2024_ = lean_box_float(v___x_2021_);
v___x_2025_ = lean_box_float(v___x_2023_);
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 1, v___x_2025_);
lean_ctor_set(v___x_2006_, 0, v___x_2024_);
v___x_2027_ = v___x_2006_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___x_2024_);
lean_ctor_set(v_reuseFailAlloc_2032_, 1, v___x_2025_);
v___x_2027_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
lean_object* v___x_2029_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 1, v___x_2027_);
lean_ctor_set(v___x_2001_, 0, v_a_2017_);
v___x_2029_ = v___x_2001_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2017_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
lean_object* v___x_2030_; 
v___x_2030_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v___x_2010_, v_hasTrace_1939_, v___x_2011_, v_options_1938_, v___x_2013_, v___y_2015_, v___f_2009_, v___x_2029_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_);
return v___x_2030_;
}
}
}
v___jp_2033_:
{
lean_object* v___x_2037_; 
v___x_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2037_, 0, v_a_2036_);
v___y_2015_ = v___y_2035_;
v___y_2016_ = v___y_2034_;
v_a_2017_ = v___x_2037_;
goto v___jp_2014_;
}
v___jp_2038_:
{
lean_object* v___x_2042_; 
v___x_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2042_, 0, v_a_2041_);
v___y_2015_ = v___y_2040_;
v___y_2016_ = v___y_2039_;
v_a_2017_ = v___x_2042_;
goto v___jp_2014_;
}
v___jp_2043_:
{
if (lean_obj_tag(v___y_2046_) == 0)
{
lean_object* v_a_2047_; 
v_a_2047_ = lean_ctor_get(v___y_2046_, 0);
lean_inc(v_a_2047_);
lean_dec_ref_known(v___y_2046_, 1);
v___y_2034_ = v___y_2045_;
v___y_2035_ = v___y_2044_;
v_a_2036_ = v_a_2047_;
goto v___jp_2033_;
}
else
{
lean_object* v_a_2048_; 
v_a_2048_ = lean_ctor_get(v___y_2046_, 0);
lean_inc(v_a_2048_);
lean_dec_ref_known(v___y_2046_, 1);
v___y_2039_ = v___y_2045_;
v___y_2040_ = v___y_2044_;
v_a_2041_ = v_a_2048_;
goto v___jp_2038_;
}
}
v___jp_2049_:
{
if (v___y_2054_ == 0)
{
lean_object* v___x_2055_; 
lean_dec_ref(v___y_2051_);
lean_inc(v_a_1930_);
lean_inc_ref(v_a_1929_);
lean_inc(v_a_1928_);
lean_inc_ref(v_a_1927_);
v___x_2055_ = lean_apply_6(v_allowFailure_1925_, v_fst_1998_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, lean_box(0));
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; uint8_t v___x_2057_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2056_);
lean_dec_ref_known(v___x_2055_, 1);
v___x_2057_ = lean_unbox(v_a_2056_);
lean_dec(v_a_2056_);
if (v___x_2057_ == 0)
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
lean_dec(v___y_2050_);
v___x_2058_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1);
v___x_2059_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2058_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_);
v___y_2044_ = v___y_2053_;
v___y_2045_ = v___y_2052_;
v___y_2046_ = v___x_2059_;
goto v___jp_2043_;
}
else
{
v___y_2034_ = v___y_2052_;
v___y_2035_ = v___y_2053_;
v_a_2036_ = v___y_2050_;
goto v___jp_2033_;
}
}
else
{
lean_object* v_a_2060_; 
lean_dec(v___y_2050_);
v_a_2060_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2060_);
lean_dec_ref_known(v___x_2055_, 1);
v___y_2039_ = v___y_2052_;
v___y_2040_ = v___y_2053_;
v_a_2041_ = v_a_2060_;
goto v___jp_2038_;
}
}
else
{
lean_dec(v___y_2050_);
lean_dec(v_fst_1998_);
lean_dec_ref(v_allowFailure_1925_);
v___y_2039_ = v___y_2052_;
v___y_2040_ = v___y_2053_;
v_a_2041_ = v___y_2051_;
goto v___jp_2038_;
}
}
v___jp_2061_:
{
lean_object* v___x_2065_; double v___x_2066_; double v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2071_; 
v___x_2065_ = lean_io_get_num_heartbeats();
v___x_2066_ = lean_float_of_nat(v___y_2062_);
v___x_2067_ = lean_float_of_nat(v___x_2065_);
v___x_2068_ = lean_box_float(v___x_2066_);
v___x_2069_ = lean_box_float(v___x_2067_);
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 1, v___x_2069_);
lean_ctor_set(v___x_1935_, 0, v___x_2068_);
v___x_2071_ = v___x_1935_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2068_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v___x_2069_);
v___x_2071_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2072_, 0, v_a_2064_);
lean_ctor_set(v___x_2072_, 1, v___x_2071_);
v___x_2073_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v___x_2010_, v_hasTrace_1939_, v___x_2011_, v_options_1938_, v___x_2013_, v___y_2063_, v___f_2009_, v___x_2072_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_);
return v___x_2073_;
}
}
v___jp_2075_:
{
lean_object* v___x_2079_; 
v___x_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2079_, 0, v_a_2078_);
v___y_2062_ = v___y_2076_;
v___y_2063_ = v___y_2077_;
v_a_2064_ = v___x_2079_;
goto v___jp_2061_;
}
v___jp_2080_:
{
lean_object* v___x_2084_; 
v___x_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2084_, 0, v_a_2083_);
v___y_2062_ = v___y_2081_;
v___y_2063_ = v___y_2082_;
v_a_2064_ = v___x_2084_;
goto v___jp_2061_;
}
v___jp_2085_:
{
if (lean_obj_tag(v___y_2088_) == 0)
{
lean_object* v_a_2089_; 
v_a_2089_ = lean_ctor_get(v___y_2088_, 0);
lean_inc(v_a_2089_);
lean_dec_ref_known(v___y_2088_, 1);
v___y_2076_ = v___y_2086_;
v___y_2077_ = v___y_2087_;
v_a_2078_ = v_a_2089_;
goto v___jp_2075_;
}
else
{
lean_object* v_a_2090_; 
v_a_2090_ = lean_ctor_get(v___y_2088_, 0);
lean_inc(v_a_2090_);
lean_dec_ref_known(v___y_2088_, 1);
v___y_2081_ = v___y_2086_;
v___y_2082_ = v___y_2087_;
v_a_2083_ = v_a_2090_;
goto v___jp_2080_;
}
}
v___jp_2091_:
{
if (v___y_2096_ == 0)
{
lean_object* v___x_2097_; 
lean_dec_ref(v___y_2093_);
lean_inc(v_a_1930_);
lean_inc_ref(v_a_1929_);
lean_inc(v_a_1928_);
lean_inc_ref(v_a_1927_);
v___x_2097_ = lean_apply_6(v_allowFailure_1925_, v_fst_1998_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, lean_box(0));
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_a_2098_; uint8_t v___x_2099_; 
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_a_2098_);
lean_dec_ref_known(v___x_2097_, 1);
v___x_2099_ = lean_unbox(v_a_2098_);
lean_dec(v_a_2098_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
lean_dec(v___y_2095_);
v___x_2100_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1);
v___x_2101_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2100_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_);
v___y_2086_ = v___y_2092_;
v___y_2087_ = v___y_2094_;
v___y_2088_ = v___x_2101_;
goto v___jp_2085_;
}
else
{
v___y_2076_ = v___y_2092_;
v___y_2077_ = v___y_2094_;
v_a_2078_ = v___y_2095_;
goto v___jp_2075_;
}
}
else
{
lean_object* v_a_2102_; 
lean_dec(v___y_2095_);
v_a_2102_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_a_2102_);
lean_dec_ref_known(v___x_2097_, 1);
v___y_2081_ = v___y_2092_;
v___y_2082_ = v___y_2094_;
v_a_2083_ = v_a_2102_;
goto v___jp_2080_;
}
}
else
{
lean_dec(v___y_2095_);
lean_dec(v_fst_1998_);
lean_dec_ref(v_allowFailure_1925_);
v___y_2081_ = v___y_2092_;
v___y_2082_ = v___y_2094_;
v_a_2083_ = v___y_2093_;
goto v___jp_2080_;
}
}
v___jp_2103_:
{
lean_object* v___x_2104_; lean_object* v_a_2105_; lean_object* v___x_2106_; uint8_t v___x_2107_; 
v___x_2104_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v_a_1930_);
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2105_);
lean_dec_ref(v___x_2104_);
v___x_2106_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2107_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_1938_, v___x_2106_);
if (v___x_2107_ == 0)
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v_cache_2110_; lean_object* v_zetaDeltaFVarIds_2111_; lean_object* v_postponed_2112_; lean_object* v_diag_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2133_; 
lean_del_object(v___x_1935_);
v___x_2108_ = lean_io_mono_nanos_now();
v___x_2109_ = lean_st_ref_take(v_a_1928_);
v_cache_2110_ = lean_ctor_get(v___x_2109_, 1);
v_zetaDeltaFVarIds_2111_ = lean_ctor_get(v___x_2109_, 2);
v_postponed_2112_ = lean_ctor_get(v___x_2109_, 3);
v_diag_2113_ = lean_ctor_get(v___x_2109_, 4);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2133_ == 0)
{
lean_object* v_unused_2134_; 
v_unused_2134_ = lean_ctor_get(v___x_2109_, 0);
lean_dec(v_unused_2134_);
v___x_2115_ = v___x_2109_;
v_isShared_2116_ = v_isSharedCheck_2133_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_diag_2113_);
lean_inc(v_postponed_2112_);
lean_inc(v_zetaDeltaFVarIds_2111_);
lean_inc(v_cache_2110_);
lean_dec(v___x_2109_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2133_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 0, v_snd_1999_);
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_snd_1999_);
lean_ctor_set(v_reuseFailAlloc_2132_, 1, v_cache_2110_);
lean_ctor_set(v_reuseFailAlloc_2132_, 2, v_zetaDeltaFVarIds_2111_);
lean_ctor_set(v_reuseFailAlloc_2132_, 3, v_postponed_2112_);
lean_ctor_set(v_reuseFailAlloc_2132_, 4, v_diag_2113_);
v___x_2118_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
lean_object* v___x_2119_; uint8_t v___x_2120_; lean_object* v___x_2121_; 
v___x_2119_ = lean_st_ref_put(v_a_1928_, v___x_2118_);
v___x_2120_ = lean_unbox(v_snd_2004_);
lean_dec(v_snd_2004_);
v___x_2121_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_2003_, v___x_2120_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2122_);
lean_dec_ref_known(v___x_2121_, 1);
v___x_2123_ = lean_box(0);
lean_inc(v_fst_1998_);
v___x_2124_ = l_Lean_MVarId_apply(v_fst_1998_, v_a_2122_, v_cfg_1923_, v___x_2123_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v___x_2126_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc_n(v_a_2125_, 2);
lean_dec_ref_known(v___x_2124_, 1);
lean_inc(v_a_1930_);
lean_inc_ref(v_a_1929_);
lean_inc(v_a_1928_);
lean_inc_ref(v_a_1927_);
v___x_2126_ = lean_apply_6(v_act_1924_, v_a_2125_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, lean_box(0));
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; 
lean_dec(v_a_2125_);
lean_dec(v_fst_1998_);
lean_dec_ref(v_allowFailure_1925_);
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref_known(v___x_2126_, 1);
v___y_2034_ = v___x_2108_;
v___y_2035_ = v_a_2105_;
v_a_2036_ = v_a_2127_;
goto v___jp_2033_;
}
else
{
lean_object* v_a_2128_; uint8_t v___x_2129_; 
v_a_2128_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2128_);
lean_dec_ref_known(v___x_2126_, 1);
v___x_2129_ = l_Lean_Exception_isInterrupt(v_a_2128_);
if (v___x_2129_ == 0)
{
uint8_t v___x_2130_; 
lean_inc(v_a_2128_);
v___x_2130_ = l_Lean_Exception_isRuntime(v_a_2128_);
v___y_2050_ = v_a_2125_;
v___y_2051_ = v_a_2128_;
v___y_2052_ = v___x_2108_;
v___y_2053_ = v_a_2105_;
v___y_2054_ = v___x_2130_;
goto v___jp_2049_;
}
else
{
v___y_2050_ = v_a_2125_;
v___y_2051_ = v_a_2128_;
v___y_2052_ = v___x_2108_;
v___y_2053_ = v_a_2105_;
v___y_2054_ = v___x_2129_;
goto v___jp_2049_;
}
}
}
else
{
lean_dec(v_fst_1998_);
lean_dec_ref(v_allowFailure_1925_);
lean_dec_ref(v_act_1924_);
v___y_2044_ = v_a_2105_;
v___y_2045_ = v___x_2108_;
v___y_2046_ = v___x_2124_;
goto v___jp_2043_;
}
}
else
{
lean_object* v_a_2131_; 
lean_dec(v_fst_1998_);
lean_dec_ref(v_allowFailure_1925_);
lean_dec_ref(v_act_1924_);
lean_dec_ref(v_cfg_1923_);
v_a_2131_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2121_, 1);
v___y_2039_ = v___x_2108_;
v___y_2040_ = v_a_2105_;
v_a_2041_ = v_a_2131_;
goto v___jp_2038_;
}
}
}
}
else
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v_cache_2137_; lean_object* v_zetaDeltaFVarIds_2138_; lean_object* v_postponed_2139_; lean_object* v_diag_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2160_; 
lean_del_object(v___x_2006_);
lean_del_object(v___x_2001_);
v___x_2135_ = lean_io_get_num_heartbeats();
v___x_2136_ = lean_st_ref_take(v_a_1928_);
v_cache_2137_ = lean_ctor_get(v___x_2136_, 1);
v_zetaDeltaFVarIds_2138_ = lean_ctor_get(v___x_2136_, 2);
v_postponed_2139_ = lean_ctor_get(v___x_2136_, 3);
v_diag_2140_ = lean_ctor_get(v___x_2136_, 4);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2160_ == 0)
{
lean_object* v_unused_2161_; 
v_unused_2161_ = lean_ctor_get(v___x_2136_, 0);
lean_dec(v_unused_2161_);
v___x_2142_ = v___x_2136_;
v_isShared_2143_ = v_isSharedCheck_2160_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_diag_2140_);
lean_inc(v_postponed_2139_);
lean_inc(v_zetaDeltaFVarIds_2138_);
lean_inc(v_cache_2137_);
lean_dec(v___x_2136_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2160_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 0, v_snd_1999_);
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_snd_1999_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v_cache_2137_);
lean_ctor_set(v_reuseFailAlloc_2159_, 2, v_zetaDeltaFVarIds_2138_);
lean_ctor_set(v_reuseFailAlloc_2159_, 3, v_postponed_2139_);
lean_ctor_set(v_reuseFailAlloc_2159_, 4, v_diag_2140_);
v___x_2145_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
lean_object* v___x_2146_; uint8_t v___x_2147_; lean_object* v___x_2148_; 
v___x_2146_ = lean_st_ref_put(v_a_1928_, v___x_2145_);
v___x_2147_ = lean_unbox(v_snd_2004_);
lean_dec(v_snd_2004_);
v___x_2148_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_2003_, v___x_2147_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_a_2149_);
lean_dec_ref_known(v___x_2148_, 1);
v___x_2150_ = lean_box(0);
lean_inc(v_fst_1998_);
v___x_2151_ = l_Lean_MVarId_apply(v_fst_1998_, v_a_2149_, v_cfg_1923_, v___x_2150_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v_a_2152_; lean_object* v___x_2153_; 
v_a_2152_ = lean_ctor_get(v___x_2151_, 0);
lean_inc_n(v_a_2152_, 2);
lean_dec_ref_known(v___x_2151_, 1);
lean_inc(v_a_1930_);
lean_inc_ref(v_a_1929_);
lean_inc(v_a_1928_);
lean_inc_ref(v_a_1927_);
v___x_2153_ = lean_apply_6(v_act_1924_, v_a_2152_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, lean_box(0));
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v_a_2154_; 
lean_dec(v_a_2152_);
lean_dec(v_fst_1998_);
lean_dec_ref(v_allowFailure_1925_);
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_a_2154_);
lean_dec_ref_known(v___x_2153_, 1);
v___y_2076_ = v___x_2135_;
v___y_2077_ = v_a_2105_;
v_a_2078_ = v_a_2154_;
goto v___jp_2075_;
}
else
{
lean_object* v_a_2155_; uint8_t v___x_2156_; 
v_a_2155_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_a_2155_);
lean_dec_ref_known(v___x_2153_, 1);
v___x_2156_ = l_Lean_Exception_isInterrupt(v_a_2155_);
if (v___x_2156_ == 0)
{
uint8_t v___x_2157_; 
lean_inc(v_a_2155_);
v___x_2157_ = l_Lean_Exception_isRuntime(v_a_2155_);
v___y_2092_ = v___x_2135_;
v___y_2093_ = v_a_2155_;
v___y_2094_ = v_a_2105_;
v___y_2095_ = v_a_2152_;
v___y_2096_ = v___x_2157_;
goto v___jp_2091_;
}
else
{
v___y_2092_ = v___x_2135_;
v___y_2093_ = v_a_2155_;
v___y_2094_ = v_a_2105_;
v___y_2095_ = v_a_2152_;
v___y_2096_ = v___x_2156_;
goto v___jp_2091_;
}
}
}
else
{
lean_dec(v_fst_1998_);
lean_dec_ref(v_allowFailure_1925_);
lean_dec_ref(v_act_1924_);
v___y_2086_ = v___x_2135_;
v___y_2087_ = v_a_2105_;
v___y_2088_ = v___x_2151_;
goto v___jp_2085_;
}
}
else
{
lean_object* v_a_2158_; 
lean_dec(v_fst_1998_);
lean_dec_ref(v_allowFailure_1925_);
lean_dec_ref(v_act_1924_);
lean_dec_ref(v_cfg_1923_);
v_a_2158_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_a_2158_);
lean_dec_ref_known(v___x_2148_, 1);
v___y_2081_ = v___x_2135_;
v___y_2082_ = v_a_2105_;
v_a_2083_ = v_a_2158_;
goto v___jp_2080_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___boxed(lean_object* v_cfg_2221_, lean_object* v_act_2222_, lean_object* v_allowFailure_2223_, lean_object* v_cand_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(v_cfg_2221_, v_act_2222_, v_allowFailure_2223_, v_cand_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
lean_dec(v_a_2228_);
lean_dec_ref(v_a_2227_);
lean_dec(v_a_2226_);
lean_dec_ref(v_a_2225_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3(lean_object* v_00_u03b1_2231_, lean_object* v_x_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_x_2232_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2239_, lean_object* v_x_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3(v_00_u03b1_2239_, v_x_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(lean_object* v_act_2249_, lean_object* v_a_2250_, uint8_t v_collectAll_2251_, lean_object* v_as_2252_, size_t v_sz_2253_, size_t v_i_2254_, lean_object* v_b_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v_a_2262_; uint8_t v___x_2266_; 
v___x_2266_ = lean_usize_dec_lt(v_i_2254_, v_sz_2253_);
if (v___x_2266_ == 0)
{
lean_object* v___x_2267_; 
lean_dec_ref(v_act_2249_);
v___x_2267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2267_, 0, v_b_2255_);
return v___x_2267_;
}
else
{
lean_object* v_snd_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2341_; 
v_snd_2268_ = lean_ctor_get(v_b_2255_, 1);
v_isSharedCheck_2341_ = !lean_is_exclusive(v_b_2255_);
if (v_isSharedCheck_2341_ == 0)
{
lean_object* v_unused_2342_; 
v_unused_2342_ = lean_ctor_get(v_b_2255_, 0);
lean_dec(v_unused_2342_);
v___x_2270_ = v_b_2255_;
v_isShared_2271_ = v_isSharedCheck_2341_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_snd_2268_);
lean_dec(v_b_2255_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2341_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2272_; lean_object* v_a_2273_; lean_object* v___x_2274_; 
v___x_2272_ = lean_box(0);
v_a_2273_ = lean_array_uget_borrowed(v_as_2252_, v_i_2254_);
lean_inc_ref(v_act_2249_);
lean_inc(v___y_2259_);
lean_inc_ref(v___y_2258_);
lean_inc(v___y_2257_);
lean_inc_ref(v___y_2256_);
lean_inc(v_a_2273_);
v___x_2274_ = lean_apply_6(v_act_2249_, v_a_2273_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, lean_box(0));
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2304_; 
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2277_ = v___x_2274_;
v_isShared_2278_ = v_isSharedCheck_2304_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2274_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2304_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
uint8_t v___y_2297_; uint8_t v___x_2303_; 
v___x_2303_ = l_List_isEmpty___redArg(v_a_2275_);
if (v___x_2303_ == 0)
{
v___y_2297_ = v___x_2303_;
goto v___jp_2296_;
}
else
{
if (v_collectAll_2251_ == 0)
{
v___y_2297_ = v___x_2303_;
goto v___jp_2296_;
}
else
{
lean_del_object(v___x_2277_);
goto v___jp_2279_;
}
}
v___jp_2279_:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2280_ = lean_st_ref_get(v___y_2257_);
v___x_2281_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2250_, v___y_2257_, v___y_2259_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_mctx_2282_; lean_object* v___x_2284_; 
lean_dec_ref_known(v___x_2281_, 1);
v_mctx_2282_ = lean_ctor_get(v___x_2280_, 0);
lean_inc_ref(v_mctx_2282_);
lean_dec(v___x_2280_);
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 1, v_mctx_2282_);
lean_ctor_set(v___x_2270_, 0, v_a_2275_);
v___x_2284_ = v___x_2270_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2275_);
lean_ctor_set(v_reuseFailAlloc_2287_, 1, v_mctx_2282_);
v___x_2284_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2285_ = lean_array_push(v_snd_2268_, v___x_2284_);
v___x_2286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2272_);
lean_ctor_set(v___x_2286_, 1, v___x_2285_);
v_a_2262_ = v___x_2286_;
goto v___jp_2261_;
}
}
else
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2295_; 
lean_dec(v___x_2280_);
lean_dec(v_a_2275_);
lean_del_object(v___x_2270_);
lean_dec(v_snd_2268_);
lean_dec_ref(v_act_2249_);
v_a_2288_ = lean_ctor_get(v___x_2281_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2290_ = v___x_2281_;
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2281_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2293_; 
if (v_isShared_2291_ == 0)
{
v___x_2293_ = v___x_2290_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_a_2288_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
}
v___jp_2296_:
{
if (v___y_2297_ == 0)
{
lean_del_object(v___x_2277_);
goto v___jp_2279_;
}
else
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2301_; 
lean_dec(v_a_2275_);
lean_del_object(v___x_2270_);
lean_dec_ref(v_act_2249_);
v___x_2298_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0___closed__0));
v___x_2299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2298_);
lean_ctor_set(v___x_2299_, 1, v_snd_2268_);
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 0, v___x_2299_);
v___x_2301_ = v___x_2277_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v___x_2299_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
}
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2340_; 
v_a_2305_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2307_ = v___x_2274_;
v_isShared_2308_ = v_isSharedCheck_2340_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2274_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2340_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
uint8_t v___y_2310_; uint8_t v___x_2338_; 
v___x_2338_ = l_Lean_Exception_isInterrupt(v_a_2305_);
if (v___x_2338_ == 0)
{
uint8_t v___x_2339_; 
lean_inc(v_a_2305_);
v___x_2339_ = l_Lean_Exception_isRuntime(v_a_2305_);
v___y_2310_ = v___x_2339_;
goto v___jp_2309_;
}
else
{
v___y_2310_ = v___x_2338_;
goto v___jp_2309_;
}
v___jp_2309_:
{
if (v___y_2310_ == 0)
{
lean_object* v___x_2311_; 
lean_del_object(v___x_2307_);
v___x_2311_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2250_, v___y_2257_, v___y_2259_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2325_; 
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2325_ == 0)
{
lean_object* v_unused_2326_; 
v_unused_2326_ = lean_ctor_get(v___x_2311_, 0);
lean_dec(v_unused_2326_);
v___x_2313_ = v___x_2311_;
v_isShared_2314_ = v_isSharedCheck_2325_;
goto v_resetjp_2312_;
}
else
{
lean_dec(v___x_2311_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2325_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
uint8_t v___x_2315_; 
v___x_2315_ = l_Lean_Meta_LibrarySearch_isAbortSpeculation(v_a_2305_);
lean_dec(v_a_2305_);
if (v___x_2315_ == 0)
{
lean_object* v___x_2317_; 
lean_del_object(v___x_2313_);
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 0, v___x_2272_);
v___x_2317_ = v___x_2270_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2272_);
lean_ctor_set(v_reuseFailAlloc_2318_, 1, v_snd_2268_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
v_a_2262_ = v___x_2317_;
goto v___jp_2261_;
}
}
else
{
lean_object* v___x_2320_; 
lean_dec_ref(v_act_2249_);
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 0, v___x_2272_);
v___x_2320_ = v___x_2270_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v___x_2272_);
lean_ctor_set(v_reuseFailAlloc_2324_, 1, v_snd_2268_);
v___x_2320_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
lean_object* v___x_2322_; 
if (v_isShared_2314_ == 0)
{
lean_ctor_set(v___x_2313_, 0, v___x_2320_);
v___x_2322_ = v___x_2313_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v___x_2320_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
}
}
}
else
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2334_; 
lean_dec(v_a_2305_);
lean_del_object(v___x_2270_);
lean_dec(v_snd_2268_);
lean_dec_ref(v_act_2249_);
v_a_2327_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2329_ = v___x_2311_;
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___x_2311_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2332_; 
if (v_isShared_2330_ == 0)
{
v___x_2332_ = v___x_2329_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2327_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
else
{
lean_object* v___x_2336_; 
lean_del_object(v___x_2270_);
lean_dec(v_snd_2268_);
lean_dec_ref(v_act_2249_);
if (v_isShared_2308_ == 0)
{
v___x_2336_ = v___x_2307_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2305_);
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
}
}
v___jp_2261_:
{
size_t v___x_2263_; size_t v___x_2264_; 
v___x_2263_ = ((size_t)1ULL);
v___x_2264_ = lean_usize_add(v_i_2254_, v___x_2263_);
v_i_2254_ = v___x_2264_;
v_b_2255_ = v_a_2262_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0___boxed(lean_object* v_act_2343_, lean_object* v_a_2344_, lean_object* v_collectAll_2345_, lean_object* v_as_2346_, lean_object* v_sz_2347_, lean_object* v_i_2348_, lean_object* v_b_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
uint8_t v_collectAll_boxed_2355_; size_t v_sz_boxed_2356_; size_t v_i_boxed_2357_; lean_object* v_res_2358_; 
v_collectAll_boxed_2355_ = lean_unbox(v_collectAll_2345_);
v_sz_boxed_2356_ = lean_unbox_usize(v_sz_2347_);
lean_dec(v_sz_2347_);
v_i_boxed_2357_ = lean_unbox_usize(v_i_2348_);
lean_dec(v_i_2348_);
v_res_2358_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(v_act_2343_, v_a_2344_, v_collectAll_boxed_2355_, v_as_2346_, v_sz_boxed_2356_, v_i_boxed_2357_, v_b_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec_ref(v_as_2346_);
lean_dec_ref(v_a_2344_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryOnEach(lean_object* v_act_2364_, lean_object* v_candidates_2365_, uint8_t v_collectAll_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_){
_start:
{
lean_object* v___x_2372_; 
v___x_2372_ = l_Lean_Meta_saveState___redArg(v_a_2368_, v_a_2370_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v_a_2373_; lean_object* v___x_2374_; size_t v_sz_2375_; size_t v___x_2376_; lean_object* v___x_2377_; 
v_a_2373_ = lean_ctor_get(v___x_2372_, 0);
lean_inc(v_a_2373_);
lean_dec_ref_known(v___x_2372_, 1);
v___x_2374_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryOnEach___closed__1));
v_sz_2375_ = lean_array_size(v_candidates_2365_);
v___x_2376_ = ((size_t)0ULL);
v___x_2377_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(v_act_2364_, v_a_2373_, v_collectAll_2366_, v_candidates_2365_, v_sz_2375_, v___x_2376_, v___x_2374_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v_a_2373_);
if (lean_obj_tag(v___x_2377_) == 0)
{
lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2392_; 
v_a_2378_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2380_ = v___x_2377_;
v_isShared_2381_ = v_isSharedCheck_2392_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v___x_2377_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2392_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v_fst_2382_; 
v_fst_2382_ = lean_ctor_get(v_a_2378_, 0);
if (lean_obj_tag(v_fst_2382_) == 0)
{
lean_object* v_snd_2383_; lean_object* v___x_2384_; lean_object* v___x_2386_; 
v_snd_2383_ = lean_ctor_get(v_a_2378_, 1);
lean_inc(v_snd_2383_);
lean_dec(v_a_2378_);
v___x_2384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2384_, 0, v_snd_2383_);
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 0, v___x_2384_);
v___x_2386_ = v___x_2380_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v___x_2384_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
else
{
lean_object* v_val_2388_; lean_object* v___x_2390_; 
lean_inc_ref(v_fst_2382_);
lean_dec(v_a_2378_);
v_val_2388_ = lean_ctor_get(v_fst_2382_, 0);
lean_inc(v_val_2388_);
lean_dec_ref_known(v_fst_2382_, 1);
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 0, v_val_2388_);
v___x_2390_ = v___x_2380_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_val_2388_);
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
else
{
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2400_; 
v_a_2393_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2395_ = v___x_2377_;
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2377_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2398_; 
if (v_isShared_2396_ == 0)
{
v___x_2398_ = v___x_2395_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2393_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
}
else
{
lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2408_; 
lean_dec_ref(v_act_2364_);
v_a_2401_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2403_ = v___x_2372_;
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v___x_2372_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2406_; 
if (v_isShared_2404_ == 0)
{
v___x_2406_ = v___x_2403_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_a_2401_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryOnEach___boxed(lean_object* v_act_2409_, lean_object* v_candidates_2410_, lean_object* v_collectAll_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_){
_start:
{
uint8_t v_collectAll_boxed_2417_; lean_object* v_res_2418_; 
v_collectAll_boxed_2417_ = lean_unbox(v_collectAll_2411_);
v_res_2418_ = l_Lean_Meta_LibrarySearch_tryOnEach(v_act_2409_, v_candidates_2410_, v_collectAll_boxed_2417_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_);
lean_dec(v_a_2415_);
lean_dec_ref(v_a_2414_);
lean_dec(v_a_2413_);
lean_dec_ref(v_a_2412_);
lean_dec_ref(v_candidates_2410_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg(){
_start:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2420_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0, &l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0_once, _init_l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0);
v___x_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2420_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg___boxed(lean_object* v___y_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg();
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0(lean_object* v_00_u03b1_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v___x_2430_; 
v___x_2430_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg();
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___boxed(lean_object* v_00_u03b1_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0(v_00_u03b1_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(lean_object* v_category_2438_, lean_object* v_opts_2439_, lean_object* v_act_2440_, lean_object* v_decl_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
lean_inc(v___y_2445_);
lean_inc_ref(v___y_2444_);
lean_inc(v___y_2443_);
lean_inc_ref(v___y_2442_);
v___x_2447_ = lean_apply_4(v_act_2440_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
v___x_2448_ = l_Lean_profileitIOUnsafe___redArg(v_category_2438_, v_opts_2439_, v___x_2447_, v_decl_2441_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg___boxed(lean_object* v_category_2449_, lean_object* v_opts_2450_, lean_object* v_act_2451_, lean_object* v_decl_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
lean_object* v_res_2458_; 
v_res_2458_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v_category_2449_, v_opts_2450_, v_act_2451_, v_decl_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
lean_dec_ref(v_opts_2450_);
lean_dec_ref(v_category_2449_);
return v_res_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3(lean_object* v_00_u03b1_2459_, lean_object* v_category_2460_, lean_object* v_opts_2461_, lean_object* v_act_2462_, lean_object* v_decl_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_){
_start:
{
lean_object* v___x_2469_; 
v___x_2469_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v_category_2460_, v_opts_2461_, v_act_2462_, v_decl_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___boxed(lean_object* v_00_u03b1_2470_, lean_object* v_category_2471_, lean_object* v_opts_2472_, lean_object* v_act_2473_, lean_object* v_decl_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3(v_00_u03b1_2470_, v_category_2471_, v_opts_2472_, v_act_2473_, v_decl_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
lean_dec_ref(v_opts_2472_);
lean_dec_ref(v_category_2471_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0(lean_object* v_a_2481_, lean_object* v___x_2482_, lean_object* v_tactic_2483_, lean_object* v_allowFailure_2484_, lean_object* v_cand_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
lean_object* v___x_2491_; 
lean_inc(v___y_2489_);
lean_inc_ref(v___y_2488_);
lean_inc(v___y_2487_);
lean_inc_ref(v___y_2486_);
v___x_2491_ = lean_apply_5(v_a_2481_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, lean_box(0));
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v_a_2492_; uint8_t v___x_2493_; 
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
lean_inc(v_a_2492_);
lean_dec_ref_known(v___x_2491_, 1);
v___x_2493_ = lean_unbox(v_a_2492_);
lean_dec(v_a_2492_);
if (v___x_2493_ == 0)
{
lean_object* v___x_2494_; 
v___x_2494_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(v___x_2482_, v_tactic_2483_, v_allowFailure_2484_, v_cand_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
return v___x_2494_;
}
else
{
lean_object* v___x_2495_; lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
lean_dec_ref(v_cand_2485_);
lean_dec_ref(v_allowFailure_2484_);
lean_dec_ref(v_tactic_2483_);
lean_dec_ref(v___x_2482_);
v___x_2495_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg();
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2498_ = v___x_2495_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2495_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2501_; 
if (v_isShared_2499_ == 0)
{
v___x_2501_ = v___x_2498_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2496_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
}
else
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2511_; 
lean_dec_ref(v_cand_2485_);
lean_dec_ref(v_allowFailure_2484_);
lean_dec_ref(v_tactic_2483_);
lean_dec_ref(v___x_2482_);
v_a_2504_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2506_ = v___x_2491_;
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2491_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2509_; 
if (v_isShared_2507_ == 0)
{
v___x_2509_ = v___x_2506_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_a_2504_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed(lean_object* v_a_2512_, lean_object* v___x_2513_, lean_object* v_tactic_2514_, lean_object* v_allowFailure_2515_, lean_object* v_cand_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0(v_a_2512_, v___x_2513_, v_tactic_2514_, v_allowFailure_2515_, v_cand_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
return v_res_2522_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(lean_object* v_as_2523_, size_t v_i_2524_, size_t v_stop_2525_){
_start:
{
uint8_t v___x_2526_; 
v___x_2526_ = lean_usize_dec_eq(v_i_2524_, v_stop_2525_);
if (v___x_2526_ == 0)
{
lean_object* v___x_2527_; lean_object* v_fst_2528_; uint8_t v___x_2529_; 
v___x_2527_ = lean_array_uget_borrowed(v_as_2523_, v_i_2524_);
v_fst_2528_ = lean_ctor_get(v___x_2527_, 0);
v___x_2529_ = l_List_isEmpty___redArg(v_fst_2528_);
if (v___x_2529_ == 0)
{
size_t v___x_2530_; size_t v___x_2531_; 
v___x_2530_ = ((size_t)1ULL);
v___x_2531_ = lean_usize_add(v_i_2524_, v___x_2530_);
v_i_2524_ = v___x_2531_;
goto _start;
}
else
{
return v___x_2529_;
}
}
else
{
uint8_t v___x_2533_; 
v___x_2533_ = 0;
return v___x_2533_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2___boxed(lean_object* v_as_2534_, lean_object* v_i_2535_, lean_object* v_stop_2536_){
_start:
{
size_t v_i_boxed_2537_; size_t v_stop_boxed_2538_; uint8_t v_res_2539_; lean_object* v_r_2540_; 
v_i_boxed_2537_ = lean_unbox_usize(v_i_2535_);
lean_dec(v_i_2535_);
v_stop_boxed_2538_ = lean_unbox_usize(v_stop_2536_);
lean_dec(v_stop_2536_);
v_res_2539_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_as_2534_, v_i_boxed_2537_, v_stop_boxed_2538_);
lean_dec_ref(v_as_2534_);
v_r_2540_ = lean_box(v_res_2539_);
return v_r_2540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(lean_object* v_goal_2541_, lean_object* v___x_2542_, size_t v_sz_2543_, size_t v_i_2544_, lean_object* v_bs_2545_){
_start:
{
uint8_t v___x_2546_; 
v___x_2546_ = lean_usize_dec_lt(v_i_2544_, v_sz_2543_);
if (v___x_2546_ == 0)
{
lean_dec_ref(v___x_2542_);
lean_dec(v_goal_2541_);
return v_bs_2545_;
}
else
{
lean_object* v_v_2547_; lean_object* v___x_2548_; lean_object* v_bs_x27_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; size_t v___x_2552_; size_t v___x_2553_; lean_object* v___x_2554_; 
v_v_2547_ = lean_array_uget(v_bs_2545_, v_i_2544_);
v___x_2548_ = lean_unsigned_to_nat(0u);
v_bs_x27_2549_ = lean_array_uset(v_bs_2545_, v_i_2544_, v___x_2548_);
lean_inc_ref(v___x_2542_);
lean_inc(v_goal_2541_);
v___x_2550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2550_, 0, v_goal_2541_);
lean_ctor_set(v___x_2550_, 1, v___x_2542_);
v___x_2551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2550_);
lean_ctor_set(v___x_2551_, 1, v_v_2547_);
v___x_2552_ = ((size_t)1ULL);
v___x_2553_ = lean_usize_add(v_i_2544_, v___x_2552_);
v___x_2554_ = lean_array_uset(v_bs_x27_2549_, v_i_2544_, v___x_2551_);
v_i_2544_ = v___x_2553_;
v_bs_2545_ = v___x_2554_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1___boxed(lean_object* v_goal_2556_, lean_object* v___x_2557_, lean_object* v_sz_2558_, lean_object* v_i_2559_, lean_object* v_bs_2560_){
_start:
{
size_t v_sz_boxed_2561_; size_t v_i_boxed_2562_; lean_object* v_res_2563_; 
v_sz_boxed_2561_ = lean_unbox_usize(v_sz_2558_);
lean_dec(v_sz_2558_);
v_i_boxed_2562_ = lean_unbox_usize(v_i_2559_);
lean_dec(v_i_2559_);
v_res_2563_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2556_, v___x_2557_, v_sz_boxed_2561_, v_i_boxed_2562_, v_bs_2560_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1(lean_object* v_leavePercentHeartbeats_2565_, lean_object* v_goal_2566_, lean_object* v___x_2567_, lean_object* v_tactic_2568_, lean_object* v_allowFailure_2569_, uint8_t v_collectAll_2570_, uint8_t v_includeStar_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
lean_object* v___x_2580_; 
v___x_2580_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercentHeartbeats_2565_, v___y_2574_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
lean_inc(v_a_2581_);
lean_dec_ref_known(v___x_2580_, 1);
v___x_2582_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___closed__0));
lean_inc(v_goal_2566_);
v___x_2583_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v___x_2582_, v_goal_2566_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v_a_2584_; lean_object* v___f_2585_; lean_object* v___x_2586_; 
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
lean_inc(v_a_2584_);
lean_dec_ref_known(v___x_2583_, 1);
v___f_2585_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2585_, 0, v_a_2581_);
lean_closure_set(v___f_2585_, 1, v___x_2567_);
lean_closure_set(v___f_2585_, 2, v_tactic_2568_);
lean_closure_set(v___f_2585_, 3, v_allowFailure_2569_);
lean_inc_ref(v___f_2585_);
v___x_2586_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2585_, v_a_2584_, v_collectAll_2570_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
lean_dec(v_a_2584_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_a_2587_);
if (lean_obj_tag(v_a_2587_) == 0)
{
lean_dec_ref_known(v___x_2586_, 1);
lean_dec_ref(v___f_2585_);
lean_dec(v_goal_2566_);
goto v___jp_2577_;
}
else
{
lean_object* v_val_2588_; lean_object* v___x_2637_; lean_object* v___x_2638_; uint8_t v___x_2639_; 
v_val_2588_ = lean_ctor_get(v_a_2587_, 0);
v___x_2637_ = lean_unsigned_to_nat(0u);
v___x_2638_ = lean_array_get_size(v_val_2588_);
v___x_2639_ = lean_nat_dec_lt(v___x_2637_, v___x_2638_);
if (v___x_2639_ == 0)
{
goto v___jp_2633_;
}
else
{
if (v___x_2639_ == 0)
{
goto v___jp_2633_;
}
else
{
size_t v___x_2640_; size_t v___x_2641_; uint8_t v___x_2642_; 
v___x_2640_ = ((size_t)0ULL);
v___x_2641_ = lean_usize_of_nat(v___x_2638_);
v___x_2642_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_val_2588_, v___x_2640_, v___x_2641_);
if (v___x_2642_ == 0)
{
goto v___jp_2633_;
}
else
{
lean_dec_ref_known(v_a_2587_, 1);
lean_dec_ref(v___f_2585_);
lean_dec(v_goal_2566_);
return v___x_2586_;
}
}
}
v___jp_2589_:
{
if (v_includeStar_2571_ == 0)
{
lean_dec_ref_known(v_a_2587_, 1);
lean_dec_ref(v___f_2585_);
lean_dec(v_goal_2566_);
return v___x_2586_;
}
else
{
lean_object* v___x_2590_; 
lean_dec_ref_known(v___x_2586_, 1);
v___x_2590_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2624_; 
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2593_ = v___x_2590_;
v_isShared_2594_ = v_isSharedCheck_2624_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2590_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2624_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; uint8_t v___x_2597_; 
v___x_2595_ = lean_array_get_size(v_a_2591_);
v___x_2596_ = lean_unsigned_to_nat(0u);
v___x_2597_ = lean_nat_dec_eq(v___x_2595_, v___x_2596_);
if (v___x_2597_ == 0)
{
lean_object* v___x_2598_; lean_object* v_mctx_2599_; size_t v_sz_2600_; size_t v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
lean_inc(v_val_2588_);
lean_del_object(v___x_2593_);
lean_dec_ref_known(v_a_2587_, 1);
v___x_2598_ = lean_st_ref_get(v___y_2573_);
v_mctx_2599_ = lean_ctor_get(v___x_2598_, 0);
lean_inc_ref(v_mctx_2599_);
lean_dec(v___x_2598_);
v_sz_2600_ = lean_array_size(v_a_2591_);
v___x_2601_ = ((size_t)0ULL);
v___x_2602_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2566_, v_mctx_2599_, v_sz_2600_, v___x_2601_, v_a_2591_);
v___x_2603_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2585_, v___x_2602_, v_collectAll_2570_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
lean_dec_ref(v___x_2602_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2620_; 
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2606_ = v___x_2603_;
v_isShared_2607_ = v_isSharedCheck_2620_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2603_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2620_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
if (lean_obj_tag(v_a_2604_) == 0)
{
lean_del_object(v___x_2606_);
lean_dec(v_val_2588_);
goto v___jp_2577_;
}
else
{
lean_object* v_val_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2619_; 
v_val_2608_ = lean_ctor_get(v_a_2604_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v_a_2604_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2610_ = v_a_2604_;
v_isShared_2611_ = v_isSharedCheck_2619_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_val_2608_);
lean_dec(v_a_2604_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2619_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2612_; lean_object* v___x_2614_; 
v___x_2612_ = l_Array_append___redArg(v_val_2588_, v_val_2608_);
lean_dec(v_val_2608_);
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 0, v___x_2612_);
v___x_2614_ = v___x_2610_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v___x_2612_);
v___x_2614_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
lean_object* v___x_2616_; 
if (v_isShared_2607_ == 0)
{
lean_ctor_set(v___x_2606_, 0, v___x_2614_);
v___x_2616_ = v___x_2606_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2614_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
}
}
else
{
lean_dec(v_val_2588_);
return v___x_2603_;
}
}
else
{
lean_object* v___x_2622_; 
lean_dec(v_a_2591_);
lean_dec_ref(v___f_2585_);
lean_dec(v_goal_2566_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 0, v_a_2587_);
v___x_2622_ = v___x_2593_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2587_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec_ref_known(v_a_2587_, 1);
lean_dec_ref(v___f_2585_);
lean_dec(v_goal_2566_);
v_a_2625_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2590_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2590_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
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
v___jp_2633_:
{
if (v_collectAll_2570_ == 0)
{
lean_object* v___x_2634_; lean_object* v___x_2635_; uint8_t v___x_2636_; 
v___x_2634_ = lean_array_get_size(v_val_2588_);
v___x_2635_ = lean_unsigned_to_nat(0u);
v___x_2636_ = lean_nat_dec_eq(v___x_2634_, v___x_2635_);
if (v___x_2636_ == 0)
{
lean_dec_ref_known(v_a_2587_, 1);
lean_dec_ref(v___f_2585_);
lean_dec(v_goal_2566_);
return v___x_2586_;
}
else
{
goto v___jp_2589_;
}
}
else
{
goto v___jp_2589_;
}
}
}
}
else
{
lean_dec_ref(v___f_2585_);
lean_dec(v_goal_2566_);
return v___x_2586_;
}
}
else
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2650_; 
lean_dec(v_a_2581_);
lean_dec_ref(v_allowFailure_2569_);
lean_dec_ref(v_tactic_2568_);
lean_dec_ref(v___x_2567_);
lean_dec(v_goal_2566_);
v_a_2643_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2645_ = v___x_2583_;
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2583_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2646_ == 0)
{
v___x_2648_ = v___x_2645_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
else
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2658_; 
lean_dec_ref(v_allowFailure_2569_);
lean_dec_ref(v_tactic_2568_);
lean_dec_ref(v___x_2567_);
lean_dec(v_goal_2566_);
v_a_2651_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2653_ = v___x_2580_;
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2580_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2656_; 
if (v_isShared_2654_ == 0)
{
v___x_2656_ = v___x_2653_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_a_2651_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
v___jp_2577_:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2578_ = lean_box(0);
v___x_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2578_);
return v___x_2579_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed(lean_object* v_leavePercentHeartbeats_2659_, lean_object* v_goal_2660_, lean_object* v___x_2661_, lean_object* v_tactic_2662_, lean_object* v_allowFailure_2663_, lean_object* v_collectAll_2664_, lean_object* v_includeStar_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_){
_start:
{
uint8_t v_collectAll_boxed_2671_; uint8_t v_includeStar_boxed_2672_; lean_object* v_res_2673_; 
v_collectAll_boxed_2671_ = lean_unbox(v_collectAll_2664_);
v_includeStar_boxed_2672_ = lean_unbox(v_includeStar_2665_);
v_res_2673_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1(v_leavePercentHeartbeats_2659_, v_goal_2660_, v___x_2661_, v_tactic_2662_, v_allowFailure_2663_, v_collectAll_boxed_2671_, v_includeStar_boxed_2672_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
lean_dec(v___y_2669_);
lean_dec_ref(v___y_2668_);
lean_dec(v___y_2667_);
lean_dec_ref(v___y_2666_);
lean_dec(v_leavePercentHeartbeats_2659_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2(lean_object* v_goal_2674_, lean_object* v_x_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
lean_object* v___x_2681_; 
v___x_2681_ = l_Lean_MVarId_getType(v_goal_2674_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_object* v_a_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2690_; 
v_a_2682_ = lean_ctor_get(v___x_2681_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2684_ = v___x_2681_;
v_isShared_2685_ = v_isSharedCheck_2690_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_a_2682_);
lean_dec(v___x_2681_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2690_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2686_; lean_object* v___x_2688_; 
v___x_2686_ = l_Lean_MessageData_ofExpr(v_a_2682_);
if (v_isShared_2685_ == 0)
{
lean_ctor_set(v___x_2684_, 0, v___x_2686_);
v___x_2688_ = v___x_2684_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v___x_2686_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
else
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
v_a_2691_ = lean_ctor_get(v___x_2681_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2693_ = v___x_2681_;
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2681_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2696_; 
if (v_isShared_2694_ == 0)
{
v___x_2696_ = v___x_2693_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_a_2691_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2___boxed(lean_object* v_goal_2699_, lean_object* v_x_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
lean_object* v_res_2706_; 
v_res_2706_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2(v_goal_2699_, v_x_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
lean_dec_ref(v_x_2700_);
return v_res_2706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__6(lean_object* v_leavePercentHeartbeats_2707_, lean_object* v_goal_2708_, lean_object* v___x_2709_, lean_object* v_tactic_2710_, lean_object* v_allowFailure_2711_, uint8_t v_collectAll_2712_, uint8_t v_includeStar_2713_, uint8_t v___x_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v___x_2723_; 
v___x_2723_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercentHeartbeats_2707_, v___y_2717_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_object* v_a_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v_a_2724_ = lean_ctor_get(v___x_2723_, 0);
lean_inc(v_a_2724_);
lean_dec_ref_known(v___x_2723_, 1);
v___x_2725_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___closed__0));
lean_inc(v_goal_2708_);
v___x_2726_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v___x_2725_, v_goal_2708_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_object* v_a_2727_; lean_object* v___f_2728_; lean_object* v___x_2729_; 
v_a_2727_ = lean_ctor_get(v___x_2726_, 0);
lean_inc(v_a_2727_);
lean_dec_ref_known(v___x_2726_, 1);
v___f_2728_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2728_, 0, v_a_2724_);
lean_closure_set(v___f_2728_, 1, v___x_2709_);
lean_closure_set(v___f_2728_, 2, v_tactic_2710_);
lean_closure_set(v___f_2728_, 3, v_allowFailure_2711_);
lean_inc_ref(v___f_2728_);
v___x_2729_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2728_, v_a_2727_, v_collectAll_2712_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
lean_dec(v_a_2727_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_object* v_a_2730_; 
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_a_2730_);
if (lean_obj_tag(v_a_2730_) == 0)
{
lean_dec_ref_known(v___x_2729_, 1);
lean_dec_ref(v___f_2728_);
lean_dec(v_goal_2708_);
goto v___jp_2720_;
}
else
{
lean_object* v_val_2731_; lean_object* v___x_2781_; lean_object* v___x_2782_; uint8_t v___x_2783_; 
v_val_2731_ = lean_ctor_get(v_a_2730_, 0);
v___x_2781_ = lean_unsigned_to_nat(0u);
v___x_2782_ = lean_array_get_size(v_val_2731_);
v___x_2783_ = lean_nat_dec_lt(v___x_2781_, v___x_2782_);
if (v___x_2783_ == 0)
{
goto v___jp_2777_;
}
else
{
if (v___x_2783_ == 0)
{
goto v___jp_2777_;
}
else
{
size_t v___x_2784_; size_t v___x_2785_; uint8_t v___x_2786_; 
v___x_2784_ = ((size_t)0ULL);
v___x_2785_ = lean_usize_of_nat(v___x_2782_);
v___x_2786_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_val_2731_, v___x_2784_, v___x_2785_);
if (v___x_2786_ == 0)
{
goto v___jp_2777_;
}
else
{
if (v___x_2714_ == 0)
{
goto v___jp_2776_;
}
else
{
lean_dec_ref_known(v_a_2730_, 1);
lean_dec_ref(v___f_2728_);
lean_dec(v_goal_2708_);
return v___x_2729_;
}
}
}
}
v___jp_2732_:
{
lean_object* v___x_2733_; 
v___x_2733_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2767_; 
v_a_2734_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2736_ = v___x_2733_;
v_isShared_2737_ = v_isSharedCheck_2767_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2733_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2767_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; uint8_t v___x_2740_; 
v___x_2738_ = lean_array_get_size(v_a_2734_);
v___x_2739_ = lean_unsigned_to_nat(0u);
v___x_2740_ = lean_nat_dec_eq(v___x_2738_, v___x_2739_);
if (v___x_2740_ == 0)
{
lean_object* v___x_2741_; lean_object* v_mctx_2742_; size_t v_sz_2743_; size_t v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
lean_inc(v_val_2731_);
lean_del_object(v___x_2736_);
lean_dec_ref_known(v_a_2730_, 1);
v___x_2741_ = lean_st_ref_get(v___y_2716_);
v_mctx_2742_ = lean_ctor_get(v___x_2741_, 0);
lean_inc_ref(v_mctx_2742_);
lean_dec(v___x_2741_);
v_sz_2743_ = lean_array_size(v_a_2734_);
v___x_2744_ = ((size_t)0ULL);
v___x_2745_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2708_, v_mctx_2742_, v_sz_2743_, v___x_2744_, v_a_2734_);
v___x_2746_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2728_, v___x_2745_, v_collectAll_2712_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
lean_dec_ref(v___x_2745_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2763_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2749_ = v___x_2746_;
v_isShared_2750_ = v_isSharedCheck_2763_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2746_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2763_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
if (lean_obj_tag(v_a_2747_) == 0)
{
lean_del_object(v___x_2749_);
lean_dec(v_val_2731_);
goto v___jp_2720_;
}
else
{
lean_object* v_val_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2762_; 
v_val_2751_ = lean_ctor_get(v_a_2747_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v_a_2747_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2753_ = v_a_2747_;
v_isShared_2754_ = v_isSharedCheck_2762_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_val_2751_);
lean_dec(v_a_2747_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2762_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2755_; lean_object* v___x_2757_; 
v___x_2755_ = l_Array_append___redArg(v_val_2731_, v_val_2751_);
lean_dec(v_val_2751_);
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 0, v___x_2755_);
v___x_2757_ = v___x_2753_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v___x_2755_);
v___x_2757_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
lean_object* v___x_2759_; 
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 0, v___x_2757_);
v___x_2759_ = v___x_2749_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v___x_2757_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
}
}
}
else
{
lean_dec(v_val_2731_);
return v___x_2746_;
}
}
else
{
lean_object* v___x_2765_; 
lean_dec(v_a_2734_);
lean_dec_ref(v___f_2728_);
lean_dec(v_goal_2708_);
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 0, v_a_2730_);
v___x_2765_ = v___x_2736_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2730_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
}
else
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
lean_dec_ref_known(v_a_2730_, 1);
lean_dec_ref(v___f_2728_);
lean_dec(v_goal_2708_);
v_a_2768_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2733_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2733_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
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
v___jp_2776_:
{
if (v_includeStar_2713_ == 0)
{
if (v___x_2714_ == 0)
{
lean_dec_ref_known(v___x_2729_, 1);
goto v___jp_2732_;
}
else
{
lean_dec_ref_known(v_a_2730_, 1);
lean_dec_ref(v___f_2728_);
lean_dec(v_goal_2708_);
return v___x_2729_;
}
}
else
{
lean_dec_ref_known(v___x_2729_, 1);
goto v___jp_2732_;
}
}
v___jp_2777_:
{
if (v_collectAll_2712_ == 0)
{
if (v___x_2714_ == 0)
{
goto v___jp_2776_;
}
else
{
lean_object* v___x_2778_; lean_object* v___x_2779_; uint8_t v___x_2780_; 
v___x_2778_ = lean_array_get_size(v_val_2731_);
v___x_2779_ = lean_unsigned_to_nat(0u);
v___x_2780_ = lean_nat_dec_eq(v___x_2778_, v___x_2779_);
if (v___x_2780_ == 0)
{
lean_dec_ref_known(v_a_2730_, 1);
lean_dec_ref(v___f_2728_);
lean_dec(v_goal_2708_);
return v___x_2729_;
}
else
{
goto v___jp_2776_;
}
}
}
else
{
goto v___jp_2776_;
}
}
}
}
else
{
lean_dec_ref(v___f_2728_);
lean_dec(v_goal_2708_);
return v___x_2729_;
}
}
else
{
lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2794_; 
lean_dec(v_a_2724_);
lean_dec_ref(v_allowFailure_2711_);
lean_dec_ref(v_tactic_2710_);
lean_dec_ref(v___x_2709_);
lean_dec(v_goal_2708_);
v_a_2787_ = lean_ctor_get(v___x_2726_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2789_ = v___x_2726_;
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_dec(v___x_2726_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2790_ == 0)
{
v___x_2792_ = v___x_2789_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2787_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
}
else
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
lean_dec_ref(v_allowFailure_2711_);
lean_dec_ref(v_tactic_2710_);
lean_dec_ref(v___x_2709_);
lean_dec(v_goal_2708_);
v_a_2795_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v___x_2723_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2723_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2795_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
v___jp_2720_:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2721_ = lean_box(0);
v___x_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
return v___x_2722_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__6___boxed(lean_object* v_leavePercentHeartbeats_2803_, lean_object* v_goal_2804_, lean_object* v___x_2805_, lean_object* v_tactic_2806_, lean_object* v_allowFailure_2807_, lean_object* v_collectAll_2808_, lean_object* v_includeStar_2809_, lean_object* v___x_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
uint8_t v_collectAll_boxed_2816_; uint8_t v_includeStar_boxed_2817_; uint8_t v___x_13959__boxed_2818_; lean_object* v_res_2819_; 
v_collectAll_boxed_2816_ = lean_unbox(v_collectAll_2808_);
v_includeStar_boxed_2817_ = lean_unbox(v_includeStar_2809_);
v___x_13959__boxed_2818_ = lean_unbox(v___x_2810_);
v_res_2819_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__6(v_leavePercentHeartbeats_2803_, v_goal_2804_, v___x_2805_, v_tactic_2806_, v_allowFailure_2807_, v_collectAll_boxed_2816_, v_includeStar_boxed_2817_, v___x_13959__boxed_2818_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec(v_leavePercentHeartbeats_2803_);
return v_res_2819_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(lean_object* v_e_2820_){
_start:
{
if (lean_obj_tag(v_e_2820_) == 0)
{
uint8_t v___x_2821_; 
v___x_2821_ = 2;
return v___x_2821_;
}
else
{
lean_object* v_a_2822_; 
v_a_2822_ = lean_ctor_get(v_e_2820_, 0);
if (lean_obj_tag(v_a_2822_) == 0)
{
uint8_t v___x_2823_; 
v___x_2823_ = 1;
return v___x_2823_;
}
else
{
uint8_t v___x_2824_; 
v___x_2824_ = 0;
return v___x_2824_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4___boxed(lean_object* v_e_2825_){
_start:
{
uint8_t v_res_2826_; lean_object* v_r_2827_; 
v_res_2826_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(v_e_2825_);
lean_dec_ref(v_e_2825_);
v_r_2827_ = lean_box(v_res_2826_);
return v_r_2827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(lean_object* v_cls_2828_, uint8_t v_collapsed_2829_, lean_object* v_tag_2830_, lean_object* v_opts_2831_, uint8_t v_clsEnabled_2832_, lean_object* v_oldTraces_2833_, lean_object* v_msg_2834_, lean_object* v_resStartStop_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
lean_object* v_fst_2841_; lean_object* v_snd_2842_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v_data_2846_; lean_object* v_fst_2857_; lean_object* v_snd_2858_; lean_object* v___x_2859_; uint8_t v___x_2860_; lean_object* v___y_2862_; lean_object* v_a_2863_; uint8_t v___y_2878_; double v___y_2909_; 
v_fst_2841_ = lean_ctor_get(v_resStartStop_2835_, 0);
lean_inc(v_fst_2841_);
v_snd_2842_ = lean_ctor_get(v_resStartStop_2835_, 1);
lean_inc(v_snd_2842_);
lean_dec_ref(v_resStartStop_2835_);
v_fst_2857_ = lean_ctor_get(v_snd_2842_, 0);
lean_inc(v_fst_2857_);
v_snd_2858_ = lean_ctor_get(v_snd_2842_, 1);
lean_inc(v_snd_2858_);
lean_dec(v_snd_2842_);
v___x_2859_ = l_Lean_trace_profiler;
v___x_2860_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_2831_, v___x_2859_);
if (v___x_2860_ == 0)
{
v___y_2878_ = v___x_2860_;
goto v___jp_2877_;
}
else
{
lean_object* v___x_2914_; uint8_t v___x_2915_; 
v___x_2914_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2915_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_2831_, v___x_2914_);
if (v___x_2915_ == 0)
{
lean_object* v___x_2916_; lean_object* v___x_2917_; double v___x_2918_; double v___x_2919_; double v___x_2920_; 
v___x_2916_ = l_Lean_trace_profiler_threshold;
v___x_2917_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_2831_, v___x_2916_);
v___x_2918_ = lean_float_of_nat(v___x_2917_);
v___x_2919_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3);
v___x_2920_ = lean_float_div(v___x_2918_, v___x_2919_);
v___y_2909_ = v___x_2920_;
goto v___jp_2908_;
}
else
{
lean_object* v___x_2921_; lean_object* v___x_2922_; double v___x_2923_; 
v___x_2921_ = l_Lean_trace_profiler_threshold;
v___x_2922_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_2831_, v___x_2921_);
v___x_2923_ = lean_float_of_nat(v___x_2922_);
v___y_2909_ = v___x_2923_;
goto v___jp_2908_;
}
}
v___jp_2843_:
{
lean_object* v___x_2847_; 
lean_inc(v___y_2844_);
v___x_2847_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(v_oldTraces_2833_, v_data_2846_, v___y_2844_, v___y_2845_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v___x_2848_; 
lean_dec_ref_known(v___x_2847_, 1);
v___x_2848_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_2841_);
return v___x_2848_;
}
else
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2856_; 
lean_dec(v_fst_2841_);
v_a_2849_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2851_ = v___x_2847_;
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2847_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2849_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
}
v___jp_2861_:
{
uint8_t v_result_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; double v___x_2867_; lean_object* v_data_2868_; 
v_result_2864_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(v_fst_2841_);
v___x_2865_ = lean_box(v_result_2864_);
v___x_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2865_);
v___x_2867_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0);
lean_inc_ref(v_tag_2830_);
lean_inc_ref(v___x_2866_);
lean_inc(v_cls_2828_);
v_data_2868_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2868_, 0, v_cls_2828_);
lean_ctor_set(v_data_2868_, 1, v___x_2866_);
lean_ctor_set(v_data_2868_, 2, v_tag_2830_);
lean_ctor_set_float(v_data_2868_, sizeof(void*)*3, v___x_2867_);
lean_ctor_set_float(v_data_2868_, sizeof(void*)*3 + 8, v___x_2867_);
lean_ctor_set_uint8(v_data_2868_, sizeof(void*)*3 + 16, v_collapsed_2829_);
if (v___x_2860_ == 0)
{
lean_dec_ref_known(v___x_2866_, 1);
lean_dec(v_snd_2858_);
lean_dec(v_fst_2857_);
lean_dec_ref(v_tag_2830_);
lean_dec(v_cls_2828_);
v___y_2844_ = v___y_2862_;
v___y_2845_ = v_a_2863_;
v_data_2846_ = v_data_2868_;
goto v___jp_2843_;
}
else
{
lean_object* v_data_2869_; double v___x_2870_; double v___x_2871_; 
lean_dec_ref_known(v_data_2868_, 3);
v_data_2869_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2869_, 0, v_cls_2828_);
lean_ctor_set(v_data_2869_, 1, v___x_2866_);
lean_ctor_set(v_data_2869_, 2, v_tag_2830_);
v___x_2870_ = lean_unbox_float(v_fst_2857_);
lean_dec(v_fst_2857_);
lean_ctor_set_float(v_data_2869_, sizeof(void*)*3, v___x_2870_);
v___x_2871_ = lean_unbox_float(v_snd_2858_);
lean_dec(v_snd_2858_);
lean_ctor_set_float(v_data_2869_, sizeof(void*)*3 + 8, v___x_2871_);
lean_ctor_set_uint8(v_data_2869_, sizeof(void*)*3 + 16, v_collapsed_2829_);
v___y_2844_ = v___y_2862_;
v___y_2845_ = v_a_2863_;
v_data_2846_ = v_data_2869_;
goto v___jp_2843_;
}
}
v___jp_2872_:
{
lean_object* v_ref_2873_; lean_object* v___x_2874_; 
v_ref_2873_ = lean_ctor_get(v___y_2838_, 2);
lean_inc(v___y_2839_);
lean_inc_ref(v___y_2838_);
lean_inc(v___y_2837_);
lean_inc_ref(v___y_2836_);
lean_inc(v_fst_2841_);
v___x_2874_ = lean_apply_6(v_msg_2834_, v_fst_2841_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, lean_box(0));
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; 
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_a_2875_);
lean_dec_ref_known(v___x_2874_, 1);
v___y_2862_ = v_ref_2873_;
v_a_2863_ = v_a_2875_;
goto v___jp_2861_;
}
else
{
lean_object* v___x_2876_; 
lean_dec_ref_known(v___x_2874_, 1);
v___x_2876_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2);
v___y_2862_ = v_ref_2873_;
v_a_2863_ = v___x_2876_;
goto v___jp_2861_;
}
}
v___jp_2877_:
{
if (v_clsEnabled_2832_ == 0)
{
if (v___y_2878_ == 0)
{
lean_object* v___x_2879_; lean_object* v_traceState_2880_; lean_object* v_env_2881_; lean_object* v_nextMacroScope_2882_; lean_object* v_ngen_2883_; lean_object* v_auxDeclNGen_2884_; lean_object* v_cache_2885_; lean_object* v_messages_2886_; lean_object* v_infoState_2887_; lean_object* v_snapshotTasks_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2907_; 
lean_dec(v_snd_2858_);
lean_dec(v_fst_2857_);
lean_dec_ref(v_msg_2834_);
lean_dec_ref(v_tag_2830_);
lean_dec(v_cls_2828_);
v___x_2879_ = lean_st_ref_take(v___y_2839_);
v_traceState_2880_ = lean_ctor_get(v___x_2879_, 4);
v_env_2881_ = lean_ctor_get(v___x_2879_, 0);
v_nextMacroScope_2882_ = lean_ctor_get(v___x_2879_, 1);
v_ngen_2883_ = lean_ctor_get(v___x_2879_, 2);
v_auxDeclNGen_2884_ = lean_ctor_get(v___x_2879_, 3);
v_cache_2885_ = lean_ctor_get(v___x_2879_, 5);
v_messages_2886_ = lean_ctor_get(v___x_2879_, 6);
v_infoState_2887_ = lean_ctor_get(v___x_2879_, 7);
v_snapshotTasks_2888_ = lean_ctor_get(v___x_2879_, 8);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2890_ = v___x_2879_;
v_isShared_2891_ = v_isSharedCheck_2907_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_snapshotTasks_2888_);
lean_inc(v_infoState_2887_);
lean_inc(v_messages_2886_);
lean_inc(v_cache_2885_);
lean_inc(v_traceState_2880_);
lean_inc(v_auxDeclNGen_2884_);
lean_inc(v_ngen_2883_);
lean_inc(v_nextMacroScope_2882_);
lean_inc(v_env_2881_);
lean_dec(v___x_2879_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2907_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
uint64_t v_tid_2892_; lean_object* v_traces_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2906_; 
v_tid_2892_ = lean_ctor_get_uint64(v_traceState_2880_, sizeof(void*)*1);
v_traces_2893_ = lean_ctor_get(v_traceState_2880_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v_traceState_2880_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2895_ = v_traceState_2880_;
v_isShared_2896_ = v_isSharedCheck_2906_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_traces_2893_);
lean_dec(v_traceState_2880_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2906_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2897_; lean_object* v___x_2899_; 
v___x_2897_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2833_, v_traces_2893_);
lean_dec_ref(v_traces_2893_);
if (v_isShared_2896_ == 0)
{
lean_ctor_set(v___x_2895_, 0, v___x_2897_);
v___x_2899_ = v___x_2895_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v___x_2897_);
lean_ctor_set_uint64(v_reuseFailAlloc_2905_, sizeof(void*)*1, v_tid_2892_);
v___x_2899_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
lean_object* v___x_2901_; 
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 4, v___x_2899_);
v___x_2901_ = v___x_2890_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_env_2881_);
lean_ctor_set(v_reuseFailAlloc_2904_, 1, v_nextMacroScope_2882_);
lean_ctor_set(v_reuseFailAlloc_2904_, 2, v_ngen_2883_);
lean_ctor_set(v_reuseFailAlloc_2904_, 3, v_auxDeclNGen_2884_);
lean_ctor_set(v_reuseFailAlloc_2904_, 4, v___x_2899_);
lean_ctor_set(v_reuseFailAlloc_2904_, 5, v_cache_2885_);
lean_ctor_set(v_reuseFailAlloc_2904_, 6, v_messages_2886_);
lean_ctor_set(v_reuseFailAlloc_2904_, 7, v_infoState_2887_);
lean_ctor_set(v_reuseFailAlloc_2904_, 8, v_snapshotTasks_2888_);
v___x_2901_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2902_ = lean_st_ref_put(v___y_2839_, v___x_2901_);
v___x_2903_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_2841_);
return v___x_2903_;
}
}
}
}
}
else
{
goto v___jp_2872_;
}
}
else
{
goto v___jp_2872_;
}
}
v___jp_2908_:
{
double v___x_2910_; double v___x_2911_; double v___x_2912_; uint8_t v___x_2913_; 
v___x_2910_ = lean_unbox_float(v_snd_2858_);
v___x_2911_ = lean_unbox_float(v_fst_2857_);
v___x_2912_ = lean_float_sub(v___x_2910_, v___x_2911_);
v___x_2913_ = lean_float_decLt(v___y_2909_, v___x_2912_);
v___y_2878_ = v___x_2913_;
goto v___jp_2877_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4___boxed(lean_object* v_cls_2924_, lean_object* v_collapsed_2925_, lean_object* v_tag_2926_, lean_object* v_opts_2927_, lean_object* v_clsEnabled_2928_, lean_object* v_oldTraces_2929_, lean_object* v_msg_2930_, lean_object* v_resStartStop_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
uint8_t v_collapsed_boxed_2937_; uint8_t v_clsEnabled_boxed_2938_; lean_object* v_res_2939_; 
v_collapsed_boxed_2937_ = lean_unbox(v_collapsed_2925_);
v_clsEnabled_boxed_2938_ = lean_unbox(v_clsEnabled_2928_);
v_res_2939_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v_cls_2924_, v_collapsed_boxed_2937_, v_tag_2926_, v_opts_2927_, v_clsEnabled_boxed_2938_, v_oldTraces_2929_, v_msg_2930_, v_resStartStop_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec_ref(v_opts_2927_);
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(lean_object* v_goal_2943_, lean_object* v_tactic_2944_, lean_object* v_allowFailure_2945_, lean_object* v_leavePercentHeartbeats_2946_, uint8_t v_includeStar_2947_, uint8_t v_collectAll_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_){
_start:
{
lean_object* v_toCold_2954_; lean_object* v_options_2955_; lean_object* v_inheritedTraceOptions_2956_; uint8_t v_hasTrace_2957_; lean_object* v___x_2958_; 
v_toCold_2954_ = lean_ctor_get(v_a_2951_, 0);
v_options_2955_ = lean_ctor_get(v_toCold_2954_, 2);
v_inheritedTraceOptions_2956_ = lean_ctor_get(v_toCold_2954_, 11);
v_hasTrace_2957_ = lean_ctor_get_uint8(v_options_2955_, sizeof(void*)*1);
v___x_2958_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
if (v_hasTrace_2957_ == 0)
{
lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___f_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2959_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___closed__0));
v___x_2960_ = lean_box(v_collectAll_2948_);
v___x_2961_ = lean_box(v_includeStar_2947_);
v___f_2962_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed), 12, 7);
lean_closure_set(v___f_2962_, 0, v_leavePercentHeartbeats_2946_);
lean_closure_set(v___f_2962_, 1, v_goal_2943_);
lean_closure_set(v___f_2962_, 2, v___x_2959_);
lean_closure_set(v___f_2962_, 3, v_tactic_2944_);
lean_closure_set(v___f_2962_, 4, v_allowFailure_2945_);
lean_closure_set(v___f_2962_, 5, v___x_2960_);
lean_closure_set(v___f_2962_, 6, v___x_2961_);
v___x_2963_ = lean_box(0);
v___x_2964_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_2958_, v_options_2955_, v___f_2962_, v___x_2963_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_);
return v___x_2964_;
}
else
{
lean_object* v___f_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; uint8_t v___x_2969_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v_a_2973_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v_a_2988_; 
lean_inc(v_goal_2943_);
v___f_2965_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2965_, 0, v_goal_2943_);
v___x_2966_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_2967_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__4));
v___x_2968_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2);
v___x_2969_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2956_, v_options_2955_, v___x_2968_);
if (v___x_2969_ == 0)
{
lean_object* v___x_3051_; uint8_t v___x_3052_; 
v___x_3051_ = l_Lean_trace_profiler;
v___x_3052_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_2955_, v___x_3051_);
if (v___x_3052_ == 0)
{
uint8_t v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___f_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
lean_dec_ref(v___f_2965_);
v___x_3053_ = 0;
v___x_3054_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3054_, 0, v___x_3053_);
lean_ctor_set_uint8(v___x_3054_, 1, v_hasTrace_2957_);
lean_ctor_set_uint8(v___x_3054_, 2, v_hasTrace_2957_);
lean_ctor_set_uint8(v___x_3054_, 3, v_hasTrace_2957_);
v___x_3055_ = lean_box(v_collectAll_2948_);
v___x_3056_ = lean_box(v_includeStar_2947_);
v___f_3057_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed), 12, 7);
lean_closure_set(v___f_3057_, 0, v_leavePercentHeartbeats_2946_);
lean_closure_set(v___f_3057_, 1, v_goal_2943_);
lean_closure_set(v___f_3057_, 2, v___x_3054_);
lean_closure_set(v___f_3057_, 3, v_tactic_2944_);
lean_closure_set(v___f_3057_, 4, v_allowFailure_2945_);
lean_closure_set(v___f_3057_, 5, v___x_3055_);
lean_closure_set(v___f_3057_, 6, v___x_3056_);
v___x_3058_ = lean_box(0);
v___x_3059_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_2958_, v_options_2955_, v___f_3057_, v___x_3058_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_);
return v___x_3059_;
}
else
{
goto v___jp_2997_;
}
}
else
{
goto v___jp_2997_;
}
v___jp_2970_:
{
lean_object* v___x_2974_; double v___x_2975_; double v___x_2976_; double v___x_2977_; double v___x_2978_; double v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2974_ = lean_io_mono_nanos_now();
v___x_2975_ = lean_float_of_nat(v___y_2971_);
v___x_2976_ = lean_float_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3);
v___x_2977_ = lean_float_div(v___x_2975_, v___x_2976_);
v___x_2978_ = lean_float_of_nat(v___x_2974_);
v___x_2979_ = lean_float_div(v___x_2978_, v___x_2976_);
v___x_2980_ = lean_box_float(v___x_2977_);
v___x_2981_ = lean_box_float(v___x_2979_);
v___x_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2980_);
lean_ctor_set(v___x_2982_, 1, v___x_2981_);
v___x_2983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2983_, 0, v_a_2973_);
lean_ctor_set(v___x_2983_, 1, v___x_2982_);
v___x_2984_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v___x_2966_, v_hasTrace_2957_, v___x_2967_, v_options_2955_, v___x_2969_, v___y_2972_, v___f_2965_, v___x_2983_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_);
return v___x_2984_;
}
v___jp_2985_:
{
lean_object* v___x_2989_; double v___x_2990_; double v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2989_ = lean_io_get_num_heartbeats();
v___x_2990_ = lean_float_of_nat(v___y_2987_);
v___x_2991_ = lean_float_of_nat(v___x_2989_);
v___x_2992_ = lean_box_float(v___x_2990_);
v___x_2993_ = lean_box_float(v___x_2991_);
v___x_2994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2992_);
lean_ctor_set(v___x_2994_, 1, v___x_2993_);
v___x_2995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2995_, 0, v_a_2988_);
lean_ctor_set(v___x_2995_, 1, v___x_2994_);
v___x_2996_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v___x_2966_, v_hasTrace_2957_, v___x_2967_, v_options_2955_, v___x_2969_, v___y_2986_, v___f_2965_, v___x_2995_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_);
return v___x_2996_;
}
v___jp_2997_:
{
lean_object* v___x_2998_; lean_object* v_a_2999_; lean_object* v___x_3000_; uint8_t v___x_3001_; 
v___x_2998_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v_a_2952_);
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
lean_inc(v_a_2999_);
lean_dec_ref(v___x_2998_);
v___x_3000_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3001_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_2955_, v___x_3000_);
if (v___x_3001_ == 0)
{
lean_object* v___x_3002_; uint8_t v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___f_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_3002_ = lean_io_mono_nanos_now();
v___x_3003_ = 0;
v___x_3004_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3004_, 0, v___x_3003_);
lean_ctor_set_uint8(v___x_3004_, 1, v_hasTrace_2957_);
lean_ctor_set_uint8(v___x_3004_, 2, v_hasTrace_2957_);
lean_ctor_set_uint8(v___x_3004_, 3, v_hasTrace_2957_);
v___x_3005_ = lean_box(v_collectAll_2948_);
v___x_3006_ = lean_box(v_includeStar_2947_);
v___f_3007_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed), 12, 7);
lean_closure_set(v___f_3007_, 0, v_leavePercentHeartbeats_2946_);
lean_closure_set(v___f_3007_, 1, v_goal_2943_);
lean_closure_set(v___f_3007_, 2, v___x_3004_);
lean_closure_set(v___f_3007_, 3, v_tactic_2944_);
lean_closure_set(v___f_3007_, 4, v_allowFailure_2945_);
lean_closure_set(v___f_3007_, 5, v___x_3005_);
lean_closure_set(v___f_3007_, 6, v___x_3006_);
v___x_3008_ = lean_box(0);
v___x_3009_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_2958_, v_options_2955_, v___f_3007_, v___x_3008_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3017_; 
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3012_ = v___x_3009_;
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v___x_3009_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3015_; 
if (v_isShared_3013_ == 0)
{
lean_ctor_set_tag(v___x_3012_, 1);
v___x_3015_ = v___x_3012_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_a_3010_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
v___y_2971_ = v___x_3002_;
v___y_2972_ = v_a_2999_;
v_a_2973_ = v___x_3015_;
goto v___jp_2970_;
}
}
}
else
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3025_; 
v_a_3018_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3020_ = v___x_3009_;
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_3009_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
if (v_isShared_3021_ == 0)
{
lean_ctor_set_tag(v___x_3020_, 0);
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_a_3018_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
v___y_2971_ = v___x_3002_;
v___y_2972_ = v_a_2999_;
v_a_2973_ = v___x_3023_;
goto v___jp_2970_;
}
}
}
}
else
{
lean_object* v___x_3026_; uint8_t v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___f_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3026_ = lean_io_get_num_heartbeats();
v___x_3027_ = 0;
v___x_3028_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3028_, 0, v___x_3027_);
lean_ctor_set_uint8(v___x_3028_, 1, v___x_3001_);
lean_ctor_set_uint8(v___x_3028_, 2, v___x_3001_);
lean_ctor_set_uint8(v___x_3028_, 3, v___x_3001_);
v___x_3029_ = lean_box(v_collectAll_2948_);
v___x_3030_ = lean_box(v_includeStar_2947_);
v___x_3031_ = lean_box(v___x_3001_);
v___f_3032_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__6___boxed), 13, 8);
lean_closure_set(v___f_3032_, 0, v_leavePercentHeartbeats_2946_);
lean_closure_set(v___f_3032_, 1, v_goal_2943_);
lean_closure_set(v___f_3032_, 2, v___x_3028_);
lean_closure_set(v___f_3032_, 3, v_tactic_2944_);
lean_closure_set(v___f_3032_, 4, v_allowFailure_2945_);
lean_closure_set(v___f_3032_, 5, v___x_3029_);
lean_closure_set(v___f_3032_, 6, v___x_3030_);
lean_closure_set(v___f_3032_, 7, v___x_3031_);
v___x_3033_ = lean_box(0);
v___x_3034_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_2958_, v_options_2955_, v___f_3032_, v___x_3033_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_);
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_object* v_a_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3042_; 
v_a_3035_ = lean_ctor_get(v___x_3034_, 0);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3037_ = v___x_3034_;
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_a_3035_);
lean_dec(v___x_3034_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3040_; 
if (v_isShared_3038_ == 0)
{
lean_ctor_set_tag(v___x_3037_, 1);
v___x_3040_ = v___x_3037_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_3035_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
v___y_2986_ = v_a_2999_;
v___y_2987_ = v___x_3026_;
v_a_2988_ = v___x_3040_;
goto v___jp_2985_;
}
}
}
else
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
v_a_3043_ = lean_ctor_get(v___x_3034_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___x_3034_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_3034_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3048_; 
if (v_isShared_3046_ == 0)
{
lean_ctor_set_tag(v___x_3045_, 0);
v___x_3048_ = v___x_3045_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3043_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
v___y_2986_ = v_a_2999_;
v___y_2987_ = v___x_3026_;
v_a_2988_ = v___x_3048_;
goto v___jp_2985_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___boxed(lean_object* v_goal_3060_, lean_object* v_tactic_3061_, lean_object* v_allowFailure_3062_, lean_object* v_leavePercentHeartbeats_3063_, lean_object* v_includeStar_3064_, lean_object* v_collectAll_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_){
_start:
{
uint8_t v_includeStar_boxed_3071_; uint8_t v_collectAll_boxed_3072_; lean_object* v_res_3073_; 
v_includeStar_boxed_3071_ = lean_unbox(v_includeStar_3064_);
v_collectAll_boxed_3072_ = lean_unbox(v_collectAll_3065_);
v_res_3073_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(v_goal_3060_, v_tactic_3061_, v_allowFailure_3062_, v_leavePercentHeartbeats_3063_, v_includeStar_boxed_3071_, v_collectAll_boxed_3072_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
lean_dec(v_a_3069_);
lean_dec_ref(v_a_3068_);
lean_dec(v_a_3067_);
lean_dec_ref(v_a_3066_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearch(lean_object* v_goal_3074_, lean_object* v_tactic_3075_, lean_object* v_allowFailure_3076_, lean_object* v_leavePercentHeartbeats_3077_, uint8_t v_includeStar_3078_, uint8_t v_collectAll_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_){
_start:
{
lean_object* v___x_3085_; 
v___x_3085_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(v_goal_3074_, v_tactic_3075_, v_allowFailure_3076_, v_leavePercentHeartbeats_3077_, v_includeStar_3078_, v_collectAll_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearch___boxed(lean_object* v_goal_3086_, lean_object* v_tactic_3087_, lean_object* v_allowFailure_3088_, lean_object* v_leavePercentHeartbeats_3089_, lean_object* v_includeStar_3090_, lean_object* v_collectAll_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_){
_start:
{
uint8_t v_includeStar_boxed_3097_; uint8_t v_collectAll_boxed_3098_; lean_object* v_res_3099_; 
v_includeStar_boxed_3097_ = lean_unbox(v_includeStar_3090_);
v_collectAll_boxed_3098_ = lean_unbox(v_collectAll_3091_);
v_res_3099_ = l_Lean_Meta_LibrarySearch_librarySearch(v_goal_3086_, v_tactic_3087_, v_allowFailure_3088_, v_leavePercentHeartbeats_3089_, v_includeStar_boxed_3097_, v_collectAll_boxed_3098_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_);
lean_dec(v_a_3095_);
lean_dec_ref(v_a_3094_);
lean_dec(v_a_3093_);
lean_dec_ref(v_a_3092_);
return v_res_3099_;
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
