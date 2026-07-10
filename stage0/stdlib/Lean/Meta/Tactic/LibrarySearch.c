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
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_of_nat(lean_object*);
double lean_float_div(double, double);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapForallTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerInternalExceptionId(lean_object*);
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_List_isEmpty___redArg(lean_object*);
uint8_t l_Lean_Linter_isDeprecated(lean_object*, lean_object*);
uint8_t l_Lean_Name_isMetaprogramming(lean_object*);
lean_object* l_Lean_AsyncConstantInfo_toConstantVal(lean_object*);
lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SolveByElim_solveByElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(lean_object*, lean_object*);
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
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__0;
static const lean_string_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__1_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3;
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
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_LibrarySearch_libSearchFindDecls___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_480_; uint8_t v_transparency_481_; lean_object* v___f_482_; lean_object* v___f_483_; lean_object* v___f_484_; uint8_t v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; lean_object* v___y_489_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
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
v___x_509_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_grindDischarger___closed__3));
v___x_510_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_510_, 0, v___x_486_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
lean_ctor_set_uint8(v___x_510_, sizeof(void*)*2, v_transparency_481_);
lean_ctor_set_uint8(v___x_510_, sizeof(void*)*2 + 1, v___x_485_);
lean_ctor_set_uint8(v___x_510_, sizeof(void*)*2 + 2, v_exfalso_470_);
v___x_511_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_511_, 0, v___x_510_);
lean_ctor_set_uint8(v___x_511_, sizeof(void*)*1, v___x_485_);
lean_ctor_set_uint8(v___x_511_, sizeof(void*)*1 + 1, v___x_485_);
lean_ctor_set_uint8(v___x_511_, sizeof(void*)*1 + 2, v___x_487_);
lean_ctor_set_uint8(v___x_511_, sizeof(void*)*1 + 3, v___x_487_);
if (v_try_x3f_474_ == 0)
{
if (v_grind_473_ == 0)
{
v___y_489_ = v___x_511_;
goto v___jp_488_;
}
else
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__4));
v___x_513_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v___x_511_, v___x_512_);
v___y_489_ = v___x_513_;
goto v___jp_488_;
}
}
else
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__5));
v___x_515_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v___x_511_, v___x_514_);
v___y_489_ = v___x_515_;
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
lean_object* v_a_493_; lean_object* v_fst_494_; lean_object* v_snd_495_; uint8_t v___x_496_; uint8_t v___x_497_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc(v_a_493_);
lean_dec_ref_known(v___x_492_, 1);
v_fst_494_ = lean_ctor_get(v_a_493_, 0);
lean_inc(v_fst_494_);
v_snd_495_ = lean_ctor_get(v_a_493_, 1);
lean_inc(v_snd_495_);
lean_dec(v_a_493_);
v___x_496_ = l_List_isEmpty___redArg(v_required_469_);
v___x_497_ = lean_bool_not(v___x_496_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; 
lean_dec(v_required_469_);
v___x_498_ = l_Lean_Meta_SolveByElim_solveByElim(v___y_489_, v_fst_494_, v_snd_495_, v_goals_471_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
return v___x_498_;
}
else
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(v___y_489_, v_required_469_);
v___x_500_ = l_Lean_Meta_SolveByElim_solveByElim(v___x_499_, v_fst_494_, v_snd_495_, v_goals_471_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
return v___x_500_;
}
}
else
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
lean_dec_ref(v___y_489_);
lean_dec(v_goals_471_);
lean_dec(v_required_469_);
v_a_501_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_508_ == 0)
{
v___x_503_ = v___x_492_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_492_);
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
uint8_t v___x_1299_; uint8_t v___x_1300_; 
v___x_1299_ = l_Lean_Expr_hasMVar(v_e_1296_);
v___x_1300_ = lean_bool_not(v___x_1299_);
if (v___x_1300_ == 0)
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
else
{
lean_object* v___x_1321_; 
v___x_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1321_, 0, v_e_1296_);
return v___x_1321_;
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
lean_object* v_a_1373_; lean_object* v___x_1374_; lean_object* v_mctx_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
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
v___x_1377_ = lean_alloc_closure((void*)(l_Lean_MVarId_applySymm___boxed), 6, 1);
lean_closure_set(v___x_1377_, 0, v_goal_1364_);
v___x_1378_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(v___x_1377_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1439_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1381_ = v___x_1378_;
v_isShared_1382_ = v_isSharedCheck_1439_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1378_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1439_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
if (lean_obj_tag(v_a_1379_) == 1)
{
lean_object* v_val_1383_; lean_object* v___x_1384_; 
lean_del_object(v___x_1381_);
v_val_1383_ = lean_ctor_get(v_a_1379_, 0);
lean_inc_n(v_val_1383_, 2);
lean_dec_ref_known(v_a_1379_, 1);
v___x_1384_ = l_Lean_MVarId_getType(v_val_1383_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1386_; lean_object* v_a_1387_; lean_object* v___x_1388_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1384_, 1);
v___x_1386_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(v_a_1385_, v_a_1366_);
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_a_1387_);
lean_dec_ref(v___x_1386_);
lean_inc(v_a_1368_);
lean_inc_ref(v_a_1367_);
lean_inc(v_a_1366_);
lean_inc_ref(v_a_1365_);
v___x_1388_ = lean_apply_6(v_searchFn_1363_, v_a_1387_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, lean_box(0));
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1416_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1391_ = v___x_1388_;
v_isShared_1392_ = v_isSharedCheck_1416_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1388_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1416_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v_cache_1395_; lean_object* v_zetaDeltaFVarIds_1396_; lean_object* v_postponed_1397_; lean_object* v_diag_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1414_; 
v___x_1393_ = lean_st_ref_get(v_a_1366_);
v___x_1394_ = lean_st_ref_take(v_a_1366_);
v_cache_1395_ = lean_ctor_get(v___x_1394_, 1);
v_zetaDeltaFVarIds_1396_ = lean_ctor_get(v___x_1394_, 2);
v_postponed_1397_ = lean_ctor_get(v___x_1394_, 3);
v_diag_1398_ = lean_ctor_get(v___x_1394_, 4);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1414_ == 0)
{
lean_object* v_unused_1415_; 
v_unused_1415_ = lean_ctor_get(v___x_1394_, 0);
lean_dec(v_unused_1415_);
v___x_1400_ = v___x_1394_;
v_isShared_1401_ = v_isSharedCheck_1414_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_diag_1398_);
lean_inc(v_postponed_1397_);
lean_inc(v_zetaDeltaFVarIds_1396_);
lean_inc(v_cache_1395_);
lean_dec(v___x_1394_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1414_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 0, v_mctx_1375_);
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_mctx_1375_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_cache_1395_);
lean_ctor_set(v_reuseFailAlloc_1413_, 2, v_zetaDeltaFVarIds_1396_);
lean_ctor_set(v_reuseFailAlloc_1413_, 3, v_postponed_1397_);
lean_ctor_set(v_reuseFailAlloc_1413_, 4, v_diag_1398_);
v___x_1403_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
lean_object* v___x_1404_; lean_object* v_mctx_1405_; lean_object* v___f_1406_; lean_object* v___x_1407_; lean_object* v___f_1408_; lean_object* v___x_1409_; lean_object* v___x_1411_; 
v___x_1404_ = lean_st_ref_set(v_a_1366_, v___x_1403_);
v_mctx_1405_ = lean_ctor_get(v___x_1393_, 0);
lean_inc_ref(v_mctx_1405_);
lean_dec(v___x_1393_);
v___f_1406_ = lean_alloc_closure((void*)(l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0), 2, 1);
lean_closure_set(v___f_1406_, 0, v___x_1376_);
v___x_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1407_, 0, v_val_1383_);
lean_ctor_set(v___x_1407_, 1, v_mctx_1405_);
v___f_1408_ = lean_alloc_closure((void*)(l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0), 2, 1);
lean_closure_set(v___f_1408_, 0, v___x_1407_);
v___x_1409_ = l_Lean_Meta_LibrarySearch_interleaveWith___redArg(v___f_1406_, v_a_1373_, v___f_1408_, v_a_1389_);
lean_dec(v_a_1389_);
lean_dec(v_a_1373_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 0, v___x_1409_);
v___x_1411_ = v___x_1391_;
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
lean_dec(v_val_1383_);
lean_dec_ref_known(v___x_1376_, 2);
lean_dec_ref(v_mctx_1375_);
lean_dec(v_a_1373_);
v_a_1417_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___x_1388_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1388_);
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
lean_dec(v_val_1383_);
lean_dec_ref_known(v___x_1376_, 2);
lean_dec_ref(v_mctx_1375_);
lean_dec(v_a_1373_);
lean_dec_ref(v_searchFn_1363_);
v_a_1425_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1384_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1384_);
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
lean_dec(v_a_1379_);
lean_dec_ref(v_mctx_1375_);
lean_dec_ref(v_searchFn_1363_);
v_sz_1433_ = lean_array_size(v_a_1373_);
v___x_1434_ = ((size_t)0ULL);
v___x_1435_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(v___x_1376_, v_sz_1433_, v___x_1434_, v_a_1373_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 0, v___x_1435_);
v___x_1437_ = v___x_1381_;
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
lean_dec_ref_known(v___x_1376_, 2);
lean_dec_ref(v_mctx_1375_);
lean_dec(v_a_1373_);
lean_dec_ref(v_searchFn_1363_);
v_a_1440_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1378_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1378_);
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
lean_object* v___x_1525_; 
v___x_1525_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_lem_1518_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
if (lean_obj_tag(v___x_1525_) == 0)
{
switch(v_mod_1519_)
{
case 0:
{
return v___x_1525_;
}
case 1:
{
lean_object* v_a_1526_; lean_object* v___f_1527_; lean_object* v___x_1528_; 
v_a_1526_ = lean_ctor_get(v___x_1525_, 0);
lean_inc(v_a_1526_);
lean_dec_ref_known(v___x_1525_, 1);
v___f_1527_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__0));
v___x_1528_ = l_Lean_Meta_mapForallTelescope(v___f_1527_, v_a_1526_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
return v___x_1528_;
}
default: 
{
lean_object* v_a_1529_; lean_object* v___f_1530_; lean_object* v___x_1531_; 
v_a_1529_ = lean_ctor_get(v___x_1525_, 0);
lean_inc(v_a_1529_);
lean_dec_ref_known(v___x_1525_, 1);
v___f_1530_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__1));
v___x_1531_ = l_Lean_Meta_mapForallTelescope(v___f_1530_, v_a_1529_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
return v___x_1531_;
}
}
}
else
{
return v___x_1525_;
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
lean_object* v___x_1560_; lean_object* v_traceState_1561_; lean_object* v_traces_1562_; lean_object* v___x_1563_; lean_object* v_traceState_1564_; lean_object* v_env_1565_; lean_object* v_nextMacroScope_1566_; lean_object* v_ngen_1567_; lean_object* v_auxDeclNGen_1568_; lean_object* v_cache_1569_; lean_object* v_messages_1570_; lean_object* v_infoState_1571_; lean_object* v_snapshotTasks_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1591_; 
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
v_messages_1570_ = lean_ctor_get(v___x_1563_, 6);
v_infoState_1571_ = lean_ctor_get(v___x_1563_, 7);
v_snapshotTasks_1572_ = lean_ctor_get(v___x_1563_, 8);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1574_ = v___x_1563_;
v_isShared_1575_ = v_isSharedCheck_1591_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_snapshotTasks_1572_);
lean_inc(v_infoState_1571_);
lean_inc(v_messages_1570_);
lean_inc(v_cache_1569_);
lean_inc(v_traceState_1564_);
lean_inc(v_auxDeclNGen_1568_);
lean_inc(v_ngen_1567_);
lean_inc(v_nextMacroScope_1566_);
lean_inc(v_env_1565_);
lean_dec(v___x_1563_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1591_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
uint64_t v_tid_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1589_; 
v_tid_1576_ = lean_ctor_get_uint64(v_traceState_1564_, sizeof(void*)*1);
v_isSharedCheck_1589_ = !lean_is_exclusive(v_traceState_1564_);
if (v_isSharedCheck_1589_ == 0)
{
lean_object* v_unused_1590_; 
v_unused_1590_ = lean_ctor_get(v_traceState_1564_, 0);
lean_dec(v_unused_1590_);
v___x_1578_ = v_traceState_1564_;
v_isShared_1579_ = v_isSharedCheck_1589_;
goto v_resetjp_1577_;
}
else
{
lean_dec(v_traceState_1564_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1589_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1580_; lean_object* v___x_1582_; 
v___x_1580_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1);
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 0, v___x_1580_);
v___x_1582_ = v___x_1578_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1580_);
lean_ctor_set_uint64(v_reuseFailAlloc_1588_, sizeof(void*)*1, v_tid_1576_);
v___x_1582_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
lean_object* v___x_1584_; 
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 4, v___x_1582_);
v___x_1584_ = v___x_1574_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_env_1565_);
lean_ctor_set(v_reuseFailAlloc_1587_, 1, v_nextMacroScope_1566_);
lean_ctor_set(v_reuseFailAlloc_1587_, 2, v_ngen_1567_);
lean_ctor_set(v_reuseFailAlloc_1587_, 3, v_auxDeclNGen_1568_);
lean_ctor_set(v_reuseFailAlloc_1587_, 4, v___x_1582_);
lean_ctor_set(v_reuseFailAlloc_1587_, 5, v_cache_1569_);
lean_ctor_set(v_reuseFailAlloc_1587_, 6, v_messages_1570_);
lean_ctor_set(v_reuseFailAlloc_1587_, 7, v_infoState_1571_);
lean_ctor_set(v_reuseFailAlloc_1587_, 8, v_snapshotTasks_1572_);
v___x_1584_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = lean_st_ref_set(v___y_1558_, v___x_1584_);
v___x_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1586_, 0, v_traces_1562_);
return v___x_1586_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___boxed(lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v___y_1592_);
lean_dec(v___y_1592_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0(lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v___x_1600_; 
v___x_1600_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v___y_1598_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___boxed(lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0(v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
return v_res_1606_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(lean_object* v_opts_1607_, lean_object* v_opt_1608_){
_start:
{
lean_object* v_name_1609_; lean_object* v_defValue_1610_; lean_object* v_map_1611_; lean_object* v___x_1612_; 
v_name_1609_ = lean_ctor_get(v_opt_1608_, 0);
v_defValue_1610_ = lean_ctor_get(v_opt_1608_, 1);
v_map_1611_ = lean_ctor_get(v_opts_1607_, 0);
v___x_1612_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1611_, v_name_1609_);
if (lean_obj_tag(v___x_1612_) == 0)
{
uint8_t v___x_1613_; 
v___x_1613_ = lean_unbox(v_defValue_1610_);
return v___x_1613_;
}
else
{
lean_object* v_val_1614_; 
v_val_1614_ = lean_ctor_get(v___x_1612_, 0);
lean_inc(v_val_1614_);
lean_dec_ref_known(v___x_1612_, 1);
if (lean_obj_tag(v_val_1614_) == 1)
{
uint8_t v_v_1615_; 
v_v_1615_ = lean_ctor_get_uint8(v_val_1614_, 0);
lean_dec_ref_known(v_val_1614_, 0);
return v_v_1615_;
}
else
{
uint8_t v___x_1616_; 
lean_dec(v_val_1614_);
v___x_1616_ = lean_unbox(v_defValue_1610_);
return v___x_1616_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1___boxed(lean_object* v_opts_1617_, lean_object* v_opt_1618_){
_start:
{
uint8_t v_res_1619_; lean_object* v_r_1620_; 
v_res_1619_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_1617_, v_opt_1618_);
lean_dec_ref(v_opt_1618_);
lean_dec_ref(v_opts_1617_);
v_r_1620_ = lean_box(v_res_1619_);
return v_r_1620_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__0));
v___x_1623_ = l_Lean_stringToMessageData(v___x_1622_);
return v___x_1623_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1625_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__2));
v___x_1626_ = l_Lean_stringToMessageData(v___x_1625_);
return v___x_1626_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1630_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__5));
v___x_1631_ = l_Lean_MessageData_ofFormat(v___x_1630_);
return v___x_1631_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__8));
v___x_1636_ = l_Lean_MessageData_ofFormat(v___x_1635_);
return v___x_1636_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12(void){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__11));
v___x_1641_ = l_Lean_MessageData_ofFormat(v___x_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0(lean_object* v_fst_1642_, uint8_t v_snd_1643_, lean_object* v_x_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___y_1654_; 
v___x_1650_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1);
v___x_1651_ = l_Lean_MessageData_ofName(v_fst_1642_);
v___x_1652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1650_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
switch(v_snd_1643_)
{
case 0:
{
lean_object* v___x_1659_; 
v___x_1659_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6);
v___y_1654_ = v___x_1659_;
goto v___jp_1653_;
}
case 1:
{
lean_object* v___x_1660_; 
v___x_1660_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9);
v___y_1654_ = v___x_1660_;
goto v___jp_1653_;
}
default: 
{
lean_object* v___x_1661_; 
v___x_1661_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12);
v___y_1654_ = v___x_1661_;
goto v___jp_1653_;
}
}
v___jp_1653_:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
lean_inc_ref(v___y_1654_);
v___x_1655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1652_);
lean_ctor_set(v___x_1655_, 1, v___y_1654_);
v___x_1656_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3);
v___x_1657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1655_);
lean_ctor_set(v___x_1657_, 1, v___x_1656_);
v___x_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1657_);
return v___x_1658_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___boxed(lean_object* v_fst_1662_, lean_object* v_snd_1663_, lean_object* v_x_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
uint8_t v_snd_11555__boxed_1670_; lean_object* v_res_1671_; 
v_snd_11555__boxed_1670_ = lean_unbox(v_snd_1663_);
v_res_1671_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0(v_fst_1662_, v_snd_11555__boxed_1670_, v_x_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec_ref(v_x_1664_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(lean_object* v_opts_1672_, lean_object* v_opt_1673_){
_start:
{
lean_object* v_name_1674_; lean_object* v_defValue_1675_; lean_object* v_map_1676_; lean_object* v___x_1677_; 
v_name_1674_ = lean_ctor_get(v_opt_1673_, 0);
v_defValue_1675_ = lean_ctor_get(v_opt_1673_, 1);
v_map_1676_ = lean_ctor_get(v_opts_1672_, 0);
v___x_1677_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1676_, v_name_1674_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_inc(v_defValue_1675_);
return v_defValue_1675_;
}
else
{
lean_object* v_val_1678_; 
v_val_1678_ = lean_ctor_get(v___x_1677_, 0);
lean_inc(v_val_1678_);
lean_dec_ref_known(v___x_1677_, 1);
if (lean_obj_tag(v_val_1678_) == 3)
{
lean_object* v_v_1679_; 
v_v_1679_ = lean_ctor_get(v_val_1678_, 0);
lean_inc(v_v_1679_);
lean_dec_ref_known(v_val_1678_, 1);
return v_v_1679_;
}
else
{
lean_dec(v_val_1678_);
lean_inc(v_defValue_1675_);
return v_defValue_1675_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5___boxed(lean_object* v_opts_1680_, lean_object* v_opt_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_1680_, v_opt_1681_);
lean_dec_ref(v_opt_1681_);
lean_dec_ref(v_opts_1680_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(lean_object* v_x_1683_){
_start:
{
if (lean_obj_tag(v_x_1683_) == 0)
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
v_a_1685_ = lean_ctor_get(v_x_1683_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v_x_1683_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v_x_1683_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v_x_1683_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
lean_ctor_set_tag(v___x_1687_, 1);
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
else
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
v_a_1693_ = lean_ctor_get(v_x_1683_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_x_1683_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v_x_1683_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v_x_1683_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
lean_ctor_set_tag(v___x_1695_, 0);
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1693_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg___boxed(lean_object* v_x_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_x_1701_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3(size_t v_sz_1704_, size_t v_i_1705_, lean_object* v_bs_1706_){
_start:
{
uint8_t v___x_1707_; 
v___x_1707_ = lean_usize_dec_lt(v_i_1705_, v_sz_1704_);
if (v___x_1707_ == 0)
{
return v_bs_1706_;
}
else
{
lean_object* v_v_1708_; lean_object* v_msg_1709_; lean_object* v___x_1710_; lean_object* v_bs_x27_1711_; size_t v___x_1712_; size_t v___x_1713_; lean_object* v___x_1714_; 
v_v_1708_ = lean_array_uget_borrowed(v_bs_1706_, v_i_1705_);
v_msg_1709_ = lean_ctor_get(v_v_1708_, 1);
lean_inc_ref(v_msg_1709_);
v___x_1710_ = lean_unsigned_to_nat(0u);
v_bs_x27_1711_ = lean_array_uset(v_bs_1706_, v_i_1705_, v___x_1710_);
v___x_1712_ = ((size_t)1ULL);
v___x_1713_ = lean_usize_add(v_i_1705_, v___x_1712_);
v___x_1714_ = lean_array_uset(v_bs_x27_1711_, v_i_1705_, v_msg_1709_);
v_i_1705_ = v___x_1713_;
v_bs_1706_ = v___x_1714_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_1716_, lean_object* v_i_1717_, lean_object* v_bs_1718_){
_start:
{
size_t v_sz_boxed_1719_; size_t v_i_boxed_1720_; lean_object* v_res_1721_; 
v_sz_boxed_1719_ = lean_unbox_usize(v_sz_1716_);
lean_dec(v_sz_1716_);
v_i_boxed_1720_ = lean_unbox_usize(v_i_1717_);
lean_dec(v_i_1717_);
v_res_1721_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3(v_sz_boxed_1719_, v_i_boxed_1720_, v_bs_1718_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(lean_object* v_oldTraces_1722_, lean_object* v_data_1723_, lean_object* v_ref_1724_, lean_object* v_msg_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v_fileName_1731_; lean_object* v_fileMap_1732_; lean_object* v_options_1733_; lean_object* v_currRecDepth_1734_; lean_object* v_maxRecDepth_1735_; lean_object* v_ref_1736_; lean_object* v_currNamespace_1737_; lean_object* v_openDecls_1738_; lean_object* v_initHeartbeats_1739_; lean_object* v_maxHeartbeats_1740_; lean_object* v_quotContext_1741_; lean_object* v_currMacroScope_1742_; uint8_t v_diag_1743_; lean_object* v_cancelTk_x3f_1744_; uint8_t v_suppressElabErrors_1745_; lean_object* v_inheritedTraceOptions_1746_; lean_object* v___x_1747_; lean_object* v_traceState_1748_; lean_object* v_traces_1749_; lean_object* v_ref_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; size_t v_sz_1753_; size_t v___x_1754_; lean_object* v___x_1755_; lean_object* v_msg_1756_; lean_object* v___x_1757_; lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1795_; 
v_fileName_1731_ = lean_ctor_get(v___y_1728_, 0);
v_fileMap_1732_ = lean_ctor_get(v___y_1728_, 1);
v_options_1733_ = lean_ctor_get(v___y_1728_, 2);
v_currRecDepth_1734_ = lean_ctor_get(v___y_1728_, 3);
v_maxRecDepth_1735_ = lean_ctor_get(v___y_1728_, 4);
v_ref_1736_ = lean_ctor_get(v___y_1728_, 5);
v_currNamespace_1737_ = lean_ctor_get(v___y_1728_, 6);
v_openDecls_1738_ = lean_ctor_get(v___y_1728_, 7);
v_initHeartbeats_1739_ = lean_ctor_get(v___y_1728_, 8);
v_maxHeartbeats_1740_ = lean_ctor_get(v___y_1728_, 9);
v_quotContext_1741_ = lean_ctor_get(v___y_1728_, 10);
v_currMacroScope_1742_ = lean_ctor_get(v___y_1728_, 11);
v_diag_1743_ = lean_ctor_get_uint8(v___y_1728_, sizeof(void*)*14);
v_cancelTk_x3f_1744_ = lean_ctor_get(v___y_1728_, 12);
v_suppressElabErrors_1745_ = lean_ctor_get_uint8(v___y_1728_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1746_ = lean_ctor_get(v___y_1728_, 13);
v___x_1747_ = lean_st_ref_get(v___y_1729_);
v_traceState_1748_ = lean_ctor_get(v___x_1747_, 4);
lean_inc_ref(v_traceState_1748_);
lean_dec(v___x_1747_);
v_traces_1749_ = lean_ctor_get(v_traceState_1748_, 0);
lean_inc_ref(v_traces_1749_);
lean_dec_ref(v_traceState_1748_);
v_ref_1750_ = l_Lean_replaceRef(v_ref_1724_, v_ref_1736_);
lean_inc_ref(v_inheritedTraceOptions_1746_);
lean_inc(v_cancelTk_x3f_1744_);
lean_inc(v_currMacroScope_1742_);
lean_inc(v_quotContext_1741_);
lean_inc(v_maxHeartbeats_1740_);
lean_inc(v_initHeartbeats_1739_);
lean_inc(v_openDecls_1738_);
lean_inc(v_currNamespace_1737_);
lean_inc(v_maxRecDepth_1735_);
lean_inc(v_currRecDepth_1734_);
lean_inc_ref(v_options_1733_);
lean_inc_ref(v_fileMap_1732_);
lean_inc_ref(v_fileName_1731_);
v___x_1751_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1751_, 0, v_fileName_1731_);
lean_ctor_set(v___x_1751_, 1, v_fileMap_1732_);
lean_ctor_set(v___x_1751_, 2, v_options_1733_);
lean_ctor_set(v___x_1751_, 3, v_currRecDepth_1734_);
lean_ctor_set(v___x_1751_, 4, v_maxRecDepth_1735_);
lean_ctor_set(v___x_1751_, 5, v_ref_1750_);
lean_ctor_set(v___x_1751_, 6, v_currNamespace_1737_);
lean_ctor_set(v___x_1751_, 7, v_openDecls_1738_);
lean_ctor_set(v___x_1751_, 8, v_initHeartbeats_1739_);
lean_ctor_set(v___x_1751_, 9, v_maxHeartbeats_1740_);
lean_ctor_set(v___x_1751_, 10, v_quotContext_1741_);
lean_ctor_set(v___x_1751_, 11, v_currMacroScope_1742_);
lean_ctor_set(v___x_1751_, 12, v_cancelTk_x3f_1744_);
lean_ctor_set(v___x_1751_, 13, v_inheritedTraceOptions_1746_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*14, v_diag_1743_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*14 + 1, v_suppressElabErrors_1745_);
v___x_1752_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1749_);
lean_dec_ref(v_traces_1749_);
v_sz_1753_ = lean_array_size(v___x_1752_);
v___x_1754_ = ((size_t)0ULL);
v___x_1755_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3(v_sz_1753_, v___x_1754_, v___x_1752_);
v_msg_1756_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1756_, 0, v_data_1723_);
lean_ctor_set(v_msg_1756_, 1, v_msg_1725_);
lean_ctor_set(v_msg_1756_, 2, v___x_1755_);
v___x_1757_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(v_msg_1756_, v___y_1726_, v___y_1727_, v___x_1751_, v___y_1729_);
lean_dec_ref_known(v___x_1751_, 14);
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1760_ = v___x_1757_;
v_isShared_1761_ = v_isSharedCheck_1795_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1757_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1795_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1762_; lean_object* v_traceState_1763_; lean_object* v_env_1764_; lean_object* v_nextMacroScope_1765_; lean_object* v_ngen_1766_; lean_object* v_auxDeclNGen_1767_; lean_object* v_cache_1768_; lean_object* v_messages_1769_; lean_object* v_infoState_1770_; lean_object* v_snapshotTasks_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1794_; 
v___x_1762_ = lean_st_ref_take(v___y_1729_);
v_traceState_1763_ = lean_ctor_get(v___x_1762_, 4);
v_env_1764_ = lean_ctor_get(v___x_1762_, 0);
v_nextMacroScope_1765_ = lean_ctor_get(v___x_1762_, 1);
v_ngen_1766_ = lean_ctor_get(v___x_1762_, 2);
v_auxDeclNGen_1767_ = lean_ctor_get(v___x_1762_, 3);
v_cache_1768_ = lean_ctor_get(v___x_1762_, 5);
v_messages_1769_ = lean_ctor_get(v___x_1762_, 6);
v_infoState_1770_ = lean_ctor_get(v___x_1762_, 7);
v_snapshotTasks_1771_ = lean_ctor_get(v___x_1762_, 8);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1773_ = v___x_1762_;
v_isShared_1774_ = v_isSharedCheck_1794_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_snapshotTasks_1771_);
lean_inc(v_infoState_1770_);
lean_inc(v_messages_1769_);
lean_inc(v_cache_1768_);
lean_inc(v_traceState_1763_);
lean_inc(v_auxDeclNGen_1767_);
lean_inc(v_ngen_1766_);
lean_inc(v_nextMacroScope_1765_);
lean_inc(v_env_1764_);
lean_dec(v___x_1762_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1794_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
uint64_t v_tid_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1792_; 
v_tid_1775_ = lean_ctor_get_uint64(v_traceState_1763_, sizeof(void*)*1);
v_isSharedCheck_1792_ = !lean_is_exclusive(v_traceState_1763_);
if (v_isSharedCheck_1792_ == 0)
{
lean_object* v_unused_1793_; 
v_unused_1793_ = lean_ctor_get(v_traceState_1763_, 0);
lean_dec(v_unused_1793_);
v___x_1777_ = v_traceState_1763_;
v_isShared_1778_ = v_isSharedCheck_1792_;
goto v_resetjp_1776_;
}
else
{
lean_dec(v_traceState_1763_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1792_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1782_; 
v___x_1779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1779_, 0, v_ref_1724_);
lean_ctor_set(v___x_1779_, 1, v_a_1758_);
v___x_1780_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1722_, v___x_1779_);
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 0, v___x_1780_);
v___x_1782_ = v___x_1777_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1780_);
lean_ctor_set_uint64(v_reuseFailAlloc_1791_, sizeof(void*)*1, v_tid_1775_);
v___x_1782_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
lean_object* v___x_1784_; 
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 4, v___x_1782_);
v___x_1784_ = v___x_1773_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_env_1764_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v_nextMacroScope_1765_);
lean_ctor_set(v_reuseFailAlloc_1790_, 2, v_ngen_1766_);
lean_ctor_set(v_reuseFailAlloc_1790_, 3, v_auxDeclNGen_1767_);
lean_ctor_set(v_reuseFailAlloc_1790_, 4, v___x_1782_);
lean_ctor_set(v_reuseFailAlloc_1790_, 5, v_cache_1768_);
lean_ctor_set(v_reuseFailAlloc_1790_, 6, v_messages_1769_);
lean_ctor_set(v_reuseFailAlloc_1790_, 7, v_infoState_1770_);
lean_ctor_set(v_reuseFailAlloc_1790_, 8, v_snapshotTasks_1771_);
v___x_1784_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1788_; 
v___x_1785_ = lean_st_ref_set(v___y_1729_, v___x_1784_);
v___x_1786_ = lean_box(0);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v___x_1786_);
v___x_1788_ = v___x_1760_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1786_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2___boxed(lean_object* v_oldTraces_1796_, lean_object* v_data_1797_, lean_object* v_ref_1798_, lean_object* v_msg_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(v_oldTraces_1796_, v_data_1797_, v_ref_1798_, v_msg_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
return v_res_1805_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(lean_object* v_e_1806_){
_start:
{
if (lean_obj_tag(v_e_1806_) == 0)
{
uint8_t v___x_1807_; 
v___x_1807_ = 2;
return v___x_1807_;
}
else
{
uint8_t v___x_1808_; 
v___x_1808_ = 0;
return v___x_1808_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4___boxed(lean_object* v_e_1809_){
_start:
{
uint8_t v_res_1810_; lean_object* v_r_1811_; 
v_res_1810_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(v_e_1809_);
lean_dec_ref(v_e_1809_);
v_r_1811_ = lean_box(v_res_1810_);
return v_r_1811_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1812_; double v___x_1813_; 
v___x_1812_ = lean_unsigned_to_nat(0u);
v___x_1813_ = lean_float_of_nat(v___x_1812_);
return v___x_1813_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__1));
v___x_1816_ = l_Lean_stringToMessageData(v___x_1815_);
return v___x_1816_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1817_; double v___x_1818_; 
v___x_1817_ = lean_unsigned_to_nat(1000u);
v___x_1818_ = lean_float_of_nat(v___x_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(lean_object* v_cls_1819_, uint8_t v_collapsed_1820_, lean_object* v_tag_1821_, lean_object* v_opts_1822_, uint8_t v_clsEnabled_1823_, lean_object* v_oldTraces_1824_, lean_object* v_msg_1825_, lean_object* v_resStartStop_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v_fst_1832_; lean_object* v_snd_1833_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v_data_1837_; lean_object* v_fst_1848_; lean_object* v_snd_1849_; lean_object* v___x_1850_; uint8_t v___x_1851_; lean_object* v___y_1853_; lean_object* v_a_1854_; uint8_t v___y_1869_; double v___y_1900_; 
v_fst_1832_ = lean_ctor_get(v_resStartStop_1826_, 0);
lean_inc(v_fst_1832_);
v_snd_1833_ = lean_ctor_get(v_resStartStop_1826_, 1);
lean_inc(v_snd_1833_);
lean_dec_ref(v_resStartStop_1826_);
v_fst_1848_ = lean_ctor_get(v_snd_1833_, 0);
lean_inc(v_fst_1848_);
v_snd_1849_ = lean_ctor_get(v_snd_1833_, 1);
lean_inc(v_snd_1849_);
lean_dec(v_snd_1833_);
v___x_1850_ = l_Lean_trace_profiler;
v___x_1851_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_1822_, v___x_1850_);
if (v___x_1851_ == 0)
{
v___y_1869_ = v___x_1851_;
goto v___jp_1868_;
}
else
{
lean_object* v___x_1905_; uint8_t v___x_1906_; 
v___x_1905_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1906_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_1822_, v___x_1905_);
if (v___x_1906_ == 0)
{
lean_object* v___x_1907_; lean_object* v___x_1908_; double v___x_1909_; double v___x_1910_; double v___x_1911_; 
v___x_1907_ = l_Lean_trace_profiler_threshold;
v___x_1908_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_1822_, v___x_1907_);
v___x_1909_ = lean_float_of_nat(v___x_1908_);
v___x_1910_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3);
v___x_1911_ = lean_float_div(v___x_1909_, v___x_1910_);
v___y_1900_ = v___x_1911_;
goto v___jp_1899_;
}
else
{
lean_object* v___x_1912_; lean_object* v___x_1913_; double v___x_1914_; 
v___x_1912_ = l_Lean_trace_profiler_threshold;
v___x_1913_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_1822_, v___x_1912_);
v___x_1914_ = lean_float_of_nat(v___x_1913_);
v___y_1900_ = v___x_1914_;
goto v___jp_1899_;
}
}
v___jp_1834_:
{
lean_object* v___x_1838_; 
lean_inc(v___y_1836_);
v___x_1838_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(v_oldTraces_1824_, v_data_1837_, v___y_1836_, v___y_1835_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v___x_1839_; 
lean_dec_ref_known(v___x_1838_, 1);
v___x_1839_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_1832_);
return v___x_1839_;
}
else
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
lean_dec(v_fst_1832_);
v_a_1840_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1842_ = v___x_1838_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1838_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1840_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
v___jp_1852_:
{
uint8_t v_result_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; double v___x_1858_; lean_object* v_data_1859_; 
v_result_1855_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(v_fst_1832_);
v___x_1856_ = lean_box(v_result_1855_);
v___x_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
v___x_1858_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0);
lean_inc_ref(v_tag_1821_);
lean_inc_ref(v___x_1857_);
lean_inc(v_cls_1819_);
v_data_1859_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1859_, 0, v_cls_1819_);
lean_ctor_set(v_data_1859_, 1, v___x_1857_);
lean_ctor_set(v_data_1859_, 2, v_tag_1821_);
lean_ctor_set_float(v_data_1859_, sizeof(void*)*3, v___x_1858_);
lean_ctor_set_float(v_data_1859_, sizeof(void*)*3 + 8, v___x_1858_);
lean_ctor_set_uint8(v_data_1859_, sizeof(void*)*3 + 16, v_collapsed_1820_);
if (v___x_1851_ == 0)
{
lean_dec_ref_known(v___x_1857_, 1);
lean_dec(v_snd_1849_);
lean_dec(v_fst_1848_);
lean_dec_ref(v_tag_1821_);
lean_dec(v_cls_1819_);
v___y_1835_ = v_a_1854_;
v___y_1836_ = v___y_1853_;
v_data_1837_ = v_data_1859_;
goto v___jp_1834_;
}
else
{
lean_object* v_data_1860_; double v___x_1861_; double v___x_1862_; 
lean_dec_ref_known(v_data_1859_, 3);
v_data_1860_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1860_, 0, v_cls_1819_);
lean_ctor_set(v_data_1860_, 1, v___x_1857_);
lean_ctor_set(v_data_1860_, 2, v_tag_1821_);
v___x_1861_ = lean_unbox_float(v_fst_1848_);
lean_dec(v_fst_1848_);
lean_ctor_set_float(v_data_1860_, sizeof(void*)*3, v___x_1861_);
v___x_1862_ = lean_unbox_float(v_snd_1849_);
lean_dec(v_snd_1849_);
lean_ctor_set_float(v_data_1860_, sizeof(void*)*3 + 8, v___x_1862_);
lean_ctor_set_uint8(v_data_1860_, sizeof(void*)*3 + 16, v_collapsed_1820_);
v___y_1835_ = v_a_1854_;
v___y_1836_ = v___y_1853_;
v_data_1837_ = v_data_1860_;
goto v___jp_1834_;
}
}
v___jp_1863_:
{
lean_object* v_ref_1864_; lean_object* v___x_1865_; 
v_ref_1864_ = lean_ctor_get(v___y_1829_, 5);
lean_inc(v___y_1830_);
lean_inc_ref(v___y_1829_);
lean_inc(v___y_1828_);
lean_inc_ref(v___y_1827_);
lean_inc(v_fst_1832_);
v___x_1865_ = lean_apply_6(v_msg_1825_, v_fst_1832_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, lean_box(0));
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_a_1866_);
lean_dec_ref_known(v___x_1865_, 1);
v___y_1853_ = v_ref_1864_;
v_a_1854_ = v_a_1866_;
goto v___jp_1852_;
}
else
{
lean_object* v___x_1867_; 
lean_dec_ref_known(v___x_1865_, 1);
v___x_1867_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2);
v___y_1853_ = v_ref_1864_;
v_a_1854_ = v___x_1867_;
goto v___jp_1852_;
}
}
v___jp_1868_:
{
if (v_clsEnabled_1823_ == 0)
{
if (v___y_1869_ == 0)
{
lean_object* v___x_1870_; lean_object* v_traceState_1871_; lean_object* v_env_1872_; lean_object* v_nextMacroScope_1873_; lean_object* v_ngen_1874_; lean_object* v_auxDeclNGen_1875_; lean_object* v_cache_1876_; lean_object* v_messages_1877_; lean_object* v_infoState_1878_; lean_object* v_snapshotTasks_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1898_; 
lean_dec(v_snd_1849_);
lean_dec(v_fst_1848_);
lean_dec_ref(v_msg_1825_);
lean_dec_ref(v_tag_1821_);
lean_dec(v_cls_1819_);
v___x_1870_ = lean_st_ref_take(v___y_1830_);
v_traceState_1871_ = lean_ctor_get(v___x_1870_, 4);
v_env_1872_ = lean_ctor_get(v___x_1870_, 0);
v_nextMacroScope_1873_ = lean_ctor_get(v___x_1870_, 1);
v_ngen_1874_ = lean_ctor_get(v___x_1870_, 2);
v_auxDeclNGen_1875_ = lean_ctor_get(v___x_1870_, 3);
v_cache_1876_ = lean_ctor_get(v___x_1870_, 5);
v_messages_1877_ = lean_ctor_get(v___x_1870_, 6);
v_infoState_1878_ = lean_ctor_get(v___x_1870_, 7);
v_snapshotTasks_1879_ = lean_ctor_get(v___x_1870_, 8);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1881_ = v___x_1870_;
v_isShared_1882_ = v_isSharedCheck_1898_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_snapshotTasks_1879_);
lean_inc(v_infoState_1878_);
lean_inc(v_messages_1877_);
lean_inc(v_cache_1876_);
lean_inc(v_traceState_1871_);
lean_inc(v_auxDeclNGen_1875_);
lean_inc(v_ngen_1874_);
lean_inc(v_nextMacroScope_1873_);
lean_inc(v_env_1872_);
lean_dec(v___x_1870_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1898_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
uint64_t v_tid_1883_; lean_object* v_traces_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1897_; 
v_tid_1883_ = lean_ctor_get_uint64(v_traceState_1871_, sizeof(void*)*1);
v_traces_1884_ = lean_ctor_get(v_traceState_1871_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v_traceState_1871_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1886_ = v_traceState_1871_;
v_isShared_1887_ = v_isSharedCheck_1897_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_traces_1884_);
lean_dec(v_traceState_1871_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1897_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1888_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1824_, v_traces_1884_);
lean_dec_ref(v_traces_1884_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 0, v___x_1888_);
v___x_1890_ = v___x_1886_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1888_);
lean_ctor_set_uint64(v_reuseFailAlloc_1896_, sizeof(void*)*1, v_tid_1883_);
v___x_1890_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1892_; 
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 4, v___x_1890_);
v___x_1892_ = v___x_1881_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_env_1872_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v_nextMacroScope_1873_);
lean_ctor_set(v_reuseFailAlloc_1895_, 2, v_ngen_1874_);
lean_ctor_set(v_reuseFailAlloc_1895_, 3, v_auxDeclNGen_1875_);
lean_ctor_set(v_reuseFailAlloc_1895_, 4, v___x_1890_);
lean_ctor_set(v_reuseFailAlloc_1895_, 5, v_cache_1876_);
lean_ctor_set(v_reuseFailAlloc_1895_, 6, v_messages_1877_);
lean_ctor_set(v_reuseFailAlloc_1895_, 7, v_infoState_1878_);
lean_ctor_set(v_reuseFailAlloc_1895_, 8, v_snapshotTasks_1879_);
v___x_1892_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = lean_st_ref_set(v___y_1830_, v___x_1892_);
v___x_1894_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_1832_);
return v___x_1894_;
}
}
}
}
}
else
{
goto v___jp_1863_;
}
}
else
{
goto v___jp_1863_;
}
}
v___jp_1899_:
{
double v___x_1901_; double v___x_1902_; double v___x_1903_; uint8_t v___x_1904_; 
v___x_1901_ = lean_unbox_float(v_snd_1849_);
v___x_1902_ = lean_unbox_float(v_fst_1848_);
v___x_1903_ = lean_float_sub(v___x_1901_, v___x_1902_);
v___x_1904_ = lean_float_decLt(v___y_1900_, v___x_1903_);
v___y_1869_ = v___x_1904_;
goto v___jp_1868_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___boxed(lean_object* v_cls_1915_, lean_object* v_collapsed_1916_, lean_object* v_tag_1917_, lean_object* v_opts_1918_, lean_object* v_clsEnabled_1919_, lean_object* v_oldTraces_1920_, lean_object* v_msg_1921_, lean_object* v_resStartStop_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
uint8_t v_collapsed_boxed_1928_; uint8_t v_clsEnabled_boxed_1929_; lean_object* v_res_1930_; 
v_collapsed_boxed_1928_ = lean_unbox(v_collapsed_1916_);
v_clsEnabled_boxed_1929_ = lean_unbox(v_clsEnabled_1919_);
v_res_1930_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v_cls_1915_, v_collapsed_boxed_1928_, v_tag_1917_, v_opts_1918_, v_clsEnabled_boxed_1929_, v_oldTraces_1920_, v_msg_1921_, v_resStartStop_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
lean_dec_ref(v_opts_1918_);
return v_res_1930_;
}
}
static double _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__0(void){
_start:
{
lean_object* v___x_1931_; double v___x_1932_; 
v___x_1931_ = lean_unsigned_to_nat(1000000000u);
v___x_1932_ = lean_float_of_nat(v___x_1931_);
return v___x_1932_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3(void){
_start:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1936_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_1937_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2));
v___x_1938_ = l_Lean_Name_append(v___x_1937_, v___x_1936_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(lean_object* v_cfg_1939_, lean_object* v_act_1940_, lean_object* v_allowFailure_1941_, lean_object* v_cand_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_){
_start:
{
lean_object* v_fst_1948_; lean_object* v_snd_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_2248_; 
v_fst_1948_ = lean_ctor_get(v_cand_1942_, 0);
v_snd_1949_ = lean_ctor_get(v_cand_1942_, 1);
v_isSharedCheck_2248_ = !lean_is_exclusive(v_cand_1942_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_1951_ = v_cand_1942_;
v_isShared_1952_ = v_isSharedCheck_2248_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_snd_1949_);
lean_inc(v_fst_1948_);
lean_dec(v_cand_1942_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_2248_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v_fst_1953_; lean_object* v_snd_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_2247_; 
v_fst_1953_ = lean_ctor_get(v_fst_1948_, 0);
v_snd_1954_ = lean_ctor_get(v_fst_1948_, 1);
v_isSharedCheck_2247_ = !lean_is_exclusive(v_fst_1948_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_1956_ = v_fst_1948_;
v_isShared_1957_ = v_isSharedCheck_2247_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_snd_1954_);
lean_inc(v_fst_1953_);
lean_dec(v_fst_1948_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_2247_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___y_1959_; lean_object* v___y_1960_; uint8_t v___y_1961_; lean_object* v_options_1982_; lean_object* v_fst_1983_; lean_object* v_snd_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_2246_; 
v_options_1982_ = lean_ctor_get(v_a_1945_, 2);
v_fst_1983_ = lean_ctor_get(v_snd_1949_, 0);
v_snd_1984_ = lean_ctor_get(v_snd_1949_, 1);
v_isSharedCheck_2246_ = !lean_is_exclusive(v_snd_1949_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_1986_ = v_snd_1949_;
v_isShared_1987_ = v_isSharedCheck_2246_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_snd_1984_);
lean_inc(v_fst_1983_);
lean_dec(v_snd_1949_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_2246_;
goto v_resetjp_1985_;
}
v___jp_1958_:
{
if (v___y_1961_ == 0)
{
lean_object* v___x_1962_; 
lean_dec_ref(v___y_1959_);
lean_inc(v_a_1946_);
lean_inc_ref(v_a_1945_);
lean_inc(v_a_1944_);
lean_inc_ref(v_a_1943_);
v___x_1962_ = lean_apply_6(v_allowFailure_1941_, v_fst_1953_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, lean_box(0));
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1973_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1965_ = v___x_1962_;
v_isShared_1966_ = v_isSharedCheck_1973_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1962_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1973_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
uint8_t v___x_1967_; 
v___x_1967_ = lean_unbox(v_a_1963_);
lean_dec(v_a_1963_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
lean_del_object(v___x_1965_);
lean_dec(v___y_1960_);
v___x_1968_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1);
v___x_1969_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_1968_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_);
return v___x_1969_;
}
else
{
lean_object* v___x_1971_; 
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 0, v___y_1960_);
v___x_1971_ = v___x_1965_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___y_1960_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
else
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
lean_dec(v___y_1960_);
v_a_1974_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___x_1962_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1962_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1974_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
else
{
lean_dec(v___y_1960_);
lean_dec(v_fst_1953_);
lean_dec_ref(v_allowFailure_1941_);
return v___y_1959_;
}
}
v_resetjp_1985_:
{
lean_object* v_inheritedTraceOptions_1988_; uint8_t v_hasTrace_1989_; uint8_t v___x_1990_; 
v_inheritedTraceOptions_1988_ = lean_ctor_get(v_a_1945_, 13);
v_hasTrace_1989_ = lean_ctor_get_uint8(v_options_1982_, sizeof(void*)*1);
v___x_1990_ = lean_bool_not(v_hasTrace_1989_);
if (v___x_1990_ == 0)
{
lean_object* v___f_1991_; lean_object* v___x_1992_; uint8_t v___x_1993_; lean_object* v___x_1994_; lean_object* v___y_1996_; lean_object* v___y_1997_; uint8_t v___y_1998_; lean_object* v_a_1999_; lean_object* v___y_2016_; lean_object* v___y_2017_; uint8_t v___y_2018_; lean_object* v_a_2019_; lean_object* v___y_2022_; lean_object* v___y_2023_; uint8_t v___y_2024_; lean_object* v_a_2025_; lean_object* v___y_2028_; lean_object* v___y_2029_; uint8_t v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; uint8_t v___y_2039_; uint8_t v___y_2040_; lean_object* v___y_2048_; uint8_t v___y_2049_; lean_object* v___y_2050_; lean_object* v_a_2051_; lean_object* v___y_2063_; uint8_t v___y_2064_; lean_object* v___y_2065_; lean_object* v_a_2066_; lean_object* v___y_2069_; uint8_t v___y_2070_; lean_object* v___y_2071_; lean_object* v_a_2072_; lean_object* v___y_2075_; uint8_t v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2082_; uint8_t v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; uint8_t v___y_2087_; uint8_t v___y_2095_; uint8_t v_a_2155_; 
lean_inc(v_snd_1984_);
lean_inc(v_fst_1983_);
v___f_1991_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1991_, 0, v_fst_1983_);
lean_closure_set(v___f_1991_, 1, v_snd_1984_);
v___x_1992_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_1993_ = 1;
v___x_1994_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__4));
if (v_hasTrace_1989_ == 0)
{
v_a_2155_ = v_hasTrace_1989_;
goto v___jp_2154_;
}
else
{
lean_object* v___x_2190_; uint8_t v___x_2191_; 
v___x_2190_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3);
v___x_2191_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1988_, v_options_1982_, v___x_2190_);
if (v___x_2191_ == 0)
{
v_a_2155_ = v___x_2191_;
goto v___jp_2154_;
}
else
{
v___y_2095_ = v___x_2191_;
goto v___jp_2094_;
}
}
v___jp_1995_:
{
lean_object* v___x_2000_; double v___x_2001_; double v___x_2002_; double v___x_2003_; double v___x_2004_; double v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2009_; 
v___x_2000_ = lean_io_mono_nanos_now();
v___x_2001_ = lean_float_of_nat(v___y_1996_);
v___x_2002_ = lean_float_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__0, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__0_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__0);
v___x_2003_ = lean_float_div(v___x_2001_, v___x_2002_);
v___x_2004_ = lean_float_of_nat(v___x_2000_);
v___x_2005_ = lean_float_div(v___x_2004_, v___x_2002_);
v___x_2006_ = lean_box_float(v___x_2003_);
v___x_2007_ = lean_box_float(v___x_2005_);
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 1, v___x_2007_);
lean_ctor_set(v___x_1986_, 0, v___x_2006_);
v___x_2009_ = v___x_1986_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2006_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v___x_2007_);
v___x_2009_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
lean_object* v___x_2011_; 
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 1, v___x_2009_);
lean_ctor_set(v___x_1956_, 0, v_a_1999_);
v___x_2011_ = v___x_1956_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_1999_);
lean_ctor_set(v_reuseFailAlloc_2013_, 1, v___x_2009_);
v___x_2011_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
lean_object* v___x_2012_; 
v___x_2012_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v___x_1992_, v___x_1993_, v___x_1994_, v_options_1982_, v___y_1998_, v___y_1997_, v___f_1991_, v___x_2011_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_);
return v___x_2012_;
}
}
}
v___jp_2015_:
{
lean_object* v___x_2020_; 
v___x_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2020_, 0, v_a_2019_);
v___y_1996_ = v___y_2016_;
v___y_1997_ = v___y_2017_;
v___y_1998_ = v___y_2018_;
v_a_1999_ = v___x_2020_;
goto v___jp_1995_;
}
v___jp_2021_:
{
lean_object* v___x_2026_; 
v___x_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2026_, 0, v_a_2025_);
v___y_1996_ = v___y_2022_;
v___y_1997_ = v___y_2023_;
v___y_1998_ = v___y_2024_;
v_a_1999_ = v___x_2026_;
goto v___jp_1995_;
}
v___jp_2027_:
{
if (lean_obj_tag(v___y_2031_) == 0)
{
lean_object* v_a_2032_; 
v_a_2032_ = lean_ctor_get(v___y_2031_, 0);
lean_inc(v_a_2032_);
lean_dec_ref_known(v___y_2031_, 1);
v___y_2022_ = v___y_2028_;
v___y_2023_ = v___y_2029_;
v___y_2024_ = v___y_2030_;
v_a_2025_ = v_a_2032_;
goto v___jp_2021_;
}
else
{
lean_object* v_a_2033_; 
v_a_2033_ = lean_ctor_get(v___y_2031_, 0);
lean_inc(v_a_2033_);
lean_dec_ref_known(v___y_2031_, 1);
v___y_2016_ = v___y_2028_;
v___y_2017_ = v___y_2029_;
v___y_2018_ = v___y_2030_;
v_a_2019_ = v_a_2033_;
goto v___jp_2015_;
}
}
v___jp_2034_:
{
if (v___y_2040_ == 0)
{
lean_object* v___x_2041_; 
lean_dec_ref(v___y_2035_);
lean_inc(v_a_1946_);
lean_inc_ref(v_a_1945_);
lean_inc(v_a_1944_);
lean_inc_ref(v_a_1943_);
v___x_2041_ = lean_apply_6(v_allowFailure_1941_, v_fst_1953_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, lean_box(0));
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; uint8_t v___x_2043_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2042_);
lean_dec_ref_known(v___x_2041_, 1);
v___x_2043_ = lean_unbox(v_a_2042_);
lean_dec(v_a_2042_);
if (v___x_2043_ == 0)
{
lean_object* v___x_2044_; lean_object* v___x_2045_; 
lean_dec(v___y_2036_);
v___x_2044_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1);
v___x_2045_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2044_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_);
v___y_2028_ = v___y_2037_;
v___y_2029_ = v___y_2038_;
v___y_2030_ = v___y_2039_;
v___y_2031_ = v___x_2045_;
goto v___jp_2027_;
}
else
{
v___y_2022_ = v___y_2037_;
v___y_2023_ = v___y_2038_;
v___y_2024_ = v___y_2039_;
v_a_2025_ = v___y_2036_;
goto v___jp_2021_;
}
}
else
{
lean_object* v_a_2046_; 
lean_dec(v___y_2036_);
v_a_2046_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2046_);
lean_dec_ref_known(v___x_2041_, 1);
v___y_2016_ = v___y_2037_;
v___y_2017_ = v___y_2038_;
v___y_2018_ = v___y_2039_;
v_a_2019_ = v_a_2046_;
goto v___jp_2015_;
}
}
else
{
lean_dec(v___y_2036_);
lean_dec(v_fst_1953_);
lean_dec_ref(v_allowFailure_1941_);
v___y_2016_ = v___y_2037_;
v___y_2017_ = v___y_2038_;
v___y_2018_ = v___y_2039_;
v_a_2019_ = v___y_2035_;
goto v___jp_2015_;
}
}
v___jp_2047_:
{
lean_object* v___x_2052_; double v___x_2053_; double v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2058_; 
v___x_2052_ = lean_io_get_num_heartbeats();
v___x_2053_ = lean_float_of_nat(v___y_2050_);
v___x_2054_ = lean_float_of_nat(v___x_2052_);
v___x_2055_ = lean_box_float(v___x_2053_);
v___x_2056_ = lean_box_float(v___x_2054_);
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 1, v___x_2056_);
lean_ctor_set(v___x_1951_, 0, v___x_2055_);
v___x_2058_ = v___x_1951_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2055_);
lean_ctor_set(v_reuseFailAlloc_2061_, 1, v___x_2056_);
v___x_2058_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2059_, 0, v_a_2051_);
lean_ctor_set(v___x_2059_, 1, v___x_2058_);
v___x_2060_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v___x_1992_, v___x_1993_, v___x_1994_, v_options_1982_, v___y_2049_, v___y_2048_, v___f_1991_, v___x_2059_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_);
return v___x_2060_;
}
}
v___jp_2062_:
{
lean_object* v___x_2067_; 
v___x_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2067_, 0, v_a_2066_);
v___y_2048_ = v___y_2063_;
v___y_2049_ = v___y_2064_;
v___y_2050_ = v___y_2065_;
v_a_2051_ = v___x_2067_;
goto v___jp_2047_;
}
v___jp_2068_:
{
lean_object* v___x_2073_; 
v___x_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2073_, 0, v_a_2072_);
v___y_2048_ = v___y_2069_;
v___y_2049_ = v___y_2070_;
v___y_2050_ = v___y_2071_;
v_a_2051_ = v___x_2073_;
goto v___jp_2047_;
}
v___jp_2074_:
{
if (lean_obj_tag(v___y_2078_) == 0)
{
lean_object* v_a_2079_; 
v_a_2079_ = lean_ctor_get(v___y_2078_, 0);
lean_inc(v_a_2079_);
lean_dec_ref_known(v___y_2078_, 1);
v___y_2069_ = v___y_2075_;
v___y_2070_ = v___y_2076_;
v___y_2071_ = v___y_2077_;
v_a_2072_ = v_a_2079_;
goto v___jp_2068_;
}
else
{
lean_object* v_a_2080_; 
v_a_2080_ = lean_ctor_get(v___y_2078_, 0);
lean_inc(v_a_2080_);
lean_dec_ref_known(v___y_2078_, 1);
v___y_2063_ = v___y_2075_;
v___y_2064_ = v___y_2076_;
v___y_2065_ = v___y_2077_;
v_a_2066_ = v_a_2080_;
goto v___jp_2062_;
}
}
v___jp_2081_:
{
if (v___y_2087_ == 0)
{
lean_object* v___x_2088_; 
lean_dec_ref(v___y_2086_);
lean_inc(v_a_1946_);
lean_inc_ref(v_a_1945_);
lean_inc(v_a_1944_);
lean_inc_ref(v_a_1943_);
v___x_2088_ = lean_apply_6(v_allowFailure_1941_, v_fst_1953_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, lean_box(0));
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; uint8_t v___x_2090_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_a_2089_);
lean_dec_ref_known(v___x_2088_, 1);
v___x_2090_ = lean_unbox(v_a_2089_);
lean_dec(v_a_2089_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
lean_dec(v___y_2084_);
v___x_2091_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1);
v___x_2092_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2091_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_);
v___y_2075_ = v___y_2082_;
v___y_2076_ = v___y_2083_;
v___y_2077_ = v___y_2085_;
v___y_2078_ = v___x_2092_;
goto v___jp_2074_;
}
else
{
v___y_2069_ = v___y_2082_;
v___y_2070_ = v___y_2083_;
v___y_2071_ = v___y_2085_;
v_a_2072_ = v___y_2084_;
goto v___jp_2068_;
}
}
else
{
lean_object* v_a_2093_; 
lean_dec(v___y_2084_);
v_a_2093_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_a_2093_);
lean_dec_ref_known(v___x_2088_, 1);
v___y_2063_ = v___y_2082_;
v___y_2064_ = v___y_2083_;
v___y_2065_ = v___y_2085_;
v_a_2066_ = v_a_2093_;
goto v___jp_2062_;
}
}
else
{
lean_dec(v___y_2084_);
lean_dec(v_fst_1953_);
lean_dec_ref(v_allowFailure_1941_);
v___y_2063_ = v___y_2082_;
v___y_2064_ = v___y_2083_;
v___y_2065_ = v___y_2085_;
v_a_2066_ = v___y_2086_;
goto v___jp_2062_;
}
}
v___jp_2094_:
{
lean_object* v___x_2096_; lean_object* v_a_2097_; lean_object* v___x_2098_; uint8_t v___x_2099_; 
v___x_2096_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v_a_1946_);
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2097_);
lean_dec_ref(v___x_2096_);
v___x_2098_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2099_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_1982_, v___x_2098_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v_cache_2102_; lean_object* v_zetaDeltaFVarIds_2103_; lean_object* v_postponed_2104_; lean_object* v_diag_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2125_; 
lean_del_object(v___x_1951_);
v___x_2100_ = lean_io_mono_nanos_now();
v___x_2101_ = lean_st_ref_take(v_a_1944_);
v_cache_2102_ = lean_ctor_get(v___x_2101_, 1);
v_zetaDeltaFVarIds_2103_ = lean_ctor_get(v___x_2101_, 2);
v_postponed_2104_ = lean_ctor_get(v___x_2101_, 3);
v_diag_2105_ = lean_ctor_get(v___x_2101_, 4);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2125_ == 0)
{
lean_object* v_unused_2126_; 
v_unused_2126_ = lean_ctor_get(v___x_2101_, 0);
lean_dec(v_unused_2126_);
v___x_2107_ = v___x_2101_;
v_isShared_2108_ = v_isSharedCheck_2125_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_diag_2105_);
lean_inc(v_postponed_2104_);
lean_inc(v_zetaDeltaFVarIds_2103_);
lean_inc(v_cache_2102_);
lean_dec(v___x_2101_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2125_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
lean_ctor_set(v___x_2107_, 0, v_snd_1954_);
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_snd_1954_);
lean_ctor_set(v_reuseFailAlloc_2124_, 1, v_cache_2102_);
lean_ctor_set(v_reuseFailAlloc_2124_, 2, v_zetaDeltaFVarIds_2103_);
lean_ctor_set(v_reuseFailAlloc_2124_, 3, v_postponed_2104_);
lean_ctor_set(v_reuseFailAlloc_2124_, 4, v_diag_2105_);
v___x_2110_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
lean_object* v___x_2111_; uint8_t v___x_2112_; lean_object* v___x_2113_; 
v___x_2111_ = lean_st_ref_set(v_a_1944_, v___x_2110_);
v___x_2112_ = lean_unbox(v_snd_1984_);
lean_dec(v_snd_1984_);
v___x_2113_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_1983_, v___x_2112_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_a_2114_);
lean_dec_ref_known(v___x_2113_, 1);
v___x_2115_ = lean_box(0);
lean_inc(v_fst_1953_);
v___x_2116_ = l_Lean_MVarId_apply(v_fst_1953_, v_a_2114_, v_cfg_1939_, v___x_2115_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v___x_2118_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc_n(v_a_2117_, 2);
lean_dec_ref_known(v___x_2116_, 1);
lean_inc(v_a_1946_);
lean_inc_ref(v_a_1945_);
lean_inc(v_a_1944_);
lean_inc_ref(v_a_1943_);
v___x_2118_ = lean_apply_6(v_act_1940_, v_a_2117_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, lean_box(0));
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; 
lean_dec(v_a_2117_);
lean_dec(v_fst_1953_);
lean_dec_ref(v_allowFailure_1941_);
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2119_);
lean_dec_ref_known(v___x_2118_, 1);
v___y_2022_ = v___x_2100_;
v___y_2023_ = v_a_2097_;
v___y_2024_ = v___y_2095_;
v_a_2025_ = v_a_2119_;
goto v___jp_2021_;
}
else
{
lean_object* v_a_2120_; uint8_t v___x_2121_; 
v_a_2120_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2120_);
lean_dec_ref_known(v___x_2118_, 1);
v___x_2121_ = l_Lean_Exception_isInterrupt(v_a_2120_);
if (v___x_2121_ == 0)
{
uint8_t v___x_2122_; 
lean_inc(v_a_2120_);
v___x_2122_ = l_Lean_Exception_isRuntime(v_a_2120_);
v___y_2035_ = v_a_2120_;
v___y_2036_ = v_a_2117_;
v___y_2037_ = v___x_2100_;
v___y_2038_ = v_a_2097_;
v___y_2039_ = v___y_2095_;
v___y_2040_ = v___x_2122_;
goto v___jp_2034_;
}
else
{
v___y_2035_ = v_a_2120_;
v___y_2036_ = v_a_2117_;
v___y_2037_ = v___x_2100_;
v___y_2038_ = v_a_2097_;
v___y_2039_ = v___y_2095_;
v___y_2040_ = v___x_2121_;
goto v___jp_2034_;
}
}
}
else
{
lean_dec(v_fst_1953_);
lean_dec_ref(v_allowFailure_1941_);
lean_dec_ref(v_act_1940_);
v___y_2028_ = v___x_2100_;
v___y_2029_ = v_a_2097_;
v___y_2030_ = v___y_2095_;
v___y_2031_ = v___x_2116_;
goto v___jp_2027_;
}
}
else
{
lean_object* v_a_2123_; 
lean_dec(v_fst_1953_);
lean_dec_ref(v_allowFailure_1941_);
lean_dec_ref(v_act_1940_);
lean_dec_ref(v_cfg_1939_);
v_a_2123_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v___x_2113_, 1);
v___y_2016_ = v___x_2100_;
v___y_2017_ = v_a_2097_;
v___y_2018_ = v___y_2095_;
v_a_2019_ = v_a_2123_;
goto v___jp_2015_;
}
}
}
}
else
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v_cache_2129_; lean_object* v_zetaDeltaFVarIds_2130_; lean_object* v_postponed_2131_; lean_object* v_diag_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2152_; 
lean_del_object(v___x_1986_);
lean_del_object(v___x_1956_);
v___x_2127_ = lean_io_get_num_heartbeats();
v___x_2128_ = lean_st_ref_take(v_a_1944_);
v_cache_2129_ = lean_ctor_get(v___x_2128_, 1);
v_zetaDeltaFVarIds_2130_ = lean_ctor_get(v___x_2128_, 2);
v_postponed_2131_ = lean_ctor_get(v___x_2128_, 3);
v_diag_2132_ = lean_ctor_get(v___x_2128_, 4);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2152_ == 0)
{
lean_object* v_unused_2153_; 
v_unused_2153_ = lean_ctor_get(v___x_2128_, 0);
lean_dec(v_unused_2153_);
v___x_2134_ = v___x_2128_;
v_isShared_2135_ = v_isSharedCheck_2152_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_diag_2132_);
lean_inc(v_postponed_2131_);
lean_inc(v_zetaDeltaFVarIds_2130_);
lean_inc(v_cache_2129_);
lean_dec(v___x_2128_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2152_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
if (v_isShared_2135_ == 0)
{
lean_ctor_set(v___x_2134_, 0, v_snd_1954_);
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_snd_1954_);
lean_ctor_set(v_reuseFailAlloc_2151_, 1, v_cache_2129_);
lean_ctor_set(v_reuseFailAlloc_2151_, 2, v_zetaDeltaFVarIds_2130_);
lean_ctor_set(v_reuseFailAlloc_2151_, 3, v_postponed_2131_);
lean_ctor_set(v_reuseFailAlloc_2151_, 4, v_diag_2132_);
v___x_2137_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
lean_object* v___x_2138_; uint8_t v___x_2139_; lean_object* v___x_2140_; 
v___x_2138_ = lean_st_ref_set(v_a_1944_, v___x_2137_);
v___x_2139_ = lean_unbox(v_snd_1984_);
lean_dec(v_snd_1984_);
v___x_2140_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_1983_, v___x_2139_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_a_2141_);
lean_dec_ref_known(v___x_2140_, 1);
v___x_2142_ = lean_box(0);
lean_inc(v_fst_1953_);
v___x_2143_ = l_Lean_MVarId_apply(v_fst_1953_, v_a_2141_, v_cfg_1939_, v___x_2142_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; lean_object* v___x_2145_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc_n(v_a_2144_, 2);
lean_dec_ref_known(v___x_2143_, 1);
lean_inc(v_a_1946_);
lean_inc_ref(v_a_1945_);
lean_inc(v_a_1944_);
lean_inc_ref(v_a_1943_);
v___x_2145_ = lean_apply_6(v_act_1940_, v_a_2144_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, lean_box(0));
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v_a_2146_; 
lean_dec(v_a_2144_);
lean_dec(v_fst_1953_);
lean_dec_ref(v_allowFailure_1941_);
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
lean_inc(v_a_2146_);
lean_dec_ref_known(v___x_2145_, 1);
v___y_2069_ = v_a_2097_;
v___y_2070_ = v___y_2095_;
v___y_2071_ = v___x_2127_;
v_a_2072_ = v_a_2146_;
goto v___jp_2068_;
}
else
{
lean_object* v_a_2147_; uint8_t v___x_2148_; 
v_a_2147_ = lean_ctor_get(v___x_2145_, 0);
lean_inc(v_a_2147_);
lean_dec_ref_known(v___x_2145_, 1);
v___x_2148_ = l_Lean_Exception_isInterrupt(v_a_2147_);
if (v___x_2148_ == 0)
{
uint8_t v___x_2149_; 
lean_inc(v_a_2147_);
v___x_2149_ = l_Lean_Exception_isRuntime(v_a_2147_);
v___y_2082_ = v_a_2097_;
v___y_2083_ = v___y_2095_;
v___y_2084_ = v_a_2144_;
v___y_2085_ = v___x_2127_;
v___y_2086_ = v_a_2147_;
v___y_2087_ = v___x_2149_;
goto v___jp_2081_;
}
else
{
v___y_2082_ = v_a_2097_;
v___y_2083_ = v___y_2095_;
v___y_2084_ = v_a_2144_;
v___y_2085_ = v___x_2127_;
v___y_2086_ = v_a_2147_;
v___y_2087_ = v___x_2148_;
goto v___jp_2081_;
}
}
}
else
{
lean_dec(v_fst_1953_);
lean_dec_ref(v_allowFailure_1941_);
lean_dec_ref(v_act_1940_);
v___y_2075_ = v_a_2097_;
v___y_2076_ = v___y_2095_;
v___y_2077_ = v___x_2127_;
v___y_2078_ = v___x_2143_;
goto v___jp_2074_;
}
}
else
{
lean_object* v_a_2150_; 
lean_dec(v_fst_1953_);
lean_dec_ref(v_allowFailure_1941_);
lean_dec_ref(v_act_1940_);
lean_dec_ref(v_cfg_1939_);
v_a_2150_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_a_2150_);
lean_dec_ref_known(v___x_2140_, 1);
v___y_2063_ = v_a_2097_;
v___y_2064_ = v___y_2095_;
v___y_2065_ = v___x_2127_;
v_a_2066_ = v_a_2150_;
goto v___jp_2062_;
}
}
}
}
}
v___jp_2154_:
{
lean_object* v___x_2156_; uint8_t v___x_2157_; 
v___x_2156_ = l_Lean_trace_profiler;
v___x_2157_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_1982_, v___x_2156_);
if (v___x_2157_ == 0)
{
lean_object* v___x_2158_; lean_object* v_cache_2159_; lean_object* v_zetaDeltaFVarIds_2160_; lean_object* v_postponed_2161_; lean_object* v_diag_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2188_; 
lean_dec_ref(v___f_1991_);
lean_del_object(v___x_1986_);
lean_del_object(v___x_1956_);
lean_del_object(v___x_1951_);
v___x_2158_ = lean_st_ref_take(v_a_1944_);
v_cache_2159_ = lean_ctor_get(v___x_2158_, 1);
v_zetaDeltaFVarIds_2160_ = lean_ctor_get(v___x_2158_, 2);
v_postponed_2161_ = lean_ctor_get(v___x_2158_, 3);
v_diag_2162_ = lean_ctor_get(v___x_2158_, 4);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2188_ == 0)
{
lean_object* v_unused_2189_; 
v_unused_2189_ = lean_ctor_get(v___x_2158_, 0);
lean_dec(v_unused_2189_);
v___x_2164_ = v___x_2158_;
v_isShared_2165_ = v_isSharedCheck_2188_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_diag_2162_);
lean_inc(v_postponed_2161_);
lean_inc(v_zetaDeltaFVarIds_2160_);
lean_inc(v_cache_2159_);
lean_dec(v___x_2158_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2188_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 0, v_snd_1954_);
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_snd_1954_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_cache_2159_);
lean_ctor_set(v_reuseFailAlloc_2187_, 2, v_zetaDeltaFVarIds_2160_);
lean_ctor_set(v_reuseFailAlloc_2187_, 3, v_postponed_2161_);
lean_ctor_set(v_reuseFailAlloc_2187_, 4, v_diag_2162_);
v___x_2167_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
lean_object* v___x_2168_; uint8_t v___x_2169_; lean_object* v___x_2170_; 
v___x_2168_ = lean_st_ref_set(v_a_1944_, v___x_2167_);
v___x_2169_ = lean_unbox(v_snd_1984_);
lean_dec(v_snd_1984_);
v___x_2170_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_1983_, v___x_2169_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2171_);
lean_dec_ref_known(v___x_2170_, 1);
v___x_2172_ = lean_box(0);
lean_inc(v_fst_1953_);
v___x_2173_ = l_Lean_MVarId_apply(v_fst_1953_, v_a_2171_, v_cfg_1939_, v___x_2172_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; lean_object* v___x_2175_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
lean_inc_n(v_a_2174_, 2);
lean_dec_ref_known(v___x_2173_, 1);
lean_inc(v_a_1946_);
lean_inc_ref(v_a_1945_);
lean_inc(v_a_1944_);
lean_inc_ref(v_a_1943_);
v___x_2175_ = lean_apply_6(v_act_1940_, v_a_2174_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, lean_box(0));
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_dec(v_a_2174_);
lean_dec(v_fst_1953_);
lean_dec_ref(v_allowFailure_1941_);
return v___x_2175_;
}
else
{
lean_object* v_a_2176_; uint8_t v___x_2177_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2176_);
v___x_2177_ = l_Lean_Exception_isInterrupt(v_a_2176_);
if (v___x_2177_ == 0)
{
uint8_t v___x_2178_; 
v___x_2178_ = l_Lean_Exception_isRuntime(v_a_2176_);
v___y_1959_ = v___x_2175_;
v___y_1960_ = v_a_2174_;
v___y_1961_ = v___x_2178_;
goto v___jp_1958_;
}
else
{
lean_dec(v_a_2176_);
v___y_1959_ = v___x_2175_;
v___y_1960_ = v_a_2174_;
v___y_1961_ = v___x_2177_;
goto v___jp_1958_;
}
}
}
else
{
lean_dec(v_fst_1953_);
lean_dec_ref(v_allowFailure_1941_);
lean_dec_ref(v_act_1940_);
return v___x_2173_;
}
}
else
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
lean_dec(v_fst_1953_);
lean_dec_ref(v_allowFailure_1941_);
lean_dec_ref(v_act_1940_);
lean_dec_ref(v_cfg_1939_);
v_a_2179_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2170_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2170_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
}
else
{
v___y_2095_ = v_a_2155_;
goto v___jp_2094_;
}
}
}
else
{
lean_object* v___x_2192_; lean_object* v_cache_2193_; lean_object* v_zetaDeltaFVarIds_2194_; lean_object* v_postponed_2195_; lean_object* v_diag_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2244_; 
lean_del_object(v___x_1986_);
lean_del_object(v___x_1956_);
lean_del_object(v___x_1951_);
v___x_2192_ = lean_st_ref_take(v_a_1944_);
v_cache_2193_ = lean_ctor_get(v___x_2192_, 1);
v_zetaDeltaFVarIds_2194_ = lean_ctor_get(v___x_2192_, 2);
v_postponed_2195_ = lean_ctor_get(v___x_2192_, 3);
v_diag_2196_ = lean_ctor_get(v___x_2192_, 4);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2244_ == 0)
{
lean_object* v_unused_2245_; 
v_unused_2245_ = lean_ctor_get(v___x_2192_, 0);
lean_dec(v_unused_2245_);
v___x_2198_ = v___x_2192_;
v_isShared_2199_ = v_isSharedCheck_2244_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_diag_2196_);
lean_inc(v_postponed_2195_);
lean_inc(v_zetaDeltaFVarIds_2194_);
lean_inc(v_cache_2193_);
lean_dec(v___x_2192_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2244_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 0, v_snd_1954_);
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_snd_1954_);
lean_ctor_set(v_reuseFailAlloc_2243_, 1, v_cache_2193_);
lean_ctor_set(v_reuseFailAlloc_2243_, 2, v_zetaDeltaFVarIds_2194_);
lean_ctor_set(v_reuseFailAlloc_2243_, 3, v_postponed_2195_);
lean_ctor_set(v_reuseFailAlloc_2243_, 4, v_diag_2196_);
v___x_2201_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
lean_object* v___x_2202_; uint8_t v___x_2203_; lean_object* v___x_2204_; 
v___x_2202_ = lean_st_ref_set(v_a_1944_, v___x_2201_);
v___x_2203_ = lean_unbox(v_snd_1984_);
lean_dec(v_snd_1984_);
v___x_2204_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_1983_, v___x_2203_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
lean_inc(v_a_2205_);
lean_dec_ref_known(v___x_2204_, 1);
v___x_2206_ = lean_box(0);
lean_inc(v_fst_1953_);
v___x_2207_ = l_Lean_MVarId_apply(v_fst_1953_, v_a_2205_, v_cfg_1939_, v___x_2206_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v_a_2208_; lean_object* v___x_2209_; 
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc_n(v_a_2208_, 2);
lean_dec_ref_known(v___x_2207_, 1);
lean_inc(v_a_1946_);
lean_inc_ref(v_a_1945_);
lean_inc(v_a_1944_);
lean_inc_ref(v_a_1943_);
v___x_2209_ = lean_apply_6(v_act_1940_, v_a_2208_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, lean_box(0));
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_dec(v_a_2208_);
lean_dec(v_fst_1953_);
lean_dec_ref(v_allowFailure_1941_);
return v___x_2209_;
}
else
{
lean_object* v_a_2210_; uint8_t v___y_2212_; uint8_t v___x_2233_; 
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_a_2210_);
v___x_2233_ = l_Lean_Exception_isInterrupt(v_a_2210_);
if (v___x_2233_ == 0)
{
uint8_t v___x_2234_; 
v___x_2234_ = l_Lean_Exception_isRuntime(v_a_2210_);
v___y_2212_ = v___x_2234_;
goto v___jp_2211_;
}
else
{
lean_dec(v_a_2210_);
v___y_2212_ = v___x_2233_;
goto v___jp_2211_;
}
v___jp_2211_:
{
if (v___y_2212_ == 0)
{
lean_object* v___x_2213_; 
lean_dec_ref_known(v___x_2209_, 1);
lean_inc(v_a_1946_);
lean_inc_ref(v_a_1945_);
lean_inc(v_a_1944_);
lean_inc_ref(v_a_1943_);
v___x_2213_ = lean_apply_6(v_allowFailure_1941_, v_fst_1953_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, lean_box(0));
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2224_; 
v_a_2214_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2216_ = v___x_2213_;
v_isShared_2217_ = v_isSharedCheck_2224_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2213_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2224_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
uint8_t v___x_2218_; 
v___x_2218_ = lean_unbox(v_a_2214_);
lean_dec(v_a_2214_);
if (v___x_2218_ == 0)
{
lean_object* v___x_2219_; lean_object* v___x_2220_; 
lean_del_object(v___x_2216_);
lean_dec(v_a_2208_);
v___x_2219_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1);
v___x_2220_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2219_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_);
return v___x_2220_;
}
else
{
lean_object* v___x_2222_; 
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 0, v_a_2208_);
v___x_2222_ = v___x_2216_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2208_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
else
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
lean_dec(v_a_2208_);
v_a_2225_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2213_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2213_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2225_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
else
{
lean_dec(v_a_2208_);
lean_dec(v_fst_1953_);
lean_dec_ref(v_allowFailure_1941_);
return v___x_2209_;
}
}
}
}
else
{
lean_dec(v_fst_1953_);
lean_dec_ref(v_allowFailure_1941_);
lean_dec_ref(v_act_1940_);
return v___x_2207_;
}
}
else
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
lean_dec(v_fst_1953_);
lean_dec_ref(v_allowFailure_1941_);
lean_dec_ref(v_act_1940_);
lean_dec_ref(v_cfg_1939_);
v_a_2235_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2237_ = v___x_2204_;
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2204_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2240_; 
if (v_isShared_2238_ == 0)
{
v___x_2240_ = v___x_2237_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2235_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___boxed(lean_object* v_cfg_2249_, lean_object* v_act_2250_, lean_object* v_allowFailure_2251_, lean_object* v_cand_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(v_cfg_2249_, v_act_2250_, v_allowFailure_2251_, v_cand_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_);
lean_dec(v_a_2256_);
lean_dec_ref(v_a_2255_);
lean_dec(v_a_2254_);
lean_dec_ref(v_a_2253_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3(lean_object* v_00_u03b1_2259_, lean_object* v_x_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v___x_2266_; 
v___x_2266_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_x_2260_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2267_, lean_object* v_x_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3(v_00_u03b1_2267_, v_x_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(lean_object* v_act_2277_, lean_object* v_a_2278_, uint8_t v_collectAll_2279_, lean_object* v_as_2280_, size_t v_sz_2281_, size_t v_i_2282_, lean_object* v_b_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v_a_2290_; uint8_t v___x_2294_; 
v___x_2294_ = lean_usize_dec_lt(v_i_2282_, v_sz_2281_);
if (v___x_2294_ == 0)
{
lean_object* v___x_2295_; 
lean_dec_ref(v_act_2277_);
v___x_2295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2295_, 0, v_b_2283_);
return v___x_2295_;
}
else
{
lean_object* v_snd_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2371_; 
v_snd_2296_ = lean_ctor_get(v_b_2283_, 1);
v_isSharedCheck_2371_ = !lean_is_exclusive(v_b_2283_);
if (v_isSharedCheck_2371_ == 0)
{
lean_object* v_unused_2372_; 
v_unused_2372_ = lean_ctor_get(v_b_2283_, 0);
lean_dec(v_unused_2372_);
v___x_2298_ = v_b_2283_;
v_isShared_2299_ = v_isSharedCheck_2371_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_snd_2296_);
lean_dec(v_b_2283_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2371_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2300_; lean_object* v_a_2301_; lean_object* v___x_2302_; 
v___x_2300_ = lean_box(0);
v_a_2301_ = lean_array_uget_borrowed(v_as_2280_, v_i_2282_);
lean_inc_ref(v_act_2277_);
lean_inc(v___y_2287_);
lean_inc_ref(v___y_2286_);
lean_inc(v___y_2285_);
lean_inc_ref(v___y_2284_);
lean_inc(v_a_2301_);
v___x_2302_ = lean_apply_6(v_act_2277_, v_a_2301_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, lean_box(0));
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2334_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2305_ = v___x_2302_;
v_isShared_2306_ = v_isSharedCheck_2334_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2302_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2334_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
uint8_t v___y_2308_; uint8_t v___x_2332_; 
v___x_2332_ = l_List_isEmpty___redArg(v_a_2303_);
if (v___x_2332_ == 0)
{
v___y_2308_ = v___x_2332_;
goto v___jp_2307_;
}
else
{
uint8_t v___x_2333_; 
v___x_2333_ = lean_bool_not(v_collectAll_2279_);
v___y_2308_ = v___x_2333_;
goto v___jp_2307_;
}
v___jp_2307_:
{
if (v___y_2308_ == 0)
{
lean_object* v___x_2309_; lean_object* v___x_2310_; 
lean_del_object(v___x_2305_);
v___x_2309_ = lean_st_ref_get(v___y_2285_);
v___x_2310_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2278_, v___y_2285_, v___y_2287_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_mctx_2311_; lean_object* v___x_2313_; 
lean_dec_ref_known(v___x_2310_, 1);
v_mctx_2311_ = lean_ctor_get(v___x_2309_, 0);
lean_inc_ref(v_mctx_2311_);
lean_dec(v___x_2309_);
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 1, v_mctx_2311_);
lean_ctor_set(v___x_2298_, 0, v_a_2303_);
v___x_2313_ = v___x_2298_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2303_);
lean_ctor_set(v_reuseFailAlloc_2316_, 1, v_mctx_2311_);
v___x_2313_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2314_ = lean_array_push(v_snd_2296_, v___x_2313_);
v___x_2315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2300_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
v_a_2290_ = v___x_2315_;
goto v___jp_2289_;
}
}
else
{
lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2324_; 
lean_dec(v___x_2309_);
lean_dec(v_a_2303_);
lean_del_object(v___x_2298_);
lean_dec(v_snd_2296_);
lean_dec_ref(v_act_2277_);
v_a_2317_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2319_ = v___x_2310_;
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2310_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2322_; 
if (v_isShared_2320_ == 0)
{
v___x_2322_ = v___x_2319_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_a_2317_);
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
else
{
lean_object* v___x_2325_; lean_object* v___x_2327_; 
lean_dec(v_a_2303_);
lean_dec_ref(v_act_2277_);
v___x_2325_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0___closed__0));
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 0, v___x_2325_);
v___x_2327_ = v___x_2298_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v___x_2325_);
lean_ctor_set(v_reuseFailAlloc_2331_, 1, v_snd_2296_);
v___x_2327_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
lean_object* v___x_2329_; 
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 0, v___x_2327_);
v___x_2329_ = v___x_2305_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2327_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
}
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2370_; 
v_a_2335_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2337_ = v___x_2302_;
v_isShared_2338_ = v_isSharedCheck_2370_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2302_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2370_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
uint8_t v___y_2340_; uint8_t v___x_2368_; 
v___x_2368_ = l_Lean_Exception_isInterrupt(v_a_2335_);
if (v___x_2368_ == 0)
{
uint8_t v___x_2369_; 
lean_inc(v_a_2335_);
v___x_2369_ = l_Lean_Exception_isRuntime(v_a_2335_);
v___y_2340_ = v___x_2369_;
goto v___jp_2339_;
}
else
{
v___y_2340_ = v___x_2368_;
goto v___jp_2339_;
}
v___jp_2339_:
{
if (v___y_2340_ == 0)
{
lean_object* v___x_2341_; 
lean_del_object(v___x_2337_);
v___x_2341_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2278_, v___y_2285_, v___y_2287_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2355_; 
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2355_ == 0)
{
lean_object* v_unused_2356_; 
v_unused_2356_ = lean_ctor_get(v___x_2341_, 0);
lean_dec(v_unused_2356_);
v___x_2343_ = v___x_2341_;
v_isShared_2344_ = v_isSharedCheck_2355_;
goto v_resetjp_2342_;
}
else
{
lean_dec(v___x_2341_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2355_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
uint8_t v___x_2345_; 
v___x_2345_ = l_Lean_Meta_LibrarySearch_isAbortSpeculation(v_a_2335_);
lean_dec(v_a_2335_);
if (v___x_2345_ == 0)
{
lean_object* v___x_2347_; 
lean_del_object(v___x_2343_);
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 0, v___x_2300_);
v___x_2347_ = v___x_2298_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2300_);
lean_ctor_set(v_reuseFailAlloc_2348_, 1, v_snd_2296_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
v_a_2290_ = v___x_2347_;
goto v___jp_2289_;
}
}
else
{
lean_object* v___x_2350_; 
lean_dec_ref(v_act_2277_);
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 0, v___x_2300_);
v___x_2350_ = v___x_2298_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v___x_2300_);
lean_ctor_set(v_reuseFailAlloc_2354_, 1, v_snd_2296_);
v___x_2350_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
lean_object* v___x_2352_; 
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 0, v___x_2350_);
v___x_2352_ = v___x_2343_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v___x_2350_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
}
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
lean_dec(v_a_2335_);
lean_del_object(v___x_2298_);
lean_dec(v_snd_2296_);
lean_dec_ref(v_act_2277_);
v_a_2357_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2341_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2341_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2360_ == 0)
{
v___x_2362_ = v___x_2359_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_a_2357_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
else
{
lean_object* v___x_2366_; 
lean_del_object(v___x_2298_);
lean_dec(v_snd_2296_);
lean_dec_ref(v_act_2277_);
if (v_isShared_2338_ == 0)
{
v___x_2366_ = v___x_2337_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2335_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
}
}
}
}
v___jp_2289_:
{
size_t v___x_2291_; size_t v___x_2292_; 
v___x_2291_ = ((size_t)1ULL);
v___x_2292_ = lean_usize_add(v_i_2282_, v___x_2291_);
v_i_2282_ = v___x_2292_;
v_b_2283_ = v_a_2290_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0___boxed(lean_object* v_act_2373_, lean_object* v_a_2374_, lean_object* v_collectAll_2375_, lean_object* v_as_2376_, lean_object* v_sz_2377_, lean_object* v_i_2378_, lean_object* v_b_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
uint8_t v_collectAll_boxed_2385_; size_t v_sz_boxed_2386_; size_t v_i_boxed_2387_; lean_object* v_res_2388_; 
v_collectAll_boxed_2385_ = lean_unbox(v_collectAll_2375_);
v_sz_boxed_2386_ = lean_unbox_usize(v_sz_2377_);
lean_dec(v_sz_2377_);
v_i_boxed_2387_ = lean_unbox_usize(v_i_2378_);
lean_dec(v_i_2378_);
v_res_2388_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(v_act_2373_, v_a_2374_, v_collectAll_boxed_2385_, v_as_2376_, v_sz_boxed_2386_, v_i_boxed_2387_, v_b_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec_ref(v_as_2376_);
lean_dec_ref(v_a_2374_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryOnEach(lean_object* v_act_2394_, lean_object* v_candidates_2395_, uint8_t v_collectAll_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_){
_start:
{
lean_object* v___x_2402_; 
v___x_2402_ = l_Lean_Meta_saveState___redArg(v_a_2398_, v_a_2400_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_a_2403_; lean_object* v___x_2404_; size_t v_sz_2405_; size_t v___x_2406_; lean_object* v___x_2407_; 
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_a_2403_);
lean_dec_ref_known(v___x_2402_, 1);
v___x_2404_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryOnEach___closed__1));
v_sz_2405_ = lean_array_size(v_candidates_2395_);
v___x_2406_ = ((size_t)0ULL);
v___x_2407_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(v_act_2394_, v_a_2403_, v_collectAll_2396_, v_candidates_2395_, v_sz_2405_, v___x_2406_, v___x_2404_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
lean_dec(v_a_2403_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2422_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2410_ = v___x_2407_;
v_isShared_2411_ = v_isSharedCheck_2422_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2407_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2422_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v_fst_2412_; 
v_fst_2412_ = lean_ctor_get(v_a_2408_, 0);
if (lean_obj_tag(v_fst_2412_) == 0)
{
lean_object* v_snd_2413_; lean_object* v___x_2414_; lean_object* v___x_2416_; 
v_snd_2413_ = lean_ctor_get(v_a_2408_, 1);
lean_inc(v_snd_2413_);
lean_dec(v_a_2408_);
v___x_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2414_, 0, v_snd_2413_);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 0, v___x_2414_);
v___x_2416_ = v___x_2410_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2414_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
else
{
lean_object* v_val_2418_; lean_object* v___x_2420_; 
lean_inc_ref(v_fst_2412_);
lean_dec(v_a_2408_);
v_val_2418_ = lean_ctor_get(v_fst_2412_, 0);
lean_inc(v_val_2418_);
lean_dec_ref_known(v_fst_2412_, 1);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 0, v_val_2418_);
v___x_2420_ = v___x_2410_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_val_2418_);
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
else
{
lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2430_; 
v_a_2423_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2425_ = v___x_2407_;
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_dec(v___x_2407_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2428_; 
if (v_isShared_2426_ == 0)
{
v___x_2428_ = v___x_2425_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_a_2423_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
}
}
else
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2438_; 
lean_dec_ref(v_act_2394_);
v_a_2431_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2433_ = v___x_2402_;
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2402_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2436_; 
if (v_isShared_2434_ == 0)
{
v___x_2436_ = v___x_2433_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_a_2431_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryOnEach___boxed(lean_object* v_act_2439_, lean_object* v_candidates_2440_, lean_object* v_collectAll_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_){
_start:
{
uint8_t v_collectAll_boxed_2447_; lean_object* v_res_2448_; 
v_collectAll_boxed_2447_ = lean_unbox(v_collectAll_2441_);
v_res_2448_ = l_Lean_Meta_LibrarySearch_tryOnEach(v_act_2439_, v_candidates_2440_, v_collectAll_boxed_2447_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_);
lean_dec(v_a_2445_);
lean_dec_ref(v_a_2444_);
lean_dec(v_a_2443_);
lean_dec_ref(v_a_2442_);
lean_dec_ref(v_candidates_2440_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1___redArg(){
_start:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2450_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0, &l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0_once, _init_l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0);
v___x_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2450_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1___redArg___boxed(lean_object* v___y_2452_){
_start:
{
lean_object* v_res_2453_; 
v_res_2453_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1___redArg();
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(lean_object* v_00_u03b1_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v___x_2460_; 
v___x_2460_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1___redArg();
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1___boxed(lean_object* v_00_u03b1_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_00_u03b1_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4___redArg(lean_object* v_category_2468_, lean_object* v_opts_2469_, lean_object* v_act_2470_, lean_object* v_decl_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; 
lean_inc(v___y_2475_);
lean_inc_ref(v___y_2474_);
lean_inc(v___y_2473_);
lean_inc_ref(v___y_2472_);
v___x_2477_ = lean_apply_4(v_act_2470_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
v___x_2478_ = l_Lean_profileitIOUnsafe___redArg(v_category_2468_, v_opts_2469_, v___x_2477_, v_decl_2471_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4___redArg___boxed(lean_object* v_category_2479_, lean_object* v_opts_2480_, lean_object* v_act_2481_, lean_object* v_decl_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4___redArg(v_category_2479_, v_opts_2480_, v_act_2481_, v_decl_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec_ref(v_opts_2480_);
lean_dec_ref(v_category_2479_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(lean_object* v_00_u03b1_2489_, lean_object* v_category_2490_, lean_object* v_opts_2491_, lean_object* v_act_2492_, lean_object* v_decl_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
lean_object* v___x_2499_; 
v___x_2499_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4___redArg(v_category_2490_, v_opts_2491_, v_act_2492_, v_decl_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4___boxed(lean_object* v_00_u03b1_2500_, lean_object* v_category_2501_, lean_object* v_opts_2502_, lean_object* v_act_2503_, lean_object* v_decl_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v_00_u03b1_2500_, v_category_2501_, v_opts_2502_, v_act_2503_, v_decl_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec_ref(v_opts_2502_);
lean_dec_ref(v_category_2501_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0(lean_object* v_goal_2511_, lean_object* v_x_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v___x_2518_; 
v___x_2518_ = l_Lean_MVarId_getType(v_goal_2511_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2527_; 
v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2521_ = v___x_2518_;
v_isShared_2522_ = v_isSharedCheck_2527_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v___x_2518_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2527_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2523_; lean_object* v___x_2525_; 
v___x_2523_ = l_Lean_MessageData_ofExpr(v_a_2519_);
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 0, v___x_2523_);
v___x_2525_ = v___x_2521_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v___x_2523_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
else
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
v_a_2528_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2530_ = v___x_2518_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2518_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2533_; 
if (v_isShared_2531_ == 0)
{
v___x_2533_ = v___x_2530_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_a_2528_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed(lean_object* v_goal_2536_, lean_object* v_x_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
lean_object* v_res_2543_; 
v_res_2543_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0(v_goal_2536_, v_x_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
lean_dec_ref(v_x_2537_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1(lean_object* v_a_2544_, lean_object* v___x_2545_, lean_object* v_tactic_2546_, lean_object* v_allowFailure_2547_, lean_object* v_cand_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
lean_object* v___x_2554_; 
lean_inc(v___y_2552_);
lean_inc_ref(v___y_2551_);
lean_inc(v___y_2550_);
lean_inc_ref(v___y_2549_);
v___x_2554_ = lean_apply_5(v_a_2544_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, lean_box(0));
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v_a_2555_; uint8_t v___x_2556_; 
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
lean_inc(v_a_2555_);
lean_dec_ref_known(v___x_2554_, 1);
v___x_2556_ = lean_unbox(v_a_2555_);
lean_dec(v_a_2555_);
if (v___x_2556_ == 0)
{
lean_object* v___x_2557_; 
v___x_2557_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(v___x_2545_, v_tactic_2546_, v_allowFailure_2547_, v_cand_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
return v___x_2557_;
}
else
{
lean_object* v___x_2558_; lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
lean_dec_ref(v_cand_2548_);
lean_dec_ref(v_allowFailure_2547_);
lean_dec_ref(v_tactic_2546_);
lean_dec_ref(v___x_2545_);
v___x_2558_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1___redArg();
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2558_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2558_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
}
else
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2574_; 
lean_dec_ref(v_cand_2548_);
lean_dec_ref(v_allowFailure_2547_);
lean_dec_ref(v_tactic_2546_);
lean_dec_ref(v___x_2545_);
v_a_2567_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2569_ = v___x_2554_;
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2554_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2572_; 
if (v_isShared_2570_ == 0)
{
v___x_2572_ = v___x_2569_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_a_2567_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed(lean_object* v_a_2575_, lean_object* v___x_2576_, lean_object* v_tactic_2577_, lean_object* v_allowFailure_2578_, lean_object* v_cand_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1(v_a_2575_, v___x_2576_, v_tactic_2577_, v_allowFailure_2578_, v_cand_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
return v_res_2585_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3(lean_object* v_as_2586_, size_t v_i_2587_, size_t v_stop_2588_){
_start:
{
uint8_t v___x_2589_; 
v___x_2589_ = lean_usize_dec_eq(v_i_2587_, v_stop_2588_);
if (v___x_2589_ == 0)
{
lean_object* v___x_2590_; lean_object* v_fst_2591_; uint8_t v___x_2592_; 
v___x_2590_ = lean_array_uget_borrowed(v_as_2586_, v_i_2587_);
v_fst_2591_ = lean_ctor_get(v___x_2590_, 0);
v___x_2592_ = l_List_isEmpty___redArg(v_fst_2591_);
if (v___x_2592_ == 0)
{
size_t v___x_2593_; size_t v___x_2594_; 
v___x_2593_ = ((size_t)1ULL);
v___x_2594_ = lean_usize_add(v_i_2587_, v___x_2593_);
v_i_2587_ = v___x_2594_;
goto _start;
}
else
{
return v___x_2592_;
}
}
else
{
uint8_t v___x_2596_; 
v___x_2596_ = 0;
return v___x_2596_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___boxed(lean_object* v_as_2597_, lean_object* v_i_2598_, lean_object* v_stop_2599_){
_start:
{
size_t v_i_boxed_2600_; size_t v_stop_boxed_2601_; uint8_t v_res_2602_; lean_object* v_r_2603_; 
v_i_boxed_2600_ = lean_unbox_usize(v_i_2598_);
lean_dec(v_i_2598_);
v_stop_boxed_2601_ = lean_unbox_usize(v_stop_2599_);
lean_dec(v_stop_2599_);
v_res_2602_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3(v_as_2597_, v_i_boxed_2600_, v_stop_boxed_2601_);
lean_dec_ref(v_as_2597_);
v_r_2603_ = lean_box(v_res_2602_);
return v_r_2603_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(lean_object* v_goal_2604_, lean_object* v___x_2605_, size_t v_sz_2606_, size_t v_i_2607_, lean_object* v_bs_2608_){
_start:
{
uint8_t v___x_2609_; 
v___x_2609_ = lean_usize_dec_lt(v_i_2607_, v_sz_2606_);
if (v___x_2609_ == 0)
{
lean_dec_ref(v___x_2605_);
lean_dec(v_goal_2604_);
return v_bs_2608_;
}
else
{
lean_object* v_v_2610_; lean_object* v___x_2611_; lean_object* v_bs_x27_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; size_t v___x_2615_; size_t v___x_2616_; lean_object* v___x_2617_; 
v_v_2610_ = lean_array_uget(v_bs_2608_, v_i_2607_);
v___x_2611_ = lean_unsigned_to_nat(0u);
v_bs_x27_2612_ = lean_array_uset(v_bs_2608_, v_i_2607_, v___x_2611_);
lean_inc_ref(v___x_2605_);
lean_inc(v_goal_2604_);
v___x_2613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2613_, 0, v_goal_2604_);
lean_ctor_set(v___x_2613_, 1, v___x_2605_);
v___x_2614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2613_);
lean_ctor_set(v___x_2614_, 1, v_v_2610_);
v___x_2615_ = ((size_t)1ULL);
v___x_2616_ = lean_usize_add(v_i_2607_, v___x_2615_);
v___x_2617_ = lean_array_uset(v_bs_x27_2612_, v_i_2607_, v___x_2614_);
v_i_2607_ = v___x_2616_;
v_bs_2608_ = v___x_2617_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2___boxed(lean_object* v_goal_2619_, lean_object* v___x_2620_, lean_object* v_sz_2621_, lean_object* v_i_2622_, lean_object* v_bs_2623_){
_start:
{
size_t v_sz_boxed_2624_; size_t v_i_boxed_2625_; lean_object* v_res_2626_; 
v_sz_boxed_2624_ = lean_unbox_usize(v_sz_2621_);
lean_dec(v_sz_2621_);
v_i_boxed_2625_ = lean_unbox_usize(v_i_2622_);
lean_dec(v_i_2622_);
v_res_2626_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_goal_2619_, v___x_2620_, v_sz_boxed_2624_, v_i_boxed_2625_, v_bs_2623_);
return v_res_2626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2(lean_object* v_leavePercentHeartbeats_2628_, lean_object* v_goal_2629_, lean_object* v___x_2630_, lean_object* v_tactic_2631_, lean_object* v_allowFailure_2632_, uint8_t v_collectAll_2633_, uint8_t v_includeStar_2634_, uint8_t v___x_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v___x_2644_; 
v___x_2644_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercentHeartbeats_2628_, v___y_2638_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v_a_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
v_a_2645_ = lean_ctor_get(v___x_2644_, 0);
lean_inc(v_a_2645_);
lean_dec_ref_known(v___x_2644_, 1);
v___x_2646_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2___closed__0));
lean_inc(v_goal_2629_);
v___x_2647_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v___x_2646_, v_goal_2629_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v_a_2648_; lean_object* v___f_2649_; lean_object* v___x_2650_; 
v_a_2648_ = lean_ctor_get(v___x_2647_, 0);
lean_inc(v_a_2648_);
lean_dec_ref_known(v___x_2647_, 1);
v___f_2649_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed), 10, 4);
lean_closure_set(v___f_2649_, 0, v_a_2645_);
lean_closure_set(v___f_2649_, 1, v___x_2630_);
lean_closure_set(v___f_2649_, 2, v_tactic_2631_);
lean_closure_set(v___f_2649_, 3, v_allowFailure_2632_);
lean_inc_ref(v___f_2649_);
v___x_2650_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2649_, v_a_2648_, v_collectAll_2633_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
lean_dec(v_a_2648_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; 
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2651_);
if (lean_obj_tag(v_a_2651_) == 0)
{
lean_dec_ref_known(v___x_2650_, 1);
lean_dec_ref(v___f_2649_);
lean_dec(v_goal_2629_);
goto v___jp_2641_;
}
else
{
lean_object* v_val_2652_; uint8_t v___y_2654_; uint8_t v___y_2700_; lean_object* v___x_2706_; lean_object* v___x_2707_; uint8_t v___x_2708_; 
v_val_2652_ = lean_ctor_get(v_a_2651_, 0);
v___x_2706_ = lean_unsigned_to_nat(0u);
v___x_2707_ = lean_array_get_size(v_val_2652_);
v___x_2708_ = lean_nat_dec_lt(v___x_2706_, v___x_2707_);
if (v___x_2708_ == 0)
{
v___y_2700_ = v___x_2635_;
goto v___jp_2699_;
}
else
{
if (v___x_2708_ == 0)
{
v___y_2700_ = v___x_2635_;
goto v___jp_2699_;
}
else
{
size_t v___x_2709_; size_t v___x_2710_; uint8_t v___x_2711_; 
v___x_2709_ = ((size_t)0ULL);
v___x_2710_ = lean_usize_of_nat(v___x_2707_);
v___x_2711_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3(v_val_2652_, v___x_2709_, v___x_2710_);
v___y_2700_ = v___x_2711_;
goto v___jp_2699_;
}
}
v___jp_2653_:
{
if (v___y_2654_ == 0)
{
uint8_t v___x_2655_; 
v___x_2655_ = lean_bool_not(v_includeStar_2634_);
if (v___x_2655_ == 0)
{
lean_object* v___x_2656_; 
lean_dec_ref_known(v___x_2650_, 1);
v___x_2656_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2690_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2659_ = v___x_2656_;
v_isShared_2660_ = v_isSharedCheck_2690_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_a_2657_);
lean_dec(v___x_2656_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2690_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; uint8_t v___x_2663_; 
v___x_2661_ = lean_array_get_size(v_a_2657_);
v___x_2662_ = lean_unsigned_to_nat(0u);
v___x_2663_ = lean_nat_dec_eq(v___x_2661_, v___x_2662_);
if (v___x_2663_ == 0)
{
lean_object* v___x_2664_; lean_object* v_mctx_2665_; size_t v_sz_2666_; size_t v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
lean_inc(v_val_2652_);
lean_del_object(v___x_2659_);
lean_dec_ref_known(v_a_2651_, 1);
v___x_2664_ = lean_st_ref_get(v___y_2637_);
v_mctx_2665_ = lean_ctor_get(v___x_2664_, 0);
lean_inc_ref(v_mctx_2665_);
lean_dec(v___x_2664_);
v_sz_2666_ = lean_array_size(v_a_2657_);
v___x_2667_ = ((size_t)0ULL);
v___x_2668_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_goal_2629_, v_mctx_2665_, v_sz_2666_, v___x_2667_, v_a_2657_);
v___x_2669_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2649_, v___x_2668_, v_collectAll_2633_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
lean_dec_ref(v___x_2668_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2686_; 
v_a_2670_ = lean_ctor_get(v___x_2669_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2672_ = v___x_2669_;
v_isShared_2673_ = v_isSharedCheck_2686_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___x_2669_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2686_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
if (lean_obj_tag(v_a_2670_) == 0)
{
lean_del_object(v___x_2672_);
lean_dec(v_val_2652_);
goto v___jp_2641_;
}
else
{
lean_object* v_val_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2685_; 
v_val_2674_ = lean_ctor_get(v_a_2670_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v_a_2670_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2676_ = v_a_2670_;
v_isShared_2677_ = v_isSharedCheck_2685_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_val_2674_);
lean_dec(v_a_2670_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2685_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___x_2678_; lean_object* v___x_2680_; 
v___x_2678_ = l_Array_append___redArg(v_val_2652_, v_val_2674_);
lean_dec(v_val_2674_);
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 0, v___x_2678_);
v___x_2680_ = v___x_2676_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2678_);
v___x_2680_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
lean_object* v___x_2682_; 
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 0, v___x_2680_);
v___x_2682_ = v___x_2672_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2680_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
}
}
}
else
{
lean_dec(v_val_2652_);
return v___x_2669_;
}
}
else
{
lean_object* v___x_2688_; 
lean_dec(v_a_2657_);
lean_dec_ref(v___f_2649_);
lean_dec(v_goal_2629_);
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 0, v_a_2651_);
v___x_2688_ = v___x_2659_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v_a_2651_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
}
else
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
lean_dec_ref_known(v_a_2651_, 1);
lean_dec_ref(v___f_2649_);
lean_dec(v_goal_2629_);
v_a_2691_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2693_ = v___x_2656_;
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2656_);
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
else
{
lean_dec_ref_known(v_a_2651_, 1);
lean_dec_ref(v___f_2649_);
lean_dec(v_goal_2629_);
return v___x_2650_;
}
}
else
{
lean_dec_ref_known(v_a_2651_, 1);
lean_dec_ref(v___f_2649_);
lean_dec(v_goal_2629_);
return v___x_2650_;
}
}
v___jp_2699_:
{
if (v___y_2700_ == 0)
{
uint8_t v___x_2701_; 
v___x_2701_ = lean_bool_not(v_collectAll_2633_);
if (v___x_2701_ == 0)
{
v___y_2654_ = v___x_2701_;
goto v___jp_2653_;
}
else
{
lean_object* v___x_2702_; lean_object* v___x_2703_; uint8_t v___x_2704_; uint8_t v___x_2705_; 
v___x_2702_ = lean_array_get_size(v_val_2652_);
v___x_2703_ = lean_unsigned_to_nat(0u);
v___x_2704_ = lean_nat_dec_eq(v___x_2702_, v___x_2703_);
v___x_2705_ = lean_bool_not(v___x_2704_);
v___y_2654_ = v___x_2705_;
goto v___jp_2653_;
}
}
else
{
lean_dec_ref_known(v_a_2651_, 1);
lean_dec_ref(v___f_2649_);
lean_dec(v_goal_2629_);
return v___x_2650_;
}
}
}
}
else
{
lean_dec_ref(v___f_2649_);
lean_dec(v_goal_2629_);
return v___x_2650_;
}
}
else
{
lean_object* v_a_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2719_; 
lean_dec(v_a_2645_);
lean_dec_ref(v_allowFailure_2632_);
lean_dec_ref(v_tactic_2631_);
lean_dec_ref(v___x_2630_);
lean_dec(v_goal_2629_);
v_a_2712_ = lean_ctor_get(v___x_2647_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2714_ = v___x_2647_;
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_a_2712_);
lean_dec(v___x_2647_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2717_; 
if (v_isShared_2715_ == 0)
{
v___x_2717_ = v___x_2714_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_a_2712_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
}
}
else
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
lean_dec_ref(v_allowFailure_2632_);
lean_dec_ref(v_tactic_2631_);
lean_dec_ref(v___x_2630_);
lean_dec(v_goal_2629_);
v_a_2720_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2644_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2644_);
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
v___jp_2641_:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2642_ = lean_box(0);
v___x_2643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2643_, 0, v___x_2642_);
return v___x_2643_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2___boxed(lean_object* v_leavePercentHeartbeats_2728_, lean_object* v_goal_2729_, lean_object* v___x_2730_, lean_object* v_tactic_2731_, lean_object* v_allowFailure_2732_, lean_object* v_collectAll_2733_, lean_object* v_includeStar_2734_, lean_object* v___x_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
uint8_t v_collectAll_boxed_2741_; uint8_t v_includeStar_boxed_2742_; uint8_t v___x_15020__boxed_2743_; lean_object* v_res_2744_; 
v_collectAll_boxed_2741_ = lean_unbox(v_collectAll_2733_);
v_includeStar_boxed_2742_ = lean_unbox(v_includeStar_2734_);
v___x_15020__boxed_2743_ = lean_unbox(v___x_2735_);
v_res_2744_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2(v_leavePercentHeartbeats_2728_, v_goal_2729_, v___x_2730_, v_tactic_2731_, v_allowFailure_2732_, v_collectAll_boxed_2741_, v_includeStar_boxed_2742_, v___x_15020__boxed_2743_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v_leavePercentHeartbeats_2728_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4(lean_object* v_leavePercentHeartbeats_2745_, lean_object* v_goal_2746_, lean_object* v___x_2747_, lean_object* v_tactic_2748_, lean_object* v_allowFailure_2749_, uint8_t v_collectAll_2750_, uint8_t v_includeStar_2751_, uint8_t v___x_2752_, uint8_t v___x_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v___x_2762_; 
v___x_2762_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercentHeartbeats_2745_, v___y_2756_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
lean_inc(v_a_2763_);
lean_dec_ref_known(v___x_2762_, 1);
v___x_2764_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2___closed__0));
lean_inc(v_goal_2746_);
v___x_2765_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v___x_2764_, v_goal_2746_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v_a_2766_; lean_object* v___f_2767_; lean_object* v___x_2768_; 
v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
lean_inc(v_a_2766_);
lean_dec_ref_known(v___x_2765_, 1);
v___f_2767_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed), 10, 4);
lean_closure_set(v___f_2767_, 0, v_a_2763_);
lean_closure_set(v___f_2767_, 1, v___x_2747_);
lean_closure_set(v___f_2767_, 2, v_tactic_2748_);
lean_closure_set(v___f_2767_, 3, v_allowFailure_2749_);
lean_inc_ref(v___f_2767_);
v___x_2768_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2767_, v_a_2766_, v_collectAll_2750_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_);
lean_dec(v_a_2766_);
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_object* v_a_2769_; 
v_a_2769_ = lean_ctor_get(v___x_2768_, 0);
lean_inc(v_a_2769_);
if (lean_obj_tag(v_a_2769_) == 0)
{
lean_dec_ref_known(v___x_2768_, 1);
lean_dec_ref(v___f_2767_);
lean_dec(v_goal_2746_);
goto v___jp_2759_;
}
else
{
lean_object* v_val_2770_; uint8_t v___y_2772_; uint8_t v___y_2817_; uint8_t v___y_2820_; lean_object* v___x_2826_; lean_object* v___x_2827_; uint8_t v___x_2828_; 
v_val_2770_ = lean_ctor_get(v_a_2769_, 0);
v___x_2826_ = lean_unsigned_to_nat(0u);
v___x_2827_ = lean_array_get_size(v_val_2770_);
v___x_2828_ = lean_nat_dec_lt(v___x_2826_, v___x_2827_);
if (v___x_2828_ == 0)
{
v___y_2820_ = v___x_2753_;
goto v___jp_2819_;
}
else
{
if (v___x_2828_ == 0)
{
v___y_2820_ = v___x_2753_;
goto v___jp_2819_;
}
else
{
size_t v___x_2829_; size_t v___x_2830_; uint8_t v___x_2831_; 
v___x_2829_ = ((size_t)0ULL);
v___x_2830_ = lean_usize_of_nat(v___x_2827_);
v___x_2831_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3(v_val_2770_, v___x_2829_, v___x_2830_);
v___y_2820_ = v___x_2831_;
goto v___jp_2819_;
}
}
v___jp_2771_:
{
if (v___y_2772_ == 0)
{
lean_object* v___x_2773_; 
lean_dec_ref_known(v___x_2768_, 1);
v___x_2773_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2807_; 
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2776_ = v___x_2773_;
v_isShared_2777_ = v_isSharedCheck_2807_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_dec(v___x_2773_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2807_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; uint8_t v___x_2780_; 
v___x_2778_ = lean_array_get_size(v_a_2774_);
v___x_2779_ = lean_unsigned_to_nat(0u);
v___x_2780_ = lean_nat_dec_eq(v___x_2778_, v___x_2779_);
if (v___x_2780_ == 0)
{
lean_object* v___x_2781_; lean_object* v_mctx_2782_; size_t v_sz_2783_; size_t v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
lean_inc(v_val_2770_);
lean_del_object(v___x_2776_);
lean_dec_ref_known(v_a_2769_, 1);
v___x_2781_ = lean_st_ref_get(v___y_2755_);
v_mctx_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc_ref(v_mctx_2782_);
lean_dec(v___x_2781_);
v_sz_2783_ = lean_array_size(v_a_2774_);
v___x_2784_ = ((size_t)0ULL);
v___x_2785_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_goal_2746_, v_mctx_2782_, v_sz_2783_, v___x_2784_, v_a_2774_);
v___x_2786_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2767_, v___x_2785_, v_collectAll_2750_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_);
lean_dec_ref(v___x_2785_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2803_; 
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2789_ = v___x_2786_;
v_isShared_2790_ = v_isSharedCheck_2803_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_dec(v___x_2786_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2803_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
if (lean_obj_tag(v_a_2787_) == 0)
{
lean_del_object(v___x_2789_);
lean_dec(v_val_2770_);
goto v___jp_2759_;
}
else
{
lean_object* v_val_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2802_; 
v_val_2791_ = lean_ctor_get(v_a_2787_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v_a_2787_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2793_ = v_a_2787_;
v_isShared_2794_ = v_isSharedCheck_2802_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_val_2791_);
lean_dec(v_a_2787_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2802_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2795_; lean_object* v___x_2797_; 
v___x_2795_ = l_Array_append___redArg(v_val_2770_, v_val_2791_);
lean_dec(v_val_2791_);
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 0, v___x_2795_);
v___x_2797_ = v___x_2793_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2795_);
v___x_2797_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
lean_object* v___x_2799_; 
if (v_isShared_2790_ == 0)
{
lean_ctor_set(v___x_2789_, 0, v___x_2797_);
v___x_2799_ = v___x_2789_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v___x_2797_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
}
}
}
else
{
lean_dec(v_val_2770_);
return v___x_2786_;
}
}
else
{
lean_object* v___x_2805_; 
lean_dec(v_a_2774_);
lean_dec_ref(v___f_2767_);
lean_dec(v_goal_2746_);
if (v_isShared_2777_ == 0)
{
lean_ctor_set(v___x_2776_, 0, v_a_2769_);
v___x_2805_ = v___x_2776_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2769_);
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
lean_dec_ref_known(v_a_2769_, 1);
lean_dec_ref(v___f_2767_);
lean_dec(v_goal_2746_);
v_a_2808_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v___x_2773_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2773_);
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
}
else
{
lean_dec_ref_known(v_a_2769_, 1);
lean_dec_ref(v___f_2767_);
lean_dec(v_goal_2746_);
return v___x_2768_;
}
}
v___jp_2816_:
{
if (v___y_2817_ == 0)
{
uint8_t v___x_2818_; 
v___x_2818_ = lean_bool_not(v_includeStar_2751_);
v___y_2772_ = v___x_2818_;
goto v___jp_2771_;
}
else
{
v___y_2772_ = v___x_2752_;
goto v___jp_2771_;
}
}
v___jp_2819_:
{
if (v___y_2820_ == 0)
{
uint8_t v___x_2821_; 
v___x_2821_ = lean_bool_not(v_collectAll_2750_);
if (v___x_2821_ == 0)
{
v___y_2817_ = v___x_2821_;
goto v___jp_2816_;
}
else
{
lean_object* v___x_2822_; lean_object* v___x_2823_; uint8_t v___x_2824_; uint8_t v___x_2825_; 
v___x_2822_ = lean_array_get_size(v_val_2770_);
v___x_2823_ = lean_unsigned_to_nat(0u);
v___x_2824_ = lean_nat_dec_eq(v___x_2822_, v___x_2823_);
v___x_2825_ = lean_bool_not(v___x_2824_);
v___y_2817_ = v___x_2825_;
goto v___jp_2816_;
}
}
else
{
v___y_2817_ = v___x_2752_;
goto v___jp_2816_;
}
}
}
}
else
{
lean_dec_ref(v___f_2767_);
lean_dec(v_goal_2746_);
return v___x_2768_;
}
}
else
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
lean_dec(v_a_2763_);
lean_dec_ref(v_allowFailure_2749_);
lean_dec_ref(v_tactic_2748_);
lean_dec_ref(v___x_2747_);
lean_dec(v_goal_2746_);
v_a_2832_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2834_ = v___x_2765_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2765_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2832_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
}
else
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
lean_dec_ref(v_allowFailure_2749_);
lean_dec_ref(v_tactic_2748_);
lean_dec_ref(v___x_2747_);
lean_dec(v_goal_2746_);
v_a_2840_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2762_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2762_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2840_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
v___jp_2759_:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2760_ = lean_box(0);
v___x_2761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2760_);
return v___x_2761_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4___boxed(lean_object* v_leavePercentHeartbeats_2848_, lean_object* v_goal_2849_, lean_object* v___x_2850_, lean_object* v_tactic_2851_, lean_object* v_allowFailure_2852_, lean_object* v_collectAll_2853_, lean_object* v_includeStar_2854_, lean_object* v___x_2855_, lean_object* v___x_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
uint8_t v_collectAll_boxed_2862_; uint8_t v_includeStar_boxed_2863_; uint8_t v___x_15215__boxed_2864_; uint8_t v___x_15216__boxed_2865_; lean_object* v_res_2866_; 
v_collectAll_boxed_2862_ = lean_unbox(v_collectAll_2853_);
v_includeStar_boxed_2863_ = lean_unbox(v_includeStar_2854_);
v___x_15215__boxed_2864_ = lean_unbox(v___x_2855_);
v___x_15216__boxed_2865_ = lean_unbox(v___x_2856_);
v_res_2866_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4(v_leavePercentHeartbeats_2848_, v_goal_2849_, v___x_2850_, v_tactic_2851_, v_allowFailure_2852_, v_collectAll_boxed_2862_, v_includeStar_boxed_2863_, v___x_15215__boxed_2864_, v___x_15216__boxed_2865_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
lean_dec(v___y_2858_);
lean_dec_ref(v___y_2857_);
lean_dec(v_leavePercentHeartbeats_2848_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__7(lean_object* v_leavePercentHeartbeats_2867_, lean_object* v_goal_2868_, lean_object* v___x_2869_, lean_object* v_tactic_2870_, lean_object* v_allowFailure_2871_, uint8_t v_collectAll_2872_, uint8_t v_includeStar_2873_, uint8_t v___x_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_){
_start:
{
lean_object* v___x_2883_; 
v___x_2883_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercentHeartbeats_2867_, v___y_2877_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_a_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_a_2884_);
lean_dec_ref_known(v___x_2883_, 1);
v___x_2885_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2___closed__0));
lean_inc(v_goal_2868_);
v___x_2886_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v___x_2885_, v_goal_2868_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_object* v_a_2887_; lean_object* v___f_2888_; lean_object* v___x_2889_; 
v_a_2887_ = lean_ctor_get(v___x_2886_, 0);
lean_inc(v_a_2887_);
lean_dec_ref_known(v___x_2886_, 1);
v___f_2888_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed), 10, 4);
lean_closure_set(v___f_2888_, 0, v_a_2884_);
lean_closure_set(v___f_2888_, 1, v___x_2869_);
lean_closure_set(v___f_2888_, 2, v_tactic_2870_);
lean_closure_set(v___f_2888_, 3, v_allowFailure_2871_);
lean_inc_ref(v___f_2888_);
v___x_2889_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2888_, v_a_2887_, v_collectAll_2872_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
lean_dec(v_a_2887_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v_a_2890_; 
v_a_2890_ = lean_ctor_get(v___x_2889_, 0);
lean_inc(v_a_2890_);
if (lean_obj_tag(v_a_2890_) == 0)
{
lean_dec_ref_known(v___x_2889_, 1);
lean_dec_ref(v___f_2888_);
lean_dec(v_goal_2868_);
goto v___jp_2880_;
}
else
{
lean_object* v_val_2891_; uint8_t v___y_2893_; uint8_t v___y_2938_; lean_object* v___x_2946_; lean_object* v___x_2947_; uint8_t v___x_2948_; 
v_val_2891_ = lean_ctor_get(v_a_2890_, 0);
v___x_2946_ = lean_unsigned_to_nat(0u);
v___x_2947_ = lean_array_get_size(v_val_2891_);
v___x_2948_ = lean_nat_dec_lt(v___x_2946_, v___x_2947_);
if (v___x_2948_ == 0)
{
goto v___jp_2940_;
}
else
{
if (v___x_2948_ == 0)
{
goto v___jp_2940_;
}
else
{
size_t v___x_2949_; size_t v___x_2950_; uint8_t v___x_2951_; 
v___x_2949_ = ((size_t)0ULL);
v___x_2950_ = lean_usize_of_nat(v___x_2947_);
v___x_2951_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3(v_val_2891_, v___x_2949_, v___x_2950_);
if (v___x_2951_ == 0)
{
goto v___jp_2940_;
}
else
{
v___y_2938_ = v___x_2874_;
goto v___jp_2937_;
}
}
}
v___jp_2892_:
{
if (v___y_2893_ == 0)
{
lean_object* v___x_2894_; 
lean_dec_ref_known(v___x_2889_, 1);
v___x_2894_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2928_; 
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2897_ = v___x_2894_;
v_isShared_2898_ = v_isSharedCheck_2928_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2894_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2928_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; uint8_t v___x_2901_; 
v___x_2899_ = lean_array_get_size(v_a_2895_);
v___x_2900_ = lean_unsigned_to_nat(0u);
v___x_2901_ = lean_nat_dec_eq(v___x_2899_, v___x_2900_);
if (v___x_2901_ == 0)
{
lean_object* v___x_2902_; lean_object* v_mctx_2903_; size_t v_sz_2904_; size_t v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
lean_inc(v_val_2891_);
lean_del_object(v___x_2897_);
lean_dec_ref_known(v_a_2890_, 1);
v___x_2902_ = lean_st_ref_get(v___y_2876_);
v_mctx_2903_ = lean_ctor_get(v___x_2902_, 0);
lean_inc_ref(v_mctx_2903_);
lean_dec(v___x_2902_);
v_sz_2904_ = lean_array_size(v_a_2895_);
v___x_2905_ = ((size_t)0ULL);
v___x_2906_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_goal_2868_, v_mctx_2903_, v_sz_2904_, v___x_2905_, v_a_2895_);
v___x_2907_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2888_, v___x_2906_, v_collectAll_2872_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
lean_dec_ref(v___x_2906_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2924_; 
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2910_ = v___x_2907_;
v_isShared_2911_ = v_isSharedCheck_2924_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2907_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2924_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
if (lean_obj_tag(v_a_2908_) == 0)
{
lean_del_object(v___x_2910_);
lean_dec(v_val_2891_);
goto v___jp_2880_;
}
else
{
lean_object* v_val_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2923_; 
v_val_2912_ = lean_ctor_get(v_a_2908_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v_a_2908_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2914_ = v_a_2908_;
v_isShared_2915_ = v_isSharedCheck_2923_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_val_2912_);
lean_dec(v_a_2908_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2923_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2916_; lean_object* v___x_2918_; 
v___x_2916_ = l_Array_append___redArg(v_val_2891_, v_val_2912_);
lean_dec(v_val_2912_);
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 0, v___x_2916_);
v___x_2918_ = v___x_2914_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v___x_2916_);
v___x_2918_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
lean_object* v___x_2920_; 
if (v_isShared_2911_ == 0)
{
lean_ctor_set(v___x_2910_, 0, v___x_2918_);
v___x_2920_ = v___x_2910_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v___x_2918_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
}
}
}
else
{
lean_dec(v_val_2891_);
return v___x_2907_;
}
}
else
{
lean_object* v___x_2926_; 
lean_dec(v_a_2895_);
lean_dec_ref(v___f_2888_);
lean_dec(v_goal_2868_);
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 0, v_a_2890_);
v___x_2926_ = v___x_2897_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_a_2890_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
}
else
{
lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2936_; 
lean_dec_ref_known(v_a_2890_, 1);
lean_dec_ref(v___f_2888_);
lean_dec(v_goal_2868_);
v_a_2929_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2931_ = v___x_2894_;
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2929_);
lean_dec(v___x_2894_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2934_; 
if (v_isShared_2932_ == 0)
{
v___x_2934_ = v___x_2931_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_a_2929_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_2890_, 1);
lean_dec_ref(v___f_2888_);
lean_dec(v_goal_2868_);
return v___x_2889_;
}
}
v___jp_2937_:
{
if (v___y_2938_ == 0)
{
uint8_t v___x_2939_; 
v___x_2939_ = lean_bool_not(v_includeStar_2873_);
v___y_2893_ = v___x_2939_;
goto v___jp_2892_;
}
else
{
v___y_2893_ = v___x_2874_;
goto v___jp_2892_;
}
}
v___jp_2940_:
{
uint8_t v___x_2941_; 
v___x_2941_ = lean_bool_not(v_collectAll_2872_);
if (v___x_2941_ == 0)
{
v___y_2938_ = v___x_2941_;
goto v___jp_2937_;
}
else
{
lean_object* v___x_2942_; lean_object* v___x_2943_; uint8_t v___x_2944_; uint8_t v___x_2945_; 
v___x_2942_ = lean_array_get_size(v_val_2891_);
v___x_2943_ = lean_unsigned_to_nat(0u);
v___x_2944_ = lean_nat_dec_eq(v___x_2942_, v___x_2943_);
v___x_2945_ = lean_bool_not(v___x_2944_);
v___y_2938_ = v___x_2945_;
goto v___jp_2937_;
}
}
}
}
else
{
lean_dec_ref(v___f_2888_);
lean_dec(v_goal_2868_);
return v___x_2889_;
}
}
else
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
lean_dec(v_a_2884_);
lean_dec_ref(v_allowFailure_2871_);
lean_dec_ref(v_tactic_2870_);
lean_dec_ref(v___x_2869_);
lean_dec(v_goal_2868_);
v_a_2952_ = lean_ctor_get(v___x_2886_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2954_ = v___x_2886_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2886_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2952_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
else
{
lean_object* v_a_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2967_; 
lean_dec_ref(v_allowFailure_2871_);
lean_dec_ref(v_tactic_2870_);
lean_dec_ref(v___x_2869_);
lean_dec(v_goal_2868_);
v_a_2960_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2962_ = v___x_2883_;
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_a_2960_);
lean_dec(v___x_2883_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2965_; 
if (v_isShared_2963_ == 0)
{
v___x_2965_ = v___x_2962_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_a_2960_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
}
v___jp_2880_:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2881_ = lean_box(0);
v___x_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2881_);
return v___x_2882_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__7___boxed(lean_object* v_leavePercentHeartbeats_2968_, lean_object* v_goal_2969_, lean_object* v___x_2970_, lean_object* v_tactic_2971_, lean_object* v_allowFailure_2972_, lean_object* v_collectAll_2973_, lean_object* v_includeStar_2974_, lean_object* v___x_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
uint8_t v_collectAll_boxed_2981_; uint8_t v_includeStar_boxed_2982_; uint8_t v___x_15416__boxed_2983_; lean_object* v_res_2984_; 
v_collectAll_boxed_2981_ = lean_unbox(v_collectAll_2973_);
v_includeStar_boxed_2982_ = lean_unbox(v_includeStar_2974_);
v___x_15416__boxed_2983_ = lean_unbox(v___x_2975_);
v_res_2984_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__7(v_leavePercentHeartbeats_2968_, v_goal_2969_, v___x_2970_, v_tactic_2971_, v_allowFailure_2972_, v_collectAll_boxed_2981_, v_includeStar_boxed_2982_, v___x_15416__boxed_2983_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v_leavePercentHeartbeats_2968_);
return v_res_2984_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0_spec__0(lean_object* v_e_2985_){
_start:
{
if (lean_obj_tag(v_e_2985_) == 0)
{
uint8_t v___x_2986_; 
v___x_2986_ = 2;
return v___x_2986_;
}
else
{
lean_object* v_a_2987_; 
v_a_2987_ = lean_ctor_get(v_e_2985_, 0);
if (lean_obj_tag(v_a_2987_) == 0)
{
uint8_t v___x_2988_; 
v___x_2988_ = 1;
return v___x_2988_;
}
else
{
uint8_t v___x_2989_; 
v___x_2989_ = 0;
return v___x_2989_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0_spec__0___boxed(lean_object* v_e_2990_){
_start:
{
uint8_t v_res_2991_; lean_object* v_r_2992_; 
v_res_2991_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0_spec__0(v_e_2990_);
lean_dec_ref(v_e_2990_);
v_r_2992_ = lean_box(v_res_2991_);
return v_r_2992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0(lean_object* v_cls_2993_, uint8_t v_collapsed_2994_, lean_object* v_tag_2995_, lean_object* v_opts_2996_, uint8_t v_clsEnabled_2997_, lean_object* v_oldTraces_2998_, lean_object* v_msg_2999_, lean_object* v_resStartStop_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
lean_object* v_fst_3006_; lean_object* v_snd_3007_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v_data_3011_; lean_object* v_fst_3022_; lean_object* v_snd_3023_; lean_object* v___x_3024_; uint8_t v___x_3025_; lean_object* v___y_3027_; lean_object* v_a_3028_; uint8_t v___y_3043_; double v___y_3074_; 
v_fst_3006_ = lean_ctor_get(v_resStartStop_3000_, 0);
lean_inc(v_fst_3006_);
v_snd_3007_ = lean_ctor_get(v_resStartStop_3000_, 1);
lean_inc(v_snd_3007_);
lean_dec_ref(v_resStartStop_3000_);
v_fst_3022_ = lean_ctor_get(v_snd_3007_, 0);
lean_inc(v_fst_3022_);
v_snd_3023_ = lean_ctor_get(v_snd_3007_, 1);
lean_inc(v_snd_3023_);
lean_dec(v_snd_3007_);
v___x_3024_ = l_Lean_trace_profiler;
v___x_3025_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_2996_, v___x_3024_);
if (v___x_3025_ == 0)
{
v___y_3043_ = v___x_3025_;
goto v___jp_3042_;
}
else
{
lean_object* v___x_3079_; uint8_t v___x_3080_; 
v___x_3079_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3080_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_2996_, v___x_3079_);
if (v___x_3080_ == 0)
{
lean_object* v___x_3081_; lean_object* v___x_3082_; double v___x_3083_; double v___x_3084_; double v___x_3085_; 
v___x_3081_ = l_Lean_trace_profiler_threshold;
v___x_3082_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_2996_, v___x_3081_);
v___x_3083_ = lean_float_of_nat(v___x_3082_);
v___x_3084_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3);
v___x_3085_ = lean_float_div(v___x_3083_, v___x_3084_);
v___y_3074_ = v___x_3085_;
goto v___jp_3073_;
}
else
{
lean_object* v___x_3086_; lean_object* v___x_3087_; double v___x_3088_; 
v___x_3086_ = l_Lean_trace_profiler_threshold;
v___x_3087_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_2996_, v___x_3086_);
v___x_3088_ = lean_float_of_nat(v___x_3087_);
v___y_3074_ = v___x_3088_;
goto v___jp_3073_;
}
}
v___jp_3008_:
{
lean_object* v___x_3012_; 
lean_inc(v___y_3009_);
v___x_3012_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(v_oldTraces_2998_, v_data_3011_, v___y_3009_, v___y_3010_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v___x_3013_; 
lean_dec_ref_known(v___x_3012_, 1);
v___x_3013_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_3006_);
return v___x_3013_;
}
else
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3021_; 
lean_dec(v_fst_3006_);
v_a_3014_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3016_ = v___x_3012_;
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_3012_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3019_; 
if (v_isShared_3017_ == 0)
{
v___x_3019_ = v___x_3016_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_a_3014_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
v___jp_3026_:
{
uint8_t v_result_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; double v___x_3032_; lean_object* v_data_3033_; 
v_result_3029_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0_spec__0(v_fst_3006_);
v___x_3030_ = lean_box(v_result_3029_);
v___x_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3030_);
v___x_3032_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0);
lean_inc_ref(v_tag_2995_);
lean_inc_ref(v___x_3031_);
lean_inc(v_cls_2993_);
v_data_3033_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3033_, 0, v_cls_2993_);
lean_ctor_set(v_data_3033_, 1, v___x_3031_);
lean_ctor_set(v_data_3033_, 2, v_tag_2995_);
lean_ctor_set_float(v_data_3033_, sizeof(void*)*3, v___x_3032_);
lean_ctor_set_float(v_data_3033_, sizeof(void*)*3 + 8, v___x_3032_);
lean_ctor_set_uint8(v_data_3033_, sizeof(void*)*3 + 16, v_collapsed_2994_);
if (v___x_3025_ == 0)
{
lean_dec_ref_known(v___x_3031_, 1);
lean_dec(v_snd_3023_);
lean_dec(v_fst_3022_);
lean_dec_ref(v_tag_2995_);
lean_dec(v_cls_2993_);
v___y_3009_ = v___y_3027_;
v___y_3010_ = v_a_3028_;
v_data_3011_ = v_data_3033_;
goto v___jp_3008_;
}
else
{
lean_object* v_data_3034_; double v___x_3035_; double v___x_3036_; 
lean_dec_ref_known(v_data_3033_, 3);
v_data_3034_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3034_, 0, v_cls_2993_);
lean_ctor_set(v_data_3034_, 1, v___x_3031_);
lean_ctor_set(v_data_3034_, 2, v_tag_2995_);
v___x_3035_ = lean_unbox_float(v_fst_3022_);
lean_dec(v_fst_3022_);
lean_ctor_set_float(v_data_3034_, sizeof(void*)*3, v___x_3035_);
v___x_3036_ = lean_unbox_float(v_snd_3023_);
lean_dec(v_snd_3023_);
lean_ctor_set_float(v_data_3034_, sizeof(void*)*3 + 8, v___x_3036_);
lean_ctor_set_uint8(v_data_3034_, sizeof(void*)*3 + 16, v_collapsed_2994_);
v___y_3009_ = v___y_3027_;
v___y_3010_ = v_a_3028_;
v_data_3011_ = v_data_3034_;
goto v___jp_3008_;
}
}
v___jp_3037_:
{
lean_object* v_ref_3038_; lean_object* v___x_3039_; 
v_ref_3038_ = lean_ctor_get(v___y_3003_, 5);
lean_inc(v___y_3004_);
lean_inc_ref(v___y_3003_);
lean_inc(v___y_3002_);
lean_inc_ref(v___y_3001_);
lean_inc(v_fst_3006_);
v___x_3039_ = lean_apply_6(v_msg_2999_, v_fst_3006_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, lean_box(0));
if (lean_obj_tag(v___x_3039_) == 0)
{
lean_object* v_a_3040_; 
v_a_3040_ = lean_ctor_get(v___x_3039_, 0);
lean_inc(v_a_3040_);
lean_dec_ref_known(v___x_3039_, 1);
v___y_3027_ = v_ref_3038_;
v_a_3028_ = v_a_3040_;
goto v___jp_3026_;
}
else
{
lean_object* v___x_3041_; 
lean_dec_ref_known(v___x_3039_, 1);
v___x_3041_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2);
v___y_3027_ = v_ref_3038_;
v_a_3028_ = v___x_3041_;
goto v___jp_3026_;
}
}
v___jp_3042_:
{
if (v_clsEnabled_2997_ == 0)
{
if (v___y_3043_ == 0)
{
lean_object* v___x_3044_; lean_object* v_traceState_3045_; lean_object* v_env_3046_; lean_object* v_nextMacroScope_3047_; lean_object* v_ngen_3048_; lean_object* v_auxDeclNGen_3049_; lean_object* v_cache_3050_; lean_object* v_messages_3051_; lean_object* v_infoState_3052_; lean_object* v_snapshotTasks_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3072_; 
lean_dec(v_snd_3023_);
lean_dec(v_fst_3022_);
lean_dec_ref(v_msg_2999_);
lean_dec_ref(v_tag_2995_);
lean_dec(v_cls_2993_);
v___x_3044_ = lean_st_ref_take(v___y_3004_);
v_traceState_3045_ = lean_ctor_get(v___x_3044_, 4);
v_env_3046_ = lean_ctor_get(v___x_3044_, 0);
v_nextMacroScope_3047_ = lean_ctor_get(v___x_3044_, 1);
v_ngen_3048_ = lean_ctor_get(v___x_3044_, 2);
v_auxDeclNGen_3049_ = lean_ctor_get(v___x_3044_, 3);
v_cache_3050_ = lean_ctor_get(v___x_3044_, 5);
v_messages_3051_ = lean_ctor_get(v___x_3044_, 6);
v_infoState_3052_ = lean_ctor_get(v___x_3044_, 7);
v_snapshotTasks_3053_ = lean_ctor_get(v___x_3044_, 8);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3055_ = v___x_3044_;
v_isShared_3056_ = v_isSharedCheck_3072_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_snapshotTasks_3053_);
lean_inc(v_infoState_3052_);
lean_inc(v_messages_3051_);
lean_inc(v_cache_3050_);
lean_inc(v_traceState_3045_);
lean_inc(v_auxDeclNGen_3049_);
lean_inc(v_ngen_3048_);
lean_inc(v_nextMacroScope_3047_);
lean_inc(v_env_3046_);
lean_dec(v___x_3044_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3072_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
uint64_t v_tid_3057_; lean_object* v_traces_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3071_; 
v_tid_3057_ = lean_ctor_get_uint64(v_traceState_3045_, sizeof(void*)*1);
v_traces_3058_ = lean_ctor_get(v_traceState_3045_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v_traceState_3045_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3060_ = v_traceState_3045_;
v_isShared_3061_ = v_isSharedCheck_3071_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_traces_3058_);
lean_dec(v_traceState_3045_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3071_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3062_; lean_object* v___x_3064_; 
v___x_3062_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2998_, v_traces_3058_);
lean_dec_ref(v_traces_3058_);
if (v_isShared_3061_ == 0)
{
lean_ctor_set(v___x_3060_, 0, v___x_3062_);
v___x_3064_ = v___x_3060_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v___x_3062_);
lean_ctor_set_uint64(v_reuseFailAlloc_3070_, sizeof(void*)*1, v_tid_3057_);
v___x_3064_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
lean_object* v___x_3066_; 
if (v_isShared_3056_ == 0)
{
lean_ctor_set(v___x_3055_, 4, v___x_3064_);
v___x_3066_ = v___x_3055_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_env_3046_);
lean_ctor_set(v_reuseFailAlloc_3069_, 1, v_nextMacroScope_3047_);
lean_ctor_set(v_reuseFailAlloc_3069_, 2, v_ngen_3048_);
lean_ctor_set(v_reuseFailAlloc_3069_, 3, v_auxDeclNGen_3049_);
lean_ctor_set(v_reuseFailAlloc_3069_, 4, v___x_3064_);
lean_ctor_set(v_reuseFailAlloc_3069_, 5, v_cache_3050_);
lean_ctor_set(v_reuseFailAlloc_3069_, 6, v_messages_3051_);
lean_ctor_set(v_reuseFailAlloc_3069_, 7, v_infoState_3052_);
lean_ctor_set(v_reuseFailAlloc_3069_, 8, v_snapshotTasks_3053_);
v___x_3066_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3067_ = lean_st_ref_set(v___y_3004_, v___x_3066_);
v___x_3068_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_3006_);
return v___x_3068_;
}
}
}
}
}
else
{
goto v___jp_3037_;
}
}
else
{
goto v___jp_3037_;
}
}
v___jp_3073_:
{
double v___x_3075_; double v___x_3076_; double v___x_3077_; uint8_t v___x_3078_; 
v___x_3075_ = lean_unbox_float(v_snd_3023_);
v___x_3076_ = lean_unbox_float(v_fst_3022_);
v___x_3077_ = lean_float_sub(v___x_3075_, v___x_3076_);
v___x_3078_ = lean_float_decLt(v___y_3074_, v___x_3077_);
v___y_3043_ = v___x_3078_;
goto v___jp_3042_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___boxed(lean_object* v_cls_3089_, lean_object* v_collapsed_3090_, lean_object* v_tag_3091_, lean_object* v_opts_3092_, lean_object* v_clsEnabled_3093_, lean_object* v_oldTraces_3094_, lean_object* v_msg_3095_, lean_object* v_resStartStop_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_){
_start:
{
uint8_t v_collapsed_boxed_3102_; uint8_t v_clsEnabled_boxed_3103_; lean_object* v_res_3104_; 
v_collapsed_boxed_3102_ = lean_unbox(v_collapsed_3090_);
v_clsEnabled_boxed_3103_ = lean_unbox(v_clsEnabled_3093_);
v_res_3104_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0(v_cls_3089_, v_collapsed_boxed_3102_, v_tag_3091_, v_opts_3092_, v_clsEnabled_boxed_3103_, v_oldTraces_3094_, v_msg_3095_, v_resStartStop_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
lean_dec_ref(v_opts_3092_);
return v_res_3104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(lean_object* v_goal_3108_, lean_object* v_tactic_3109_, lean_object* v_allowFailure_3110_, lean_object* v_leavePercentHeartbeats_3111_, uint8_t v_includeStar_3112_, uint8_t v_collectAll_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_){
_start:
{
lean_object* v_options_3119_; lean_object* v_inheritedTraceOptions_3120_; uint8_t v_hasTrace_3121_; lean_object* v___x_3122_; uint8_t v___x_3123_; 
v_options_3119_ = lean_ctor_get(v_a_3116_, 2);
v_inheritedTraceOptions_3120_ = lean_ctor_get(v_a_3116_, 13);
v_hasTrace_3121_ = lean_ctor_get_uint8(v_options_3119_, sizeof(void*)*1);
v___x_3122_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_3123_ = lean_bool_not(v_hasTrace_3121_);
if (v___x_3123_ == 0)
{
lean_object* v___f_3124_; lean_object* v___x_3125_; uint8_t v___x_3126_; lean_object* v___x_3127_; lean_object* v___y_3129_; lean_object* v___y_3130_; uint8_t v___y_3131_; lean_object* v_a_3132_; lean_object* v___y_3145_; lean_object* v___y_3146_; uint8_t v___y_3147_; lean_object* v_a_3148_; uint8_t v___y_3158_; uint8_t v_a_3214_; 
lean_inc(v_goal_3108_);
v___f_3124_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3124_, 0, v_goal_3108_);
v___x_3125_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_3126_ = 1;
v___x_3127_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__4));
if (v_hasTrace_3121_ == 0)
{
v_a_3214_ = v_hasTrace_3121_;
goto v___jp_3213_;
}
else
{
lean_object* v___x_3224_; uint8_t v___x_3225_; 
v___x_3224_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3);
v___x_3225_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3120_, v_options_3119_, v___x_3224_);
if (v___x_3225_ == 0)
{
v_a_3214_ = v___x_3225_;
goto v___jp_3213_;
}
else
{
v___y_3158_ = v___x_3225_;
goto v___jp_3157_;
}
}
v___jp_3128_:
{
lean_object* v___x_3133_; double v___x_3134_; double v___x_3135_; double v___x_3136_; double v___x_3137_; double v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3133_ = lean_io_mono_nanos_now();
v___x_3134_ = lean_float_of_nat(v___y_3129_);
v___x_3135_ = lean_float_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__0, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__0_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__0);
v___x_3136_ = lean_float_div(v___x_3134_, v___x_3135_);
v___x_3137_ = lean_float_of_nat(v___x_3133_);
v___x_3138_ = lean_float_div(v___x_3137_, v___x_3135_);
v___x_3139_ = lean_box_float(v___x_3136_);
v___x_3140_ = lean_box_float(v___x_3138_);
v___x_3141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3139_);
lean_ctor_set(v___x_3141_, 1, v___x_3140_);
v___x_3142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3142_, 0, v_a_3132_);
lean_ctor_set(v___x_3142_, 1, v___x_3141_);
v___x_3143_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0(v___x_3125_, v___x_3126_, v___x_3127_, v_options_3119_, v___y_3131_, v___y_3130_, v___f_3124_, v___x_3142_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_);
return v___x_3143_;
}
v___jp_3144_:
{
lean_object* v___x_3149_; double v___x_3150_; double v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
v___x_3149_ = lean_io_get_num_heartbeats();
v___x_3150_ = lean_float_of_nat(v___y_3145_);
v___x_3151_ = lean_float_of_nat(v___x_3149_);
v___x_3152_ = lean_box_float(v___x_3150_);
v___x_3153_ = lean_box_float(v___x_3151_);
v___x_3154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3152_);
lean_ctor_set(v___x_3154_, 1, v___x_3153_);
v___x_3155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3155_, 0, v_a_3148_);
lean_ctor_set(v___x_3155_, 1, v___x_3154_);
v___x_3156_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0(v___x_3125_, v___x_3126_, v___x_3127_, v_options_3119_, v___y_3147_, v___y_3146_, v___f_3124_, v___x_3155_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_);
return v___x_3156_;
}
v___jp_3157_:
{
lean_object* v___x_3159_; lean_object* v_a_3160_; lean_object* v___x_3161_; uint8_t v___x_3162_; 
v___x_3159_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v_a_3117_);
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
lean_inc(v_a_3160_);
lean_dec_ref(v___x_3159_);
v___x_3161_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3162_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_3119_, v___x_3161_);
if (v___x_3162_ == 0)
{
lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___f_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3163_ = lean_io_mono_nanos_now();
v___x_3164_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___closed__0));
v___x_3165_ = lean_box(v_collectAll_3113_);
v___x_3166_ = lean_box(v_includeStar_3112_);
v___x_3167_ = lean_box(v___x_3162_);
v___f_3168_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2___boxed), 13, 8);
lean_closure_set(v___f_3168_, 0, v_leavePercentHeartbeats_3111_);
lean_closure_set(v___f_3168_, 1, v_goal_3108_);
lean_closure_set(v___f_3168_, 2, v___x_3164_);
lean_closure_set(v___f_3168_, 3, v_tactic_3109_);
lean_closure_set(v___f_3168_, 4, v_allowFailure_3110_);
lean_closure_set(v___f_3168_, 5, v___x_3165_);
lean_closure_set(v___f_3168_, 6, v___x_3166_);
lean_closure_set(v___f_3168_, 7, v___x_3167_);
v___x_3169_ = lean_box(0);
v___x_3170_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4___redArg(v___x_3122_, v_options_3119_, v___f_3168_, v___x_3169_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_);
if (lean_obj_tag(v___x_3170_) == 0)
{
lean_object* v_a_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3178_; 
v_a_3171_ = lean_ctor_get(v___x_3170_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3170_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3173_ = v___x_3170_;
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_a_3171_);
lean_dec(v___x_3170_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3176_; 
if (v_isShared_3174_ == 0)
{
lean_ctor_set_tag(v___x_3173_, 1);
v___x_3176_ = v___x_3173_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_a_3171_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
v___y_3129_ = v___x_3163_;
v___y_3130_ = v_a_3160_;
v___y_3131_ = v___y_3158_;
v_a_3132_ = v___x_3176_;
goto v___jp_3128_;
}
}
}
else
{
lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3186_; 
v_a_3179_ = lean_ctor_get(v___x_3170_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3170_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3181_ = v___x_3170_;
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_dec(v___x_3170_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3184_; 
if (v_isShared_3182_ == 0)
{
lean_ctor_set_tag(v___x_3181_, 0);
v___x_3184_ = v___x_3181_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_a_3179_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
v___y_3129_ = v___x_3163_;
v___y_3130_ = v_a_3160_;
v___y_3131_ = v___y_3158_;
v_a_3132_ = v___x_3184_;
goto v___jp_3128_;
}
}
}
}
else
{
lean_object* v___x_3187_; uint8_t v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___f_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3187_ = lean_io_get_num_heartbeats();
v___x_3188_ = 0;
v___x_3189_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3189_, 0, v___x_3188_);
lean_ctor_set_uint8(v___x_3189_, 1, v___x_3162_);
lean_ctor_set_uint8(v___x_3189_, 2, v___x_3162_);
lean_ctor_set_uint8(v___x_3189_, 3, v___x_3162_);
v___x_3190_ = lean_box(v_collectAll_3113_);
v___x_3191_ = lean_box(v_includeStar_3112_);
v___x_3192_ = lean_box(v___x_3162_);
v___x_3193_ = lean_box(v___x_3123_);
v___f_3194_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4___boxed), 14, 9);
lean_closure_set(v___f_3194_, 0, v_leavePercentHeartbeats_3111_);
lean_closure_set(v___f_3194_, 1, v_goal_3108_);
lean_closure_set(v___f_3194_, 2, v___x_3189_);
lean_closure_set(v___f_3194_, 3, v_tactic_3109_);
lean_closure_set(v___f_3194_, 4, v_allowFailure_3110_);
lean_closure_set(v___f_3194_, 5, v___x_3190_);
lean_closure_set(v___f_3194_, 6, v___x_3191_);
lean_closure_set(v___f_3194_, 7, v___x_3192_);
lean_closure_set(v___f_3194_, 8, v___x_3193_);
v___x_3195_ = lean_box(0);
v___x_3196_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4___redArg(v___x_3122_, v_options_3119_, v___f_3194_, v___x_3195_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3204_; 
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3199_ = v___x_3196_;
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___x_3196_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3202_; 
if (v_isShared_3200_ == 0)
{
lean_ctor_set_tag(v___x_3199_, 1);
v___x_3202_ = v___x_3199_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_a_3197_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
v___y_3145_ = v___x_3187_;
v___y_3146_ = v_a_3160_;
v___y_3147_ = v___y_3158_;
v_a_3148_ = v___x_3202_;
goto v___jp_3144_;
}
}
}
else
{
lean_object* v_a_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3212_; 
v_a_3205_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3207_ = v___x_3196_;
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_a_3205_);
lean_dec(v___x_3196_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3210_; 
if (v_isShared_3208_ == 0)
{
lean_ctor_set_tag(v___x_3207_, 0);
v___x_3210_ = v___x_3207_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_a_3205_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
v___y_3145_ = v___x_3187_;
v___y_3146_ = v_a_3160_;
v___y_3147_ = v___y_3158_;
v_a_3148_ = v___x_3210_;
goto v___jp_3144_;
}
}
}
}
}
v___jp_3213_:
{
lean_object* v___x_3215_; uint8_t v___x_3216_; 
v___x_3215_ = l_Lean_trace_profiler;
v___x_3216_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_3119_, v___x_3215_);
if (v___x_3216_ == 0)
{
lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___f_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
lean_dec_ref(v___f_3124_);
v___x_3217_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___closed__0));
v___x_3218_ = lean_box(v_collectAll_3113_);
v___x_3219_ = lean_box(v_includeStar_3112_);
v___x_3220_ = lean_box(v___x_3216_);
v___f_3221_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2___boxed), 13, 8);
lean_closure_set(v___f_3221_, 0, v_leavePercentHeartbeats_3111_);
lean_closure_set(v___f_3221_, 1, v_goal_3108_);
lean_closure_set(v___f_3221_, 2, v___x_3217_);
lean_closure_set(v___f_3221_, 3, v_tactic_3109_);
lean_closure_set(v___f_3221_, 4, v_allowFailure_3110_);
lean_closure_set(v___f_3221_, 5, v___x_3218_);
lean_closure_set(v___f_3221_, 6, v___x_3219_);
lean_closure_set(v___f_3221_, 7, v___x_3220_);
v___x_3222_ = lean_box(0);
v___x_3223_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4___redArg(v___x_3122_, v_options_3119_, v___f_3221_, v___x_3222_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_);
return v___x_3223_;
}
else
{
v___y_3158_ = v_a_3214_;
goto v___jp_3157_;
}
}
}
else
{
uint8_t v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___f_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
v___x_3226_ = 0;
v___x_3227_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3227_, 0, v___x_3226_);
lean_ctor_set_uint8(v___x_3227_, 1, v___x_3123_);
lean_ctor_set_uint8(v___x_3227_, 2, v___x_3123_);
lean_ctor_set_uint8(v___x_3227_, 3, v___x_3123_);
v___x_3228_ = lean_box(v_collectAll_3113_);
v___x_3229_ = lean_box(v_includeStar_3112_);
v___x_3230_ = lean_box(v___x_3123_);
v___f_3231_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__7___boxed), 13, 8);
lean_closure_set(v___f_3231_, 0, v_leavePercentHeartbeats_3111_);
lean_closure_set(v___f_3231_, 1, v_goal_3108_);
lean_closure_set(v___f_3231_, 2, v___x_3227_);
lean_closure_set(v___f_3231_, 3, v_tactic_3109_);
lean_closure_set(v___f_3231_, 4, v_allowFailure_3110_);
lean_closure_set(v___f_3231_, 5, v___x_3228_);
lean_closure_set(v___f_3231_, 6, v___x_3229_);
lean_closure_set(v___f_3231_, 7, v___x_3230_);
v___x_3232_ = lean_box(0);
v___x_3233_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4___redArg(v___x_3122_, v_options_3119_, v___f_3231_, v___x_3232_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_);
return v___x_3233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___boxed(lean_object* v_goal_3234_, lean_object* v_tactic_3235_, lean_object* v_allowFailure_3236_, lean_object* v_leavePercentHeartbeats_3237_, lean_object* v_includeStar_3238_, lean_object* v_collectAll_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_){
_start:
{
uint8_t v_includeStar_boxed_3245_; uint8_t v_collectAll_boxed_3246_; lean_object* v_res_3247_; 
v_includeStar_boxed_3245_ = lean_unbox(v_includeStar_3238_);
v_collectAll_boxed_3246_ = lean_unbox(v_collectAll_3239_);
v_res_3247_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(v_goal_3234_, v_tactic_3235_, v_allowFailure_3236_, v_leavePercentHeartbeats_3237_, v_includeStar_boxed_3245_, v_collectAll_boxed_3246_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_);
lean_dec(v_a_3243_);
lean_dec_ref(v_a_3242_);
lean_dec(v_a_3241_);
lean_dec_ref(v_a_3240_);
return v_res_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearch(lean_object* v_goal_3248_, lean_object* v_tactic_3249_, lean_object* v_allowFailure_3250_, lean_object* v_leavePercentHeartbeats_3251_, uint8_t v_includeStar_3252_, uint8_t v_collectAll_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_){
_start:
{
lean_object* v___x_3259_; 
v___x_3259_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(v_goal_3248_, v_tactic_3249_, v_allowFailure_3250_, v_leavePercentHeartbeats_3251_, v_includeStar_3252_, v_collectAll_3253_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearch___boxed(lean_object* v_goal_3260_, lean_object* v_tactic_3261_, lean_object* v_allowFailure_3262_, lean_object* v_leavePercentHeartbeats_3263_, lean_object* v_includeStar_3264_, lean_object* v_collectAll_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_){
_start:
{
uint8_t v_includeStar_boxed_3271_; uint8_t v_collectAll_boxed_3272_; lean_object* v_res_3273_; 
v_includeStar_boxed_3271_ = lean_unbox(v_includeStar_3264_);
v_collectAll_boxed_3272_ = lean_unbox(v_collectAll_3265_);
v_res_3273_ = l_Lean_Meta_LibrarySearch_librarySearch(v_goal_3260_, v_tactic_3261_, v_allowFailure_3262_, v_leavePercentHeartbeats_3263_, v_includeStar_boxed_3271_, v_collectAll_boxed_3272_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_);
lean_dec(v_a_3269_);
lean_dec_ref(v_a_3268_);
lean_dec(v_a_3267_);
lean_dec_ref(v_a_3266_);
return v_res_3273_;
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
