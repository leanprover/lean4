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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
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
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Linter_isDeprecated(lean_object*, lean_object*);
uint8_t l_Lean_Name_isMetaprogramming(lean_object*);
lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
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
static const lean_ctor_object l_Lean_Meta_LibrarySearch_grindDischarger___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*12 + 32, .m_other = 12, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1)),((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1048576) << 1) | 1)),((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 0, 1, 0, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 1, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 1, 0, 1, 1)}};
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_641666102____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_641666102____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_defaultLibSearchState;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_instInhabitedLibSearchState;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___lam__0_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___lam__0_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___lam__0_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___lam__0_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___lam__0_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___lam__0_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_starLemmasExt;
static const lean_closure_object l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__0 = (const lean_object*)&l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__0_value;
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___x_169_);
v___x_171_ = l_Lean_Meta_getLevel(v_a_170_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
if (lean_obj_tag(v___x_171_) == 0)
{
lean_object* v_a_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_a_172_ = lean_ctor_get(v___x_171_, 0);
lean_inc(v_a_172_);
lean_dec_ref(v___x_171_);
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
lean_dec_ref(v___x_180_);
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
lean_dec_ref(v_a_181_);
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
lean_dec_ref(v___x_190_);
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
lean_dec_ref(v___x_185_);
v_a_155_ = v_a_208_;
goto v___jp_154_;
}
}
else
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_Meta_LibrarySearch_grindDischarger___lam__0(v_a_181_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
lean_dec_ref(v_a_181_);
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
lean_dec_ref(v___x_180_);
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
lean_dec_ref(v___x_171_);
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
lean_dec_ref(v___x_169_);
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
lean_dec_ref(v___x_291_);
v___x_293_ = l_Lean_Meta_getLevel(v_a_292_, v_a_265_, v_a_266_, v_a_267_, v_a_268_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_a_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v_a_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_a_294_);
lean_dec_ref(v___x_293_);
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
lean_dec_ref(v___x_331_);
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
lean_dec_ref(v_a_304_);
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
lean_dec_ref(v___x_303_);
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
lean_dec_ref(v___x_293_);
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
lean_dec_ref(v___x_291_);
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
lean_dec_ref(v___x_492_);
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
lean_dec_ref(v___x_775_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport(lean_object* v_name_827_, lean_object* v_constInfo_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_){
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
lean_object* v___f_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___f_838_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___boxed), 8, 1);
lean_closure_set(v___f_838_, 0, v_name_827_);
v___x_839_ = l_Lean_ConstantInfo_type(v_constInfo_828_);
v___x_840_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(v___x_839_, v___f_838_, v___x_837_, v_a_829_, v_a_830_, v_a_831_, v_a_832_);
return v___x_840_;
}
else
{
lean_object* v___x_841_; lean_object* v___x_842_; 
lean_dec(v_name_827_);
v___x_841_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___closed__0));
v___x_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
return v___x_842_;
}
}
else
{
lean_object* v___x_843_; lean_object* v___x_844_; 
lean_dec(v_name_827_);
v___x_843_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___closed__0));
v___x_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_844_, 0, v___x_843_);
return v___x_844_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___boxed(lean_object* v_name_845_, lean_object* v_constInfo_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport(v_name_845_, v_constInfo_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_);
lean_dec(v_a_850_);
lean_dec_ref(v_a_849_);
lean_dec(v_a_848_);
lean_dec_ref(v_a_847_);
lean_dec_ref(v_constInfo_846_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_641666102____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_854_ = lean_box(0);
v___x_855_ = lean_st_mk_ref(v___x_854_);
v___x_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_641666102____hygCtx___hyg_2____boxed(lean_object* v_a_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_641666102____hygCtx___hyg_2_();
return v_res_858_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_instInhabitedLibSearchState(void){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_defaultLibSearchState;
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___lam__0_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2_(lean_object* v___x_860_){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_st_mk_ref(v___x_860_);
v___x_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___lam__0_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2____boxed(lean_object* v___x_864_, lean_object* v___y_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___lam__0_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2_(v___x_864_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_870_; lean_object* v___f_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_870_ = lean_box(0);
v___f_871_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2_));
v___x_872_ = lean_box(2);
v___x_873_ = l_Lean_registerEnvExtension___redArg(v___f_871_, v___x_870_, v___x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2____boxed(lean_object* v_a_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2_();
return v_res_875_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_constantsPerImportTask(void){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = lean_unsigned_to_nat(6500u);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___lam__0_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2_(lean_object* v___x_902_){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = lean_st_mk_ref(v___x_902_);
v___x_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___lam__0_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2____boxed(lean_object* v___x_906_, lean_object* v___y_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___lam__0_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2_(v___x_906_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_912_; lean_object* v___f_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_912_ = lean_box(0);
v___f_913_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2_));
v___x_914_ = lean_box(2);
v___x_915_ = l_Lean_registerEnvExtension___redArg(v___f_913_, v___x_912_, v___x_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2____boxed(lean_object* v_a_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2_();
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_libSearchFindDecls(lean_object* v_ty_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v_env_928_; lean_object* v___x_929_; lean_object* v_asyncMode_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_925_ = lean_box(0);
v___x_926_ = lean_st_mk_ref(v___x_925_);
v___x_927_ = lean_st_ref_get(v_a_923_);
v_env_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc_ref(v_env_928_);
lean_dec(v___x_927_);
v___x_929_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_starLemmasExt;
v_asyncMode_930_ = lean_ctor_get(v___x_929_, 2);
v___x_931_ = lean_box(0);
v___x_932_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_926_, v___x_929_, v_env_928_, v_asyncMode_930_, v___x_931_);
lean_dec(v___x_926_);
v___x_933_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_ext;
v___x_934_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__0));
v___x_935_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_droppedKeys));
v___x_936_ = lean_unsigned_to_nat(6500u);
v___x_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_937_, 0, v___x_932_);
v___x_938_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v___x_933_, v___x_934_, v___x_935_, v___x_936_, v___x_937_, v_ty_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_);
return v___x_938_;
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_getStarLemmas(lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v_env_962_; lean_object* v___x_963_; lean_object* v_asyncMode_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_959_ = lean_box(0);
v___x_960_ = lean_st_mk_ref(v___x_959_);
v___x_961_ = lean_st_ref_get(v_a_957_);
v_env_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc_ref(v_env_962_);
lean_dec(v___x_961_);
v___x_963_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_starLemmasExt;
v_asyncMode_964_ = lean_ctor_get(v___x_963_, 2);
v___x_965_ = lean_box(0);
v___x_966_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_960_, v___x_963_, v_env_962_, v_asyncMode_964_, v___x_965_);
lean_dec(v___x_960_);
v___x_967_ = lean_st_ref_get(v___x_966_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2, &l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2_once, _init_l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2);
v___x_969_ = l_Lean_Meta_LibrarySearch_libSearchFindDecls(v___x_968_, v_a_954_, v_a_955_, v_a_956_, v_a_957_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_982_; 
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_982_ == 0)
{
lean_object* v_unused_983_; 
v_unused_983_ = lean_ctor_get(v___x_969_, 0);
lean_dec(v_unused_983_);
v___x_971_ = v___x_969_;
v_isShared_972_ = v_isSharedCheck_982_;
goto v_resetjp_970_;
}
else
{
lean_dec(v___x_969_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_982_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; 
v___x_973_ = lean_st_ref_get(v___x_966_);
lean_dec(v___x_966_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v___x_974_; lean_object* v___x_976_; 
v___x_974_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_getStarLemmas___closed__3));
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
else
{
lean_object* v_val_978_; lean_object* v___x_980_; 
v_val_978_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_val_978_);
lean_dec_ref(v___x_973_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v_val_978_);
v___x_980_ = v___x_971_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_val_978_);
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
lean_dec(v___x_966_);
return v___x_969_;
}
}
else
{
lean_object* v_val_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_dec(v___x_966_);
v_val_984_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_967_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_val_984_);
lean_dec(v___x_967_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
lean_ctor_set_tag(v___x_986_, 0);
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_val_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_getStarLemmas___boxed(lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v_a_992_, v_a_993_, v_a_994_, v_a_995_);
lean_dec(v_a_995_);
lean_dec_ref(v_a_994_);
lean_dec(v_a_993_);
lean_dec_ref(v_a_992_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0(uint8_t v___x_998_, lean_object* v___x_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
if (v___x_998_ == 0)
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Lean_getRemainingHeartbeats___redArg(v___y_1002_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1015_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1015_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1015_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
uint8_t v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1013_; 
v___x_1010_ = lean_nat_dec_lt(v_a_1006_, v___x_999_);
lean_dec(v_a_1006_);
v___x_1011_ = lean_box(v___x_1010_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1011_);
v___x_1013_ = v___x_1008_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1011_);
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
v_a_1016_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_1005_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_1005_);
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
uint8_t v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1024_ = 0;
v___x_1025_ = lean_box(v___x_1024_);
v___x_1026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
return v___x_1026_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0___boxed(lean_object* v___x_1027_, lean_object* v___x_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
uint8_t v___x_643__boxed_1034_; lean_object* v_res_1035_; 
v___x_643__boxed_1034_ = lean_unbox(v___x_1027_);
v_res_1035_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0(v___x_643__boxed_1034_, v___x_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___x_1028_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(lean_object* v_leavePercent_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Lean_getMaxHeartbeats___redArg(v_a_1037_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v___x_1041_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_a_1040_);
lean_dec_ref(v___x_1039_);
v___x_1041_ = l_Lean_getRemainingHeartbeats___redArg(v_a_1037_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1056_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1044_ = v___x_1041_;
v_isShared_1045_ = v_isSharedCheck_1056_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1041_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1056_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; uint8_t v___x_1050_; lean_object* v___x_1051_; lean_object* v___y_1052_; lean_object* v___x_1054_; 
v___x_1046_ = lean_nat_mul(v_a_1042_, v_leavePercent_1036_);
lean_dec(v_a_1042_);
v___x_1047_ = lean_unsigned_to_nat(100u);
v___x_1048_ = lean_nat_div(v___x_1046_, v___x_1047_);
lean_dec(v___x_1046_);
v___x_1049_ = lean_unsigned_to_nat(0u);
v___x_1050_ = lean_nat_dec_eq(v_a_1040_, v___x_1049_);
lean_dec(v_a_1040_);
v___x_1051_ = lean_box(v___x_1050_);
v___y_1052_ = lean_alloc_closure((void*)(l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___y_1052_, 0, v___x_1051_);
lean_closure_set(v___y_1052_, 1, v___x_1048_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 0, v___y_1052_);
v___x_1054_ = v___x_1044_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___y_1052_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
lean_dec(v_a_1040_);
v_a_1057_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v___x_1041_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1041_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
v_a_1065_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___x_1039_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1039_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1065_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___boxed(lean_object* v_leavePercent_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercent_1073_, v_a_1074_);
lean_dec_ref(v_a_1074_);
lean_dec(v_leavePercent_1073_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck(lean_object* v_leavePercent_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_){
_start:
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercent_1077_, v_a_1080_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___boxed(lean_object* v_leavePercent_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck(v_leavePercent_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
lean_dec(v_a_1088_);
lean_dec_ref(v_a_1087_);
lean_dec(v_a_1086_);
lean_dec_ref(v_a_1085_);
lean_dec(v_leavePercent_1084_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(lean_object* v_upperBound_1091_, lean_object* v_x_1092_, lean_object* v_f_1093_, lean_object* v_y_1094_, lean_object* v_g_1095_, lean_object* v_a_1096_, lean_object* v_b_1097_){
_start:
{
uint8_t v___x_1098_; 
v___x_1098_ = lean_nat_dec_lt(v_a_1096_, v_upperBound_1091_);
if (v___x_1098_ == 0)
{
lean_dec(v_a_1096_);
lean_dec(v_g_1095_);
lean_dec(v_f_1093_);
return v_b_1097_;
}
else
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1099_ = lean_array_fget_borrowed(v_x_1092_, v_a_1096_);
lean_inc(v_f_1093_);
lean_inc(v___x_1099_);
v___x_1100_ = lean_apply_1(v_f_1093_, v___x_1099_);
v___x_1101_ = lean_array_push(v_b_1097_, v___x_1100_);
v___x_1102_ = lean_array_fget_borrowed(v_y_1094_, v_a_1096_);
lean_inc(v_g_1095_);
lean_inc(v___x_1102_);
v___x_1103_ = lean_apply_1(v_g_1095_, v___x_1102_);
v___x_1104_ = lean_array_push(v___x_1101_, v___x_1103_);
v___x_1105_ = lean_unsigned_to_nat(1u);
v___x_1106_ = lean_nat_add(v_a_1096_, v___x_1105_);
lean_dec(v_a_1096_);
v_a_1096_ = v___x_1106_;
v_b_1097_ = v___x_1104_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg___boxed(lean_object* v_upperBound_1108_, lean_object* v_x_1109_, lean_object* v_f_1110_, lean_object* v_y_1111_, lean_object* v_g_1112_, lean_object* v_a_1113_, lean_object* v_b_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(v_upperBound_1108_, v_x_1109_, v_f_1110_, v_y_1111_, v_g_1112_, v_a_1113_, v_b_1114_);
lean_dec_ref(v_y_1111_);
lean_dec_ref(v_x_1109_);
lean_dec(v_upperBound_1108_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(lean_object* v_g_1116_, size_t v_sz_1117_, size_t v_i_1118_, lean_object* v_bs_1119_){
_start:
{
uint8_t v___x_1120_; 
v___x_1120_ = lean_usize_dec_lt(v_i_1118_, v_sz_1117_);
if (v___x_1120_ == 0)
{
lean_dec(v_g_1116_);
return v_bs_1119_;
}
else
{
lean_object* v_v_1121_; lean_object* v___x_1122_; lean_object* v_bs_x27_1123_; lean_object* v___x_1124_; size_t v___x_1125_; size_t v___x_1126_; lean_object* v___x_1127_; 
v_v_1121_ = lean_array_uget(v_bs_1119_, v_i_1118_);
v___x_1122_ = lean_unsigned_to_nat(0u);
v_bs_x27_1123_ = lean_array_uset(v_bs_1119_, v_i_1118_, v___x_1122_);
lean_inc(v_g_1116_);
v___x_1124_ = lean_apply_1(v_g_1116_, v_v_1121_);
v___x_1125_ = ((size_t)1ULL);
v___x_1126_ = lean_usize_add(v_i_1118_, v___x_1125_);
v___x_1127_ = lean_array_uset(v_bs_x27_1123_, v_i_1118_, v___x_1124_);
v_i_1118_ = v___x_1126_;
v_bs_1119_ = v___x_1127_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg___boxed(lean_object* v_g_1129_, lean_object* v_sz_1130_, lean_object* v_i_1131_, lean_object* v_bs_1132_){
_start:
{
size_t v_sz_boxed_1133_; size_t v_i_boxed_1134_; lean_object* v_res_1135_; 
v_sz_boxed_1133_ = lean_unbox_usize(v_sz_1130_);
lean_dec(v_sz_1130_);
v_i_boxed_1134_ = lean_unbox_usize(v_i_1131_);
lean_dec(v_i_1131_);
v_res_1135_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_g_1129_, v_sz_boxed_1133_, v_i_boxed_1134_, v_bs_1132_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith___redArg(lean_object* v_f_1136_, lean_object* v_x_1137_, lean_object* v_g_1138_, lean_object* v_y_1139_){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v_res_1143_; lean_object* v___y_1145_; uint8_t v___x_1159_; 
v___x_1140_ = lean_array_get_size(v_x_1137_);
v___x_1141_ = lean_array_get_size(v_y_1139_);
v___x_1142_ = lean_nat_add(v___x_1140_, v___x_1141_);
v_res_1143_ = lean_mk_empty_array_with_capacity(v___x_1142_);
lean_dec(v___x_1142_);
v___x_1159_ = lean_nat_dec_le(v___x_1140_, v___x_1141_);
if (v___x_1159_ == 0)
{
v___y_1145_ = v___x_1141_;
goto v___jp_1144_;
}
else
{
v___y_1145_ = v___x_1140_;
goto v___jp_1144_;
}
v___jp_1144_:
{
uint8_t v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1146_ = lean_nat_dec_lt(v___y_1145_, v___x_1140_);
v___x_1147_ = lean_unsigned_to_nat(0u);
lean_inc(v_g_1138_);
lean_inc(v_f_1136_);
v___x_1148_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(v___y_1145_, v_x_1137_, v_f_1136_, v_y_1139_, v_g_1138_, v___x_1147_, v_res_1143_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1149_; size_t v_sz_1150_; size_t v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
lean_dec(v_f_1136_);
v___x_1149_ = l_Array_extract___redArg(v_y_1139_, v___y_1145_, v___x_1141_);
v_sz_1150_ = lean_array_size(v___x_1149_);
v___x_1151_ = ((size_t)0ULL);
v___x_1152_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_g_1138_, v_sz_1150_, v___x_1151_, v___x_1149_);
v___x_1153_ = l_Array_append___redArg(v___x_1148_, v___x_1152_);
lean_dec_ref(v___x_1152_);
return v___x_1153_;
}
else
{
lean_object* v___x_1154_; size_t v_sz_1155_; size_t v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
lean_dec(v_g_1138_);
v___x_1154_ = l_Array_extract___redArg(v_x_1137_, v___y_1145_, v___x_1140_);
v_sz_1155_ = lean_array_size(v___x_1154_);
v___x_1156_ = ((size_t)0ULL);
v___x_1157_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_f_1136_, v_sz_1155_, v___x_1156_, v___x_1154_);
v___x_1158_ = l_Array_append___redArg(v___x_1148_, v___x_1157_);
lean_dec_ref(v___x_1157_);
return v___x_1158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith___redArg___boxed(lean_object* v_f_1160_, lean_object* v_x_1161_, lean_object* v_g_1162_, lean_object* v_y_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lean_Meta_LibrarySearch_interleaveWith___redArg(v_f_1160_, v_x_1161_, v_g_1162_, v_y_1163_);
lean_dec_ref(v_y_1163_);
lean_dec_ref(v_x_1161_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith(lean_object* v_00_u03b1_1165_, lean_object* v_00_u03b2_1166_, lean_object* v_00_u03b3_1167_, lean_object* v_f_1168_, lean_object* v_x_1169_, lean_object* v_g_1170_, lean_object* v_y_1171_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = l_Lean_Meta_LibrarySearch_interleaveWith___redArg(v_f_1168_, v_x_1169_, v_g_1170_, v_y_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith___boxed(lean_object* v_00_u03b1_1173_, lean_object* v_00_u03b2_1174_, lean_object* v_00_u03b3_1175_, lean_object* v_f_1176_, lean_object* v_x_1177_, lean_object* v_g_1178_, lean_object* v_y_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Lean_Meta_LibrarySearch_interleaveWith(v_00_u03b1_1173_, v_00_u03b2_1174_, v_00_u03b3_1175_, v_f_1176_, v_x_1177_, v_g_1178_, v_y_1179_);
lean_dec_ref(v_y_1179_);
lean_dec_ref(v_x_1177_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0(lean_object* v_00_u03b2_1181_, lean_object* v_00_u03b3_1182_, lean_object* v_g_1183_, size_t v_sz_1184_, size_t v_i_1185_, lean_object* v_bs_1186_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_g_1183_, v_sz_1184_, v_i_1185_, v_bs_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___boxed(lean_object* v_00_u03b2_1188_, lean_object* v_00_u03b3_1189_, lean_object* v_g_1190_, lean_object* v_sz_1191_, lean_object* v_i_1192_, lean_object* v_bs_1193_){
_start:
{
size_t v_sz_boxed_1194_; size_t v_i_boxed_1195_; lean_object* v_res_1196_; 
v_sz_boxed_1194_ = lean_unbox_usize(v_sz_1191_);
lean_dec(v_sz_1191_);
v_i_boxed_1195_ = lean_unbox_usize(v_i_1192_);
lean_dec(v_i_1192_);
v_res_1196_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0(v_00_u03b2_1188_, v_00_u03b3_1189_, v_g_1190_, v_sz_boxed_1194_, v_i_boxed_1195_, v_bs_1193_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1(lean_object* v_00_u03b3_1197_, lean_object* v_upperBound_1198_, lean_object* v_00_u03b1_1199_, lean_object* v_x_1200_, lean_object* v_f_1201_, lean_object* v_00_u03b2_1202_, lean_object* v_y_1203_, lean_object* v_g_1204_, lean_object* v_inst_1205_, lean_object* v_R_1206_, lean_object* v_a_1207_, lean_object* v_b_1208_, lean_object* v_c_1209_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(v_upperBound_1198_, v_x_1200_, v_f_1201_, v_y_1203_, v_g_1204_, v_a_1207_, v_b_1208_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___boxed(lean_object* v_00_u03b3_1211_, lean_object* v_upperBound_1212_, lean_object* v_00_u03b1_1213_, lean_object* v_x_1214_, lean_object* v_f_1215_, lean_object* v_00_u03b2_1216_, lean_object* v_y_1217_, lean_object* v_g_1218_, lean_object* v_inst_1219_, lean_object* v_R_1220_, lean_object* v_a_1221_, lean_object* v_b_1222_, lean_object* v_c_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1(v_00_u03b3_1211_, v_upperBound_1212_, v_00_u03b1_1213_, v_x_1214_, v_f_1215_, v_00_u03b2_1216_, v_y_1217_, v_g_1218_, v_inst_1219_, v_R_1220_, v_a_1221_, v_b_1222_, v_c_1223_);
lean_dec_ref(v_y_1217_);
lean_dec_ref(v_x_1214_);
lean_dec(v_upperBound_1212_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_));
v___x_1233_ = l_Lean_registerInternalExceptionId(v___x_1232_);
return v___x_1233_;
}
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
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_isAbortSpeculation(lean_object* v_x_1247_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_isAbortSpeculation___boxed(lean_object* v_x_1252_){
_start:
{
uint8_t v_res_1253_; lean_object* v_r_1254_; 
v_res_1253_ = l_Lean_Meta_LibrarySearch_isAbortSpeculation(v_x_1252_);
lean_dec_ref(v_x_1252_);
v_r_1254_ = lean_box(v_res_1253_);
return v_r_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(lean_object* v_x_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Lean_Meta_saveState___redArg(v___y_1257_, v___y_1259_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v___x_1263_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_a_1262_);
lean_dec_ref(v___x_1261_);
lean_inc(v___y_1259_);
lean_inc_ref(v___y_1258_);
lean_inc(v___y_1257_);
lean_inc_ref(v___y_1256_);
v___x_1263_ = lean_apply_5(v_x_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, lean_box(0));
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1272_; 
lean_dec(v_a_1262_);
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1266_ = v___x_1263_;
v_isShared_1267_ = v_isSharedCheck_1272_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1263_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1272_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1268_; lean_object* v___x_1270_; 
v___x_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1268_, 0, v_a_1264_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v___x_1268_);
v___x_1270_ = v___x_1266_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1268_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
else
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1302_; 
v_a_1273_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1275_ = v___x_1263_;
v_isShared_1276_ = v_isSharedCheck_1302_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1263_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1302_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
uint8_t v___y_1278_; uint8_t v___x_1300_; 
v___x_1300_ = l_Lean_Exception_isInterrupt(v_a_1273_);
if (v___x_1300_ == 0)
{
uint8_t v___x_1301_; 
lean_inc(v_a_1273_);
v___x_1301_ = l_Lean_Exception_isRuntime(v_a_1273_);
v___y_1278_ = v___x_1301_;
goto v___jp_1277_;
}
else
{
v___y_1278_ = v___x_1300_;
goto v___jp_1277_;
}
v___jp_1277_:
{
if (v___y_1278_ == 0)
{
lean_object* v___x_1279_; 
lean_del_object(v___x_1275_);
lean_dec(v_a_1273_);
v___x_1279_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1262_, v___y_1257_, v___y_1259_);
lean_dec(v_a_1262_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1287_; 
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1287_ == 0)
{
lean_object* v_unused_1288_; 
v_unused_1288_ = lean_ctor_get(v___x_1279_, 0);
lean_dec(v_unused_1288_);
v___x_1281_ = v___x_1279_;
v_isShared_1282_ = v_isSharedCheck_1287_;
goto v_resetjp_1280_;
}
else
{
lean_dec(v___x_1279_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1287_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1283_; lean_object* v___x_1285_; 
v___x_1283_ = lean_box(0);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v___x_1283_);
v___x_1285_ = v___x_1281_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1283_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
v_a_1289_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1279_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1279_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
else
{
lean_object* v___x_1298_; 
lean_dec(v_a_1262_);
if (v_isShared_1276_ == 0)
{
v___x_1298_ = v___x_1275_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1273_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
}
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
lean_dec_ref(v_x_1255_);
v_a_1303_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1261_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1261_);
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
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg___boxed(lean_object* v_x_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(v_x_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0(lean_object* v_00_u03b1_1318_, lean_object* v_x_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(v_x_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___boxed(lean_object* v_00_u03b1_1326_, lean_object* v_x_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0(v_00_u03b1_1326_, v_x_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(lean_object* v_e_1334_, lean_object* v___y_1335_){
_start:
{
uint8_t v___x_1337_; 
v___x_1337_ = l_Lean_Expr_hasMVar(v_e_1334_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; 
v___x_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1338_, 0, v_e_1334_);
return v___x_1338_;
}
else
{
lean_object* v___x_1339_; lean_object* v_mctx_1340_; lean_object* v___x_1341_; lean_object* v_fst_1342_; lean_object* v_snd_1343_; lean_object* v___x_1344_; lean_object* v_cache_1345_; lean_object* v_zetaDeltaFVarIds_1346_; lean_object* v_postponed_1347_; lean_object* v_diag_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1357_; 
v___x_1339_ = lean_st_ref_get(v___y_1335_);
v_mctx_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc_ref(v_mctx_1340_);
lean_dec(v___x_1339_);
v___x_1341_ = l_Lean_instantiateMVarsCore(v_mctx_1340_, v_e_1334_);
v_fst_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_fst_1342_);
v_snd_1343_ = lean_ctor_get(v___x_1341_, 1);
lean_inc(v_snd_1343_);
lean_dec_ref(v___x_1341_);
v___x_1344_ = lean_st_ref_take(v___y_1335_);
v_cache_1345_ = lean_ctor_get(v___x_1344_, 1);
v_zetaDeltaFVarIds_1346_ = lean_ctor_get(v___x_1344_, 2);
v_postponed_1347_ = lean_ctor_get(v___x_1344_, 3);
v_diag_1348_ = lean_ctor_get(v___x_1344_, 4);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1357_ == 0)
{
lean_object* v_unused_1358_; 
v_unused_1358_ = lean_ctor_get(v___x_1344_, 0);
lean_dec(v_unused_1358_);
v___x_1350_ = v___x_1344_;
v_isShared_1351_ = v_isSharedCheck_1357_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_diag_1348_);
lean_inc(v_postponed_1347_);
lean_inc(v_zetaDeltaFVarIds_1346_);
lean_inc(v_cache_1345_);
lean_dec(v___x_1344_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1357_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1353_; 
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 0, v_snd_1343_);
v___x_1353_ = v___x_1350_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_snd_1343_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_cache_1345_);
lean_ctor_set(v_reuseFailAlloc_1356_, 2, v_zetaDeltaFVarIds_1346_);
lean_ctor_set(v_reuseFailAlloc_1356_, 3, v_postponed_1347_);
lean_ctor_set(v_reuseFailAlloc_1356_, 4, v_diag_1348_);
v___x_1353_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = lean_st_ref_set(v___y_1335_, v___x_1353_);
v___x_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1355_, 0, v_fst_1342_);
return v___x_1355_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg___boxed(lean_object* v_e_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(v_e_1359_, v___y_1360_);
lean_dec(v___y_1360_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1(lean_object* v_e_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(v_e_1363_, v___y_1365_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___boxed(lean_object* v_e_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1(v_e_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0(lean_object* v___x_1377_, lean_object* v_x_1378_){
_start:
{
lean_object* v___x_1379_; 
v___x_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1377_);
lean_ctor_set(v___x_1379_, 1, v_x_1378_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(lean_object* v___x_1380_, size_t v_sz_1381_, size_t v_i_1382_, lean_object* v_bs_1383_){
_start:
{
uint8_t v___x_1384_; 
v___x_1384_ = lean_usize_dec_lt(v_i_1382_, v_sz_1381_);
if (v___x_1384_ == 0)
{
lean_dec_ref(v___x_1380_);
return v_bs_1383_;
}
else
{
lean_object* v_v_1385_; lean_object* v___x_1386_; lean_object* v_bs_x27_1387_; lean_object* v___x_1388_; size_t v___x_1389_; size_t v___x_1390_; lean_object* v___x_1391_; 
v_v_1385_ = lean_array_uget(v_bs_1383_, v_i_1382_);
v___x_1386_ = lean_unsigned_to_nat(0u);
v_bs_x27_1387_ = lean_array_uset(v_bs_1383_, v_i_1382_, v___x_1386_);
lean_inc_ref(v___x_1380_);
v___x_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1380_);
lean_ctor_set(v___x_1388_, 1, v_v_1385_);
v___x_1389_ = ((size_t)1ULL);
v___x_1390_ = lean_usize_add(v_i_1382_, v___x_1389_);
v___x_1391_ = lean_array_uset(v_bs_x27_1387_, v_i_1382_, v___x_1388_);
v_i_1382_ = v___x_1390_;
v_bs_1383_ = v___x_1391_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2___boxed(lean_object* v___x_1393_, lean_object* v_sz_1394_, lean_object* v_i_1395_, lean_object* v_bs_1396_){
_start:
{
size_t v_sz_boxed_1397_; size_t v_i_boxed_1398_; lean_object* v_res_1399_; 
v_sz_boxed_1397_ = lean_unbox_usize(v_sz_1394_);
lean_dec(v_sz_1394_);
v_i_boxed_1398_ = lean_unbox_usize(v_i_1395_);
lean_dec(v_i_1395_);
v_res_1399_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(v___x_1393_, v_sz_boxed_1397_, v_i_boxed_1398_, v_bs_1396_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearchSymm(lean_object* v_searchFn_1400_, lean_object* v_goal_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_){
_start:
{
lean_object* v___x_1407_; 
lean_inc(v_goal_1401_);
v___x_1407_ = l_Lean_MVarId_getType(v_goal_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1408_; lean_object* v___x_1409_; 
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_a_1408_);
lean_dec_ref(v___x_1407_);
lean_inc_ref(v_searchFn_1400_);
lean_inc(v_a_1405_);
lean_inc_ref(v_a_1404_);
lean_inc(v_a_1403_);
lean_inc_ref(v_a_1402_);
v___x_1409_ = lean_apply_6(v_searchFn_1400_, v_a_1408_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, lean_box(0));
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v_a_1410_; lean_object* v___x_1411_; lean_object* v_mctx_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_a_1410_);
lean_dec_ref(v___x_1409_);
v___x_1411_ = lean_st_ref_get(v_a_1403_);
v_mctx_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc_ref_n(v_mctx_1412_, 2);
lean_dec(v___x_1411_);
lean_inc(v_goal_1401_);
v___x_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1413_, 0, v_goal_1401_);
lean_ctor_set(v___x_1413_, 1, v_mctx_1412_);
v___x_1414_ = lean_alloc_closure((void*)(l_Lean_MVarId_applySymm___boxed), 6, 1);
lean_closure_set(v___x_1414_, 0, v_goal_1401_);
v___x_1415_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(v___x_1414_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1476_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1476_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1476_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
if (lean_obj_tag(v_a_1416_) == 1)
{
lean_object* v_val_1420_; lean_object* v___x_1421_; 
lean_del_object(v___x_1418_);
v_val_1420_ = lean_ctor_get(v_a_1416_, 0);
lean_inc_n(v_val_1420_, 2);
lean_dec_ref(v_a_1416_);
v___x_1421_ = l_Lean_MVarId_getType(v_val_1420_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v___x_1423_; lean_object* v_a_1424_; lean_object* v___x_1425_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1422_);
lean_dec_ref(v___x_1421_);
v___x_1423_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(v_a_1422_, v_a_1403_);
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_a_1424_);
lean_dec_ref(v___x_1423_);
lean_inc(v_a_1405_);
lean_inc_ref(v_a_1404_);
lean_inc(v_a_1403_);
lean_inc_ref(v_a_1402_);
v___x_1425_ = lean_apply_6(v_searchFn_1400_, v_a_1424_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, lean_box(0));
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1453_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1428_ = v___x_1425_;
v_isShared_1429_ = v_isSharedCheck_1453_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1425_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1453_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v_cache_1432_; lean_object* v_zetaDeltaFVarIds_1433_; lean_object* v_postponed_1434_; lean_object* v_diag_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1451_; 
v___x_1430_ = lean_st_ref_get(v_a_1403_);
v___x_1431_ = lean_st_ref_take(v_a_1403_);
v_cache_1432_ = lean_ctor_get(v___x_1431_, 1);
v_zetaDeltaFVarIds_1433_ = lean_ctor_get(v___x_1431_, 2);
v_postponed_1434_ = lean_ctor_get(v___x_1431_, 3);
v_diag_1435_ = lean_ctor_get(v___x_1431_, 4);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1451_ == 0)
{
lean_object* v_unused_1452_; 
v_unused_1452_ = lean_ctor_get(v___x_1431_, 0);
lean_dec(v_unused_1452_);
v___x_1437_ = v___x_1431_;
v_isShared_1438_ = v_isSharedCheck_1451_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_diag_1435_);
lean_inc(v_postponed_1434_);
lean_inc(v_zetaDeltaFVarIds_1433_);
lean_inc(v_cache_1432_);
lean_dec(v___x_1431_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1451_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 0, v_mctx_1412_);
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_mctx_1412_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v_cache_1432_);
lean_ctor_set(v_reuseFailAlloc_1450_, 2, v_zetaDeltaFVarIds_1433_);
lean_ctor_set(v_reuseFailAlloc_1450_, 3, v_postponed_1434_);
lean_ctor_set(v_reuseFailAlloc_1450_, 4, v_diag_1435_);
v___x_1440_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1441_; lean_object* v_mctx_1442_; lean_object* v___f_1443_; lean_object* v___x_1444_; lean_object* v___f_1445_; lean_object* v___x_1446_; lean_object* v___x_1448_; 
v___x_1441_ = lean_st_ref_set(v_a_1403_, v___x_1440_);
v_mctx_1442_ = lean_ctor_get(v___x_1430_, 0);
lean_inc_ref(v_mctx_1442_);
lean_dec(v___x_1430_);
v___f_1443_ = lean_alloc_closure((void*)(l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0), 2, 1);
lean_closure_set(v___f_1443_, 0, v___x_1413_);
v___x_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1444_, 0, v_val_1420_);
lean_ctor_set(v___x_1444_, 1, v_mctx_1442_);
v___f_1445_ = lean_alloc_closure((void*)(l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0), 2, 1);
lean_closure_set(v___f_1445_, 0, v___x_1444_);
v___x_1446_ = l_Lean_Meta_LibrarySearch_interleaveWith___redArg(v___f_1443_, v_a_1410_, v___f_1445_, v_a_1426_);
lean_dec(v_a_1426_);
lean_dec(v_a_1410_);
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 0, v___x_1446_);
v___x_1448_ = v___x_1428_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1446_);
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
}
else
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
lean_dec(v_val_1420_);
lean_dec_ref(v___x_1413_);
lean_dec_ref(v_mctx_1412_);
lean_dec(v_a_1410_);
v_a_1454_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1425_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1425_);
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
else
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
lean_dec(v_val_1420_);
lean_dec_ref(v___x_1413_);
lean_dec_ref(v_mctx_1412_);
lean_dec(v_a_1410_);
lean_dec_ref(v_searchFn_1400_);
v_a_1462_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1464_ = v___x_1421_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1421_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
if (v_isShared_1465_ == 0)
{
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1462_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
else
{
size_t v_sz_1470_; size_t v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1474_; 
lean_dec(v_a_1416_);
lean_dec_ref(v_mctx_1412_);
lean_dec_ref(v_searchFn_1400_);
v_sz_1470_ = lean_array_size(v_a_1410_);
v___x_1471_ = ((size_t)0ULL);
v___x_1472_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(v___x_1413_, v_sz_1470_, v___x_1471_, v_a_1410_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1472_);
v___x_1474_ = v___x_1418_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1472_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
else
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1484_; 
lean_dec_ref(v___x_1413_);
lean_dec_ref(v_mctx_1412_);
lean_dec(v_a_1410_);
lean_dec_ref(v_searchFn_1400_);
v_a_1477_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1479_ = v___x_1415_;
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1415_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1477_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
else
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
lean_dec(v_goal_1401_);
lean_dec_ref(v_searchFn_1400_);
v_a_1485_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1409_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1409_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
else
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1500_; 
lean_dec(v_goal_1401_);
lean_dec_ref(v_searchFn_1400_);
v_a_1493_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1495_ = v___x_1407_;
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___x_1407_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1498_; 
if (v_isShared_1496_ == 0)
{
v___x_1498_ = v___x_1495_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_a_1493_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearchSymm___boxed(lean_object* v_searchFn_1501_, lean_object* v_goal_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v_searchFn_1501_, v_goal_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_);
lean_dec(v_a_1506_);
lean_dec_ref(v_a_1505_);
lean_dec(v_a_1504_);
lean_dec_ref(v_a_1503_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0(lean_object* v_e_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1519_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___closed__1));
v___x_1520_ = lean_unsigned_to_nat(1u);
v___x_1521_ = lean_mk_empty_array_with_capacity(v___x_1520_);
v___x_1522_ = lean_array_push(v___x_1521_, v_e_1513_);
v___x_1523_ = l_Lean_Meta_mkAppM(v___x_1519_, v___x_1522_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___boxed(lean_object* v_e_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0(v_e_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1(lean_object* v_e_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1541_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___closed__1));
v___x_1542_ = lean_unsigned_to_nat(1u);
v___x_1543_ = lean_mk_empty_array_with_capacity(v___x_1542_);
v___x_1544_ = lean_array_push(v___x_1543_, v_e_1535_);
v___x_1545_ = l_Lean_Meta_mkAppM(v___x_1541_, v___x_1544_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___boxed(lean_object* v_e_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1(v_e_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(lean_object* v_lem_1555_, uint8_t v_mod_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_lem_1555_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_);
if (lean_obj_tag(v___x_1562_) == 0)
{
switch(v_mod_1556_)
{
case 0:
{
return v___x_1562_;
}
case 1:
{
lean_object* v_a_1563_; lean_object* v___f_1564_; lean_object* v___x_1565_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_a_1563_);
lean_dec_ref(v___x_1562_);
v___f_1564_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__0));
v___x_1565_ = l_Lean_Meta_mapForallTelescope(v___f_1564_, v_a_1563_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_);
return v___x_1565_;
}
default: 
{
lean_object* v_a_1566_; lean_object* v___f_1567_; lean_object* v___x_1568_; 
v_a_1566_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_a_1566_);
lean_dec_ref(v___x_1562_);
v___f_1567_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__1));
v___x_1568_ = l_Lean_Meta_mapForallTelescope(v___f_1567_, v_a_1566_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_);
return v___x_1568_;
}
}
}
else
{
return v___x_1562_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___boxed(lean_object* v_lem_1569_, lean_object* v_mod_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_){
_start:
{
uint8_t v_mod_boxed_1576_; lean_object* v_res_1577_; 
v_mod_boxed_1576_ = lean_unbox(v_mod_1570_);
v_res_1577_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_lem_1569_, v_mod_boxed_1576_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_);
lean_dec(v_a_1574_);
lean_dec_ref(v_a_1573_);
lean_dec(v_a_1572_);
lean_dec_ref(v_a_1571_);
return v_res_1577_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar(lean_object* v_e_1578_){
_start:
{
switch(lean_obj_tag(v_e_1578_))
{
case 0:
{
uint8_t v___x_1579_; 
v___x_1579_ = 1;
return v___x_1579_;
}
case 1:
{
uint8_t v___x_1580_; 
v___x_1580_ = 1;
return v___x_1580_;
}
case 2:
{
uint8_t v___x_1581_; 
v___x_1581_ = 1;
return v___x_1581_;
}
default: 
{
uint8_t v___x_1582_; 
v___x_1582_ = 0;
return v___x_1582_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar___boxed(lean_object* v_e_1583_){
_start:
{
uint8_t v_res_1584_; lean_object* v_r_1585_; 
v_res_1584_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar(v_e_1583_);
lean_dec_ref(v_e_1583_);
v_r_1585_ = lean_box(v_res_1584_);
return v_r_1585_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1586_ = lean_unsigned_to_nat(32u);
v___x_1587_ = lean_mk_empty_array_with_capacity(v___x_1586_);
v___x_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1587_);
return v___x_1588_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1589_ = ((size_t)5ULL);
v___x_1590_ = lean_unsigned_to_nat(0u);
v___x_1591_ = lean_unsigned_to_nat(32u);
v___x_1592_ = lean_mk_empty_array_with_capacity(v___x_1591_);
v___x_1593_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0);
v___x_1594_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1594_, 0, v___x_1593_);
lean_ctor_set(v___x_1594_, 1, v___x_1592_);
lean_ctor_set(v___x_1594_, 2, v___x_1590_);
lean_ctor_set(v___x_1594_, 3, v___x_1590_);
lean_ctor_set_usize(v___x_1594_, 4, v___x_1589_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(lean_object* v___y_1595_){
_start:
{
lean_object* v___x_1597_; lean_object* v_traceState_1598_; lean_object* v_traces_1599_; lean_object* v___x_1600_; lean_object* v_traceState_1601_; lean_object* v_env_1602_; lean_object* v_nextMacroScope_1603_; lean_object* v_ngen_1604_; lean_object* v_auxDeclNGen_1605_; lean_object* v_cache_1606_; lean_object* v_messages_1607_; lean_object* v_infoState_1608_; lean_object* v_snapshotTasks_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1628_; 
v___x_1597_ = lean_st_ref_get(v___y_1595_);
v_traceState_1598_ = lean_ctor_get(v___x_1597_, 4);
lean_inc_ref(v_traceState_1598_);
lean_dec(v___x_1597_);
v_traces_1599_ = lean_ctor_get(v_traceState_1598_, 0);
lean_inc_ref(v_traces_1599_);
lean_dec_ref(v_traceState_1598_);
v___x_1600_ = lean_st_ref_take(v___y_1595_);
v_traceState_1601_ = lean_ctor_get(v___x_1600_, 4);
v_env_1602_ = lean_ctor_get(v___x_1600_, 0);
v_nextMacroScope_1603_ = lean_ctor_get(v___x_1600_, 1);
v_ngen_1604_ = lean_ctor_get(v___x_1600_, 2);
v_auxDeclNGen_1605_ = lean_ctor_get(v___x_1600_, 3);
v_cache_1606_ = lean_ctor_get(v___x_1600_, 5);
v_messages_1607_ = lean_ctor_get(v___x_1600_, 6);
v_infoState_1608_ = lean_ctor_get(v___x_1600_, 7);
v_snapshotTasks_1609_ = lean_ctor_get(v___x_1600_, 8);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1611_ = v___x_1600_;
v_isShared_1612_ = v_isSharedCheck_1628_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_snapshotTasks_1609_);
lean_inc(v_infoState_1608_);
lean_inc(v_messages_1607_);
lean_inc(v_cache_1606_);
lean_inc(v_traceState_1601_);
lean_inc(v_auxDeclNGen_1605_);
lean_inc(v_ngen_1604_);
lean_inc(v_nextMacroScope_1603_);
lean_inc(v_env_1602_);
lean_dec(v___x_1600_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1628_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
uint64_t v_tid_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1626_; 
v_tid_1613_ = lean_ctor_get_uint64(v_traceState_1601_, sizeof(void*)*1);
v_isSharedCheck_1626_ = !lean_is_exclusive(v_traceState_1601_);
if (v_isSharedCheck_1626_ == 0)
{
lean_object* v_unused_1627_; 
v_unused_1627_ = lean_ctor_get(v_traceState_1601_, 0);
lean_dec(v_unused_1627_);
v___x_1615_ = v_traceState_1601_;
v_isShared_1616_ = v_isSharedCheck_1626_;
goto v_resetjp_1614_;
}
else
{
lean_dec(v_traceState_1601_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1626_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1617_; lean_object* v___x_1619_; 
v___x_1617_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1);
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 0, v___x_1617_);
v___x_1619_ = v___x_1615_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v___x_1617_);
lean_ctor_set_uint64(v_reuseFailAlloc_1625_, sizeof(void*)*1, v_tid_1613_);
v___x_1619_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
lean_object* v___x_1621_; 
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 4, v___x_1619_);
v___x_1621_ = v___x_1611_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_env_1602_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_nextMacroScope_1603_);
lean_ctor_set(v_reuseFailAlloc_1624_, 2, v_ngen_1604_);
lean_ctor_set(v_reuseFailAlloc_1624_, 3, v_auxDeclNGen_1605_);
lean_ctor_set(v_reuseFailAlloc_1624_, 4, v___x_1619_);
lean_ctor_set(v_reuseFailAlloc_1624_, 5, v_cache_1606_);
lean_ctor_set(v_reuseFailAlloc_1624_, 6, v_messages_1607_);
lean_ctor_set(v_reuseFailAlloc_1624_, 7, v_infoState_1608_);
lean_ctor_set(v_reuseFailAlloc_1624_, 8, v_snapshotTasks_1609_);
v___x_1621_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = lean_st_ref_set(v___y_1595_, v___x_1621_);
v___x_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1623_, 0, v_traces_1599_);
return v___x_1623_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___boxed(lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v___y_1629_);
lean_dec(v___y_1629_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0(lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v___y_1635_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___boxed(lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0(v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
return v_res_1643_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(lean_object* v_opts_1644_, lean_object* v_opt_1645_){
_start:
{
lean_object* v_name_1646_; lean_object* v_defValue_1647_; lean_object* v_map_1648_; lean_object* v___x_1649_; 
v_name_1646_ = lean_ctor_get(v_opt_1645_, 0);
v_defValue_1647_ = lean_ctor_get(v_opt_1645_, 1);
v_map_1648_ = lean_ctor_get(v_opts_1644_, 0);
v___x_1649_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1648_, v_name_1646_);
if (lean_obj_tag(v___x_1649_) == 0)
{
uint8_t v___x_1650_; 
v___x_1650_ = lean_unbox(v_defValue_1647_);
return v___x_1650_;
}
else
{
lean_object* v_val_1651_; 
v_val_1651_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_val_1651_);
lean_dec_ref(v___x_1649_);
if (lean_obj_tag(v_val_1651_) == 1)
{
uint8_t v_v_1652_; 
v_v_1652_ = lean_ctor_get_uint8(v_val_1651_, 0);
lean_dec_ref(v_val_1651_);
return v_v_1652_;
}
else
{
uint8_t v___x_1653_; 
lean_dec(v_val_1651_);
v___x_1653_ = lean_unbox(v_defValue_1647_);
return v___x_1653_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1___boxed(lean_object* v_opts_1654_, lean_object* v_opt_1655_){
_start:
{
uint8_t v_res_1656_; lean_object* v_r_1657_; 
v_res_1656_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_1654_, v_opt_1655_);
lean_dec_ref(v_opt_1655_);
lean_dec_ref(v_opts_1654_);
v_r_1657_ = lean_box(v_res_1656_);
return v_r_1657_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1659_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__0));
v___x_1660_ = l_Lean_stringToMessageData(v___x_1659_);
return v___x_1660_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1662_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__2));
v___x_1663_ = l_Lean_stringToMessageData(v___x_1662_);
return v___x_1663_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1667_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__5));
v___x_1668_ = l_Lean_MessageData_ofFormat(v___x_1667_);
return v___x_1668_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1672_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__8));
v___x_1673_ = l_Lean_MessageData_ofFormat(v___x_1672_);
return v___x_1673_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12(void){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__11));
v___x_1678_ = l_Lean_MessageData_ofFormat(v___x_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0(lean_object* v_fst_1679_, uint8_t v_snd_1680_, lean_object* v_x_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___y_1691_; 
v___x_1687_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1);
v___x_1688_ = l_Lean_MessageData_ofName(v_fst_1679_);
v___x_1689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1687_);
lean_ctor_set(v___x_1689_, 1, v___x_1688_);
switch(v_snd_1680_)
{
case 0:
{
lean_object* v___x_1696_; 
v___x_1696_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6);
v___y_1691_ = v___x_1696_;
goto v___jp_1690_;
}
case 1:
{
lean_object* v___x_1697_; 
v___x_1697_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9);
v___y_1691_ = v___x_1697_;
goto v___jp_1690_;
}
default: 
{
lean_object* v___x_1698_; 
v___x_1698_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12);
v___y_1691_ = v___x_1698_;
goto v___jp_1690_;
}
}
v___jp_1690_:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
lean_inc_ref(v___y_1691_);
v___x_1692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1689_);
lean_ctor_set(v___x_1692_, 1, v___y_1691_);
v___x_1693_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3);
v___x_1694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1692_);
lean_ctor_set(v___x_1694_, 1, v___x_1693_);
v___x_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
return v___x_1695_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___boxed(lean_object* v_fst_1699_, lean_object* v_snd_1700_, lean_object* v_x_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
uint8_t v_snd_11731__boxed_1707_; lean_object* v_res_1708_; 
v_snd_11731__boxed_1707_ = lean_unbox(v_snd_1700_);
v_res_1708_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0(v_fst_1699_, v_snd_11731__boxed_1707_, v_x_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec_ref(v_x_1701_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(lean_object* v_opts_1709_, lean_object* v_opt_1710_){
_start:
{
lean_object* v_name_1711_; lean_object* v_defValue_1712_; lean_object* v_map_1713_; lean_object* v___x_1714_; 
v_name_1711_ = lean_ctor_get(v_opt_1710_, 0);
v_defValue_1712_ = lean_ctor_get(v_opt_1710_, 1);
v_map_1713_ = lean_ctor_get(v_opts_1709_, 0);
v___x_1714_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1713_, v_name_1711_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_inc(v_defValue_1712_);
return v_defValue_1712_;
}
else
{
lean_object* v_val_1715_; 
v_val_1715_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_val_1715_);
lean_dec_ref(v___x_1714_);
if (lean_obj_tag(v_val_1715_) == 3)
{
lean_object* v_v_1716_; 
v_v_1716_ = lean_ctor_get(v_val_1715_, 0);
lean_inc(v_v_1716_);
lean_dec_ref(v_val_1715_);
return v_v_1716_;
}
else
{
lean_dec(v_val_1715_);
lean_inc(v_defValue_1712_);
return v_defValue_1712_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5___boxed(lean_object* v_opts_1717_, lean_object* v_opt_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_1717_, v_opt_1718_);
lean_dec_ref(v_opt_1718_);
lean_dec_ref(v_opts_1717_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4___redArg(lean_object* v_x_1720_){
_start:
{
if (lean_obj_tag(v_x_1720_) == 0)
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
v_a_1722_ = lean_ctor_get(v_x_1720_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v_x_1720_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1724_ = v_x_1720_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v_x_1720_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
lean_ctor_set_tag(v___x_1724_, 1);
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_a_1722_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
else
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1737_; 
v_a_1730_ = lean_ctor_get(v_x_1720_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v_x_1720_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1732_ = v_x_1720_;
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v_x_1720_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1733_ == 0)
{
lean_ctor_set_tag(v___x_1732_, 0);
v___x_1735_ = v___x_1732_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_a_1730_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4___redArg___boxed(lean_object* v_x_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4___redArg(v_x_1738_);
return v_res_1740_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(lean_object* v_e_1741_){
_start:
{
if (lean_obj_tag(v_e_1741_) == 0)
{
uint8_t v___x_1742_; 
v___x_1742_ = 2;
return v___x_1742_;
}
else
{
uint8_t v___x_1743_; 
v___x_1743_ = 0;
return v___x_1743_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2___boxed(lean_object* v_e_1744_){
_start:
{
uint8_t v_res_1745_; lean_object* v_r_1746_; 
v_res_1745_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(v_e_1744_);
lean_dec_ref(v_e_1744_);
v_r_1746_ = lean_box(v_res_1745_);
return v_r_1746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3_spec__4(size_t v_sz_1747_, size_t v_i_1748_, lean_object* v_bs_1749_){
_start:
{
uint8_t v___x_1750_; 
v___x_1750_ = lean_usize_dec_lt(v_i_1748_, v_sz_1747_);
if (v___x_1750_ == 0)
{
return v_bs_1749_;
}
else
{
lean_object* v_v_1751_; lean_object* v_msg_1752_; lean_object* v___x_1753_; lean_object* v_bs_x27_1754_; size_t v___x_1755_; size_t v___x_1756_; lean_object* v___x_1757_; 
v_v_1751_ = lean_array_uget_borrowed(v_bs_1749_, v_i_1748_);
v_msg_1752_ = lean_ctor_get(v_v_1751_, 1);
lean_inc_ref(v_msg_1752_);
v___x_1753_ = lean_unsigned_to_nat(0u);
v_bs_x27_1754_ = lean_array_uset(v_bs_1749_, v_i_1748_, v___x_1753_);
v___x_1755_ = ((size_t)1ULL);
v___x_1756_ = lean_usize_add(v_i_1748_, v___x_1755_);
v___x_1757_ = lean_array_uset(v_bs_x27_1754_, v_i_1748_, v_msg_1752_);
v_i_1748_ = v___x_1756_;
v_bs_1749_ = v___x_1757_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3_spec__4___boxed(lean_object* v_sz_1759_, lean_object* v_i_1760_, lean_object* v_bs_1761_){
_start:
{
size_t v_sz_boxed_1762_; size_t v_i_boxed_1763_; lean_object* v_res_1764_; 
v_sz_boxed_1762_ = lean_unbox_usize(v_sz_1759_);
lean_dec(v_sz_1759_);
v_i_boxed_1763_ = lean_unbox_usize(v_i_1760_);
lean_dec(v_i_1760_);
v_res_1764_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3_spec__4(v_sz_boxed_1762_, v_i_boxed_1763_, v_bs_1761_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3(lean_object* v_oldTraces_1765_, lean_object* v_data_1766_, lean_object* v_ref_1767_, lean_object* v_msg_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v_fileName_1774_; lean_object* v_fileMap_1775_; lean_object* v_options_1776_; lean_object* v_currRecDepth_1777_; lean_object* v_maxRecDepth_1778_; lean_object* v_ref_1779_; lean_object* v_currNamespace_1780_; lean_object* v_openDecls_1781_; lean_object* v_initHeartbeats_1782_; lean_object* v_maxHeartbeats_1783_; lean_object* v_quotContext_1784_; lean_object* v_currMacroScope_1785_; uint8_t v_diag_1786_; lean_object* v_cancelTk_x3f_1787_; uint8_t v_suppressElabErrors_1788_; lean_object* v_inheritedTraceOptions_1789_; lean_object* v___x_1790_; lean_object* v_traceState_1791_; lean_object* v_traces_1792_; lean_object* v_ref_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; size_t v_sz_1796_; size_t v___x_1797_; lean_object* v___x_1798_; lean_object* v_msg_1799_; lean_object* v___x_1800_; lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1838_; 
v_fileName_1774_ = lean_ctor_get(v___y_1771_, 0);
v_fileMap_1775_ = lean_ctor_get(v___y_1771_, 1);
v_options_1776_ = lean_ctor_get(v___y_1771_, 2);
v_currRecDepth_1777_ = lean_ctor_get(v___y_1771_, 3);
v_maxRecDepth_1778_ = lean_ctor_get(v___y_1771_, 4);
v_ref_1779_ = lean_ctor_get(v___y_1771_, 5);
v_currNamespace_1780_ = lean_ctor_get(v___y_1771_, 6);
v_openDecls_1781_ = lean_ctor_get(v___y_1771_, 7);
v_initHeartbeats_1782_ = lean_ctor_get(v___y_1771_, 8);
v_maxHeartbeats_1783_ = lean_ctor_get(v___y_1771_, 9);
v_quotContext_1784_ = lean_ctor_get(v___y_1771_, 10);
v_currMacroScope_1785_ = lean_ctor_get(v___y_1771_, 11);
v_diag_1786_ = lean_ctor_get_uint8(v___y_1771_, sizeof(void*)*14);
v_cancelTk_x3f_1787_ = lean_ctor_get(v___y_1771_, 12);
v_suppressElabErrors_1788_ = lean_ctor_get_uint8(v___y_1771_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1789_ = lean_ctor_get(v___y_1771_, 13);
v___x_1790_ = lean_st_ref_get(v___y_1772_);
v_traceState_1791_ = lean_ctor_get(v___x_1790_, 4);
lean_inc_ref(v_traceState_1791_);
lean_dec(v___x_1790_);
v_traces_1792_ = lean_ctor_get(v_traceState_1791_, 0);
lean_inc_ref(v_traces_1792_);
lean_dec_ref(v_traceState_1791_);
v_ref_1793_ = l_Lean_replaceRef(v_ref_1767_, v_ref_1779_);
lean_inc_ref(v_inheritedTraceOptions_1789_);
lean_inc(v_cancelTk_x3f_1787_);
lean_inc(v_currMacroScope_1785_);
lean_inc(v_quotContext_1784_);
lean_inc(v_maxHeartbeats_1783_);
lean_inc(v_initHeartbeats_1782_);
lean_inc(v_openDecls_1781_);
lean_inc(v_currNamespace_1780_);
lean_inc(v_maxRecDepth_1778_);
lean_inc(v_currRecDepth_1777_);
lean_inc_ref(v_options_1776_);
lean_inc_ref(v_fileMap_1775_);
lean_inc_ref(v_fileName_1774_);
v___x_1794_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1794_, 0, v_fileName_1774_);
lean_ctor_set(v___x_1794_, 1, v_fileMap_1775_);
lean_ctor_set(v___x_1794_, 2, v_options_1776_);
lean_ctor_set(v___x_1794_, 3, v_currRecDepth_1777_);
lean_ctor_set(v___x_1794_, 4, v_maxRecDepth_1778_);
lean_ctor_set(v___x_1794_, 5, v_ref_1793_);
lean_ctor_set(v___x_1794_, 6, v_currNamespace_1780_);
lean_ctor_set(v___x_1794_, 7, v_openDecls_1781_);
lean_ctor_set(v___x_1794_, 8, v_initHeartbeats_1782_);
lean_ctor_set(v___x_1794_, 9, v_maxHeartbeats_1783_);
lean_ctor_set(v___x_1794_, 10, v_quotContext_1784_);
lean_ctor_set(v___x_1794_, 11, v_currMacroScope_1785_);
lean_ctor_set(v___x_1794_, 12, v_cancelTk_x3f_1787_);
lean_ctor_set(v___x_1794_, 13, v_inheritedTraceOptions_1789_);
lean_ctor_set_uint8(v___x_1794_, sizeof(void*)*14, v_diag_1786_);
lean_ctor_set_uint8(v___x_1794_, sizeof(void*)*14 + 1, v_suppressElabErrors_1788_);
v___x_1795_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1792_);
lean_dec_ref(v_traces_1792_);
v_sz_1796_ = lean_array_size(v___x_1795_);
v___x_1797_ = ((size_t)0ULL);
v___x_1798_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3_spec__4(v_sz_1796_, v___x_1797_, v___x_1795_);
v_msg_1799_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1799_, 0, v_data_1766_);
lean_ctor_set(v_msg_1799_, 1, v_msg_1768_);
lean_ctor_set(v_msg_1799_, 2, v___x_1798_);
v___x_1800_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(v_msg_1799_, v___y_1769_, v___y_1770_, v___x_1794_, v___y_1772_);
lean_dec_ref(v___x_1794_);
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1803_ = v___x_1800_;
v_isShared_1804_ = v_isSharedCheck_1838_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1800_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1838_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1805_; lean_object* v_traceState_1806_; lean_object* v_env_1807_; lean_object* v_nextMacroScope_1808_; lean_object* v_ngen_1809_; lean_object* v_auxDeclNGen_1810_; lean_object* v_cache_1811_; lean_object* v_messages_1812_; lean_object* v_infoState_1813_; lean_object* v_snapshotTasks_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1837_; 
v___x_1805_ = lean_st_ref_take(v___y_1772_);
v_traceState_1806_ = lean_ctor_get(v___x_1805_, 4);
v_env_1807_ = lean_ctor_get(v___x_1805_, 0);
v_nextMacroScope_1808_ = lean_ctor_get(v___x_1805_, 1);
v_ngen_1809_ = lean_ctor_get(v___x_1805_, 2);
v_auxDeclNGen_1810_ = lean_ctor_get(v___x_1805_, 3);
v_cache_1811_ = lean_ctor_get(v___x_1805_, 5);
v_messages_1812_ = lean_ctor_get(v___x_1805_, 6);
v_infoState_1813_ = lean_ctor_get(v___x_1805_, 7);
v_snapshotTasks_1814_ = lean_ctor_get(v___x_1805_, 8);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1816_ = v___x_1805_;
v_isShared_1817_ = v_isSharedCheck_1837_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_snapshotTasks_1814_);
lean_inc(v_infoState_1813_);
lean_inc(v_messages_1812_);
lean_inc(v_cache_1811_);
lean_inc(v_traceState_1806_);
lean_inc(v_auxDeclNGen_1810_);
lean_inc(v_ngen_1809_);
lean_inc(v_nextMacroScope_1808_);
lean_inc(v_env_1807_);
lean_dec(v___x_1805_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1837_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
uint64_t v_tid_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1835_; 
v_tid_1818_ = lean_ctor_get_uint64(v_traceState_1806_, sizeof(void*)*1);
v_isSharedCheck_1835_ = !lean_is_exclusive(v_traceState_1806_);
if (v_isSharedCheck_1835_ == 0)
{
lean_object* v_unused_1836_; 
v_unused_1836_ = lean_ctor_get(v_traceState_1806_, 0);
lean_dec(v_unused_1836_);
v___x_1820_ = v_traceState_1806_;
v_isShared_1821_ = v_isSharedCheck_1835_;
goto v_resetjp_1819_;
}
else
{
lean_dec(v_traceState_1806_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1835_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1825_; 
v___x_1822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1822_, 0, v_ref_1767_);
lean_ctor_set(v___x_1822_, 1, v_a_1801_);
v___x_1823_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1765_, v___x_1822_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v___x_1823_);
v___x_1825_ = v___x_1820_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1823_);
lean_ctor_set_uint64(v_reuseFailAlloc_1834_, sizeof(void*)*1, v_tid_1818_);
v___x_1825_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
lean_object* v___x_1827_; 
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 4, v___x_1825_);
v___x_1827_ = v___x_1816_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_env_1807_);
lean_ctor_set(v_reuseFailAlloc_1833_, 1, v_nextMacroScope_1808_);
lean_ctor_set(v_reuseFailAlloc_1833_, 2, v_ngen_1809_);
lean_ctor_set(v_reuseFailAlloc_1833_, 3, v_auxDeclNGen_1810_);
lean_ctor_set(v_reuseFailAlloc_1833_, 4, v___x_1825_);
lean_ctor_set(v_reuseFailAlloc_1833_, 5, v_cache_1811_);
lean_ctor_set(v_reuseFailAlloc_1833_, 6, v_messages_1812_);
lean_ctor_set(v_reuseFailAlloc_1833_, 7, v_infoState_1813_);
lean_ctor_set(v_reuseFailAlloc_1833_, 8, v_snapshotTasks_1814_);
v___x_1827_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1831_; 
v___x_1828_ = lean_st_ref_set(v___y_1772_, v___x_1827_);
v___x_1829_ = lean_box(0);
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 0, v___x_1829_);
v___x_1831_ = v___x_1803_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1829_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___boxed(lean_object* v_oldTraces_1839_, lean_object* v_data_1840_, lean_object* v_ref_1841_, lean_object* v_msg_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3(v_oldTraces_1839_, v_data_1840_, v_ref_1841_, v_msg_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
return v_res_1848_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1849_; double v___x_1850_; 
v___x_1849_ = lean_unsigned_to_nat(0u);
v___x_1850_ = lean_float_of_nat(v___x_1849_);
return v___x_1850_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1852_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__1));
v___x_1853_ = l_Lean_stringToMessageData(v___x_1852_);
return v___x_1853_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1854_; double v___x_1855_; 
v___x_1854_ = lean_unsigned_to_nat(1000u);
v___x_1855_ = lean_float_of_nat(v___x_1854_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(lean_object* v_cls_1856_, uint8_t v_collapsed_1857_, lean_object* v_tag_1858_, lean_object* v_opts_1859_, uint8_t v_clsEnabled_1860_, lean_object* v_oldTraces_1861_, lean_object* v_msg_1862_, lean_object* v_resStartStop_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v_fst_1869_; lean_object* v_snd_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1968_; 
v_fst_1869_ = lean_ctor_get(v_resStartStop_1863_, 0);
v_snd_1870_ = lean_ctor_get(v_resStartStop_1863_, 1);
v_isSharedCheck_1968_ = !lean_is_exclusive(v_resStartStop_1863_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1872_ = v_resStartStop_1863_;
v_isShared_1873_ = v_isSharedCheck_1968_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_snd_1870_);
lean_inc(v_fst_1869_);
lean_dec(v_resStartStop_1863_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1968_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v_data_1877_; lean_object* v_fst_1888_; lean_object* v_snd_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1967_; 
v_fst_1888_ = lean_ctor_get(v_snd_1870_, 0);
v_snd_1889_ = lean_ctor_get(v_snd_1870_, 1);
v_isSharedCheck_1967_ = !lean_is_exclusive(v_snd_1870_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1891_ = v_snd_1870_;
v_isShared_1892_ = v_isSharedCheck_1967_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_snd_1889_);
lean_inc(v_fst_1888_);
lean_dec(v_snd_1870_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1967_;
goto v_resetjp_1890_;
}
v___jp_1874_:
{
lean_object* v___x_1878_; 
lean_inc(v___y_1876_);
v___x_1878_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3(v_oldTraces_1861_, v_data_1877_, v___y_1876_, v___y_1875_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v___x_1879_; 
lean_dec_ref(v___x_1878_);
v___x_1879_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4___redArg(v_fst_1869_);
return v___x_1879_;
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
lean_dec(v_fst_1869_);
v_a_1880_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1878_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1878_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
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
v_resetjp_1890_:
{
lean_object* v___x_1893_; uint8_t v___x_1894_; lean_object* v___y_1896_; lean_object* v_a_1897_; uint8_t v___y_1921_; double v___y_1952_; 
v___x_1893_ = l_Lean_trace_profiler;
v___x_1894_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_1859_, v___x_1893_);
if (v___x_1894_ == 0)
{
v___y_1921_ = v___x_1894_;
goto v___jp_1920_;
}
else
{
lean_object* v___x_1957_; uint8_t v___x_1958_; 
v___x_1957_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1958_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_1859_, v___x_1957_);
if (v___x_1958_ == 0)
{
lean_object* v___x_1959_; lean_object* v___x_1960_; double v___x_1961_; double v___x_1962_; double v___x_1963_; 
v___x_1959_ = l_Lean_trace_profiler_threshold;
v___x_1960_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_1859_, v___x_1959_);
v___x_1961_ = lean_float_of_nat(v___x_1960_);
v___x_1962_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3);
v___x_1963_ = lean_float_div(v___x_1961_, v___x_1962_);
v___y_1952_ = v___x_1963_;
goto v___jp_1951_;
}
else
{
lean_object* v___x_1964_; lean_object* v___x_1965_; double v___x_1966_; 
v___x_1964_ = l_Lean_trace_profiler_threshold;
v___x_1965_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_1859_, v___x_1964_);
v___x_1966_ = lean_float_of_nat(v___x_1965_);
v___y_1952_ = v___x_1966_;
goto v___jp_1951_;
}
}
v___jp_1895_:
{
uint8_t v_result_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1903_; 
v_result_1898_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(v_fst_1869_);
v___x_1899_ = l_Lean_TraceResult_toEmoji(v_result_1898_);
v___x_1900_ = l_Lean_stringToMessageData(v___x_1899_);
v___x_1901_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3);
if (v_isShared_1892_ == 0)
{
lean_ctor_set_tag(v___x_1891_, 7);
lean_ctor_set(v___x_1891_, 1, v___x_1901_);
lean_ctor_set(v___x_1891_, 0, v___x_1900_);
v___x_1903_ = v___x_1891_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1900_);
lean_ctor_set(v_reuseFailAlloc_1914_, 1, v___x_1901_);
v___x_1903_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
lean_object* v_m_1905_; 
if (v_isShared_1873_ == 0)
{
lean_ctor_set_tag(v___x_1872_, 7);
lean_ctor_set(v___x_1872_, 1, v_a_1897_);
lean_ctor_set(v___x_1872_, 0, v___x_1903_);
v_m_1905_ = v___x_1872_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___x_1903_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v_a_1897_);
v_m_1905_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; double v___x_1908_; lean_object* v_data_1909_; 
v___x_1906_ = lean_box(v_result_1898_);
v___x_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1906_);
v___x_1908_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0);
lean_inc_ref(v_tag_1858_);
lean_inc_ref(v___x_1907_);
lean_inc(v_cls_1856_);
v_data_1909_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1909_, 0, v_cls_1856_);
lean_ctor_set(v_data_1909_, 1, v___x_1907_);
lean_ctor_set(v_data_1909_, 2, v_tag_1858_);
lean_ctor_set_float(v_data_1909_, sizeof(void*)*3, v___x_1908_);
lean_ctor_set_float(v_data_1909_, sizeof(void*)*3 + 8, v___x_1908_);
lean_ctor_set_uint8(v_data_1909_, sizeof(void*)*3 + 16, v_collapsed_1857_);
if (v___x_1894_ == 0)
{
lean_dec_ref(v___x_1907_);
lean_dec(v_snd_1889_);
lean_dec(v_fst_1888_);
lean_dec_ref(v_tag_1858_);
lean_dec(v_cls_1856_);
v___y_1875_ = v_m_1905_;
v___y_1876_ = v___y_1896_;
v_data_1877_ = v_data_1909_;
goto v___jp_1874_;
}
else
{
lean_object* v_data_1910_; double v___x_1911_; double v___x_1912_; 
lean_dec_ref(v_data_1909_);
v_data_1910_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1910_, 0, v_cls_1856_);
lean_ctor_set(v_data_1910_, 1, v___x_1907_);
lean_ctor_set(v_data_1910_, 2, v_tag_1858_);
v___x_1911_ = lean_unbox_float(v_fst_1888_);
lean_dec(v_fst_1888_);
lean_ctor_set_float(v_data_1910_, sizeof(void*)*3, v___x_1911_);
v___x_1912_ = lean_unbox_float(v_snd_1889_);
lean_dec(v_snd_1889_);
lean_ctor_set_float(v_data_1910_, sizeof(void*)*3 + 8, v___x_1912_);
lean_ctor_set_uint8(v_data_1910_, sizeof(void*)*3 + 16, v_collapsed_1857_);
v___y_1875_ = v_m_1905_;
v___y_1876_ = v___y_1896_;
v_data_1877_ = v_data_1910_;
goto v___jp_1874_;
}
}
}
}
v___jp_1915_:
{
lean_object* v_ref_1916_; lean_object* v___x_1917_; 
v_ref_1916_ = lean_ctor_get(v___y_1866_, 5);
lean_inc(v___y_1867_);
lean_inc_ref(v___y_1866_);
lean_inc(v___y_1865_);
lean_inc_ref(v___y_1864_);
lean_inc(v_fst_1869_);
v___x_1917_ = lean_apply_6(v_msg_1862_, v_fst_1869_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, lean_box(0));
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref(v___x_1917_);
v___y_1896_ = v_ref_1916_;
v_a_1897_ = v_a_1918_;
goto v___jp_1895_;
}
else
{
lean_object* v___x_1919_; 
lean_dec_ref(v___x_1917_);
v___x_1919_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2);
v___y_1896_ = v_ref_1916_;
v_a_1897_ = v___x_1919_;
goto v___jp_1895_;
}
}
v___jp_1920_:
{
if (v_clsEnabled_1860_ == 0)
{
if (v___y_1921_ == 0)
{
lean_object* v___x_1922_; lean_object* v_traceState_1923_; lean_object* v_env_1924_; lean_object* v_nextMacroScope_1925_; lean_object* v_ngen_1926_; lean_object* v_auxDeclNGen_1927_; lean_object* v_cache_1928_; lean_object* v_messages_1929_; lean_object* v_infoState_1930_; lean_object* v_snapshotTasks_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1950_; 
lean_del_object(v___x_1891_);
lean_dec(v_snd_1889_);
lean_dec(v_fst_1888_);
lean_del_object(v___x_1872_);
lean_dec_ref(v_msg_1862_);
lean_dec_ref(v_tag_1858_);
lean_dec(v_cls_1856_);
v___x_1922_ = lean_st_ref_take(v___y_1867_);
v_traceState_1923_ = lean_ctor_get(v___x_1922_, 4);
v_env_1924_ = lean_ctor_get(v___x_1922_, 0);
v_nextMacroScope_1925_ = lean_ctor_get(v___x_1922_, 1);
v_ngen_1926_ = lean_ctor_get(v___x_1922_, 2);
v_auxDeclNGen_1927_ = lean_ctor_get(v___x_1922_, 3);
v_cache_1928_ = lean_ctor_get(v___x_1922_, 5);
v_messages_1929_ = lean_ctor_get(v___x_1922_, 6);
v_infoState_1930_ = lean_ctor_get(v___x_1922_, 7);
v_snapshotTasks_1931_ = lean_ctor_get(v___x_1922_, 8);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1933_ = v___x_1922_;
v_isShared_1934_ = v_isSharedCheck_1950_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_snapshotTasks_1931_);
lean_inc(v_infoState_1930_);
lean_inc(v_messages_1929_);
lean_inc(v_cache_1928_);
lean_inc(v_traceState_1923_);
lean_inc(v_auxDeclNGen_1927_);
lean_inc(v_ngen_1926_);
lean_inc(v_nextMacroScope_1925_);
lean_inc(v_env_1924_);
lean_dec(v___x_1922_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1950_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
uint64_t v_tid_1935_; lean_object* v_traces_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1949_; 
v_tid_1935_ = lean_ctor_get_uint64(v_traceState_1923_, sizeof(void*)*1);
v_traces_1936_ = lean_ctor_get(v_traceState_1923_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v_traceState_1923_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1938_ = v_traceState_1923_;
v_isShared_1939_ = v_isSharedCheck_1949_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_traces_1936_);
lean_dec(v_traceState_1923_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1949_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1940_; lean_object* v___x_1942_; 
v___x_1940_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1861_, v_traces_1936_);
lean_dec_ref(v_traces_1936_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 0, v___x_1940_);
v___x_1942_ = v___x_1938_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1940_);
lean_ctor_set_uint64(v_reuseFailAlloc_1948_, sizeof(void*)*1, v_tid_1935_);
v___x_1942_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
lean_object* v___x_1944_; 
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 4, v___x_1942_);
v___x_1944_ = v___x_1933_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_env_1924_);
lean_ctor_set(v_reuseFailAlloc_1947_, 1, v_nextMacroScope_1925_);
lean_ctor_set(v_reuseFailAlloc_1947_, 2, v_ngen_1926_);
lean_ctor_set(v_reuseFailAlloc_1947_, 3, v_auxDeclNGen_1927_);
lean_ctor_set(v_reuseFailAlloc_1947_, 4, v___x_1942_);
lean_ctor_set(v_reuseFailAlloc_1947_, 5, v_cache_1928_);
lean_ctor_set(v_reuseFailAlloc_1947_, 6, v_messages_1929_);
lean_ctor_set(v_reuseFailAlloc_1947_, 7, v_infoState_1930_);
lean_ctor_set(v_reuseFailAlloc_1947_, 8, v_snapshotTasks_1931_);
v___x_1944_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1945_ = lean_st_ref_set(v___y_1867_, v___x_1944_);
v___x_1946_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4___redArg(v_fst_1869_);
return v___x_1946_;
}
}
}
}
}
else
{
goto v___jp_1915_;
}
}
else
{
goto v___jp_1915_;
}
}
v___jp_1951_:
{
double v___x_1953_; double v___x_1954_; double v___x_1955_; uint8_t v___x_1956_; 
v___x_1953_ = lean_unbox_float(v_snd_1889_);
v___x_1954_ = lean_unbox_float(v_fst_1888_);
v___x_1955_ = lean_float_sub(v___x_1953_, v___x_1954_);
v___x_1956_ = lean_float_decLt(v___y_1952_, v___x_1955_);
v___y_1921_ = v___x_1956_;
goto v___jp_1920_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___boxed(lean_object* v_cls_1969_, lean_object* v_collapsed_1970_, lean_object* v_tag_1971_, lean_object* v_opts_1972_, lean_object* v_clsEnabled_1973_, lean_object* v_oldTraces_1974_, lean_object* v_msg_1975_, lean_object* v_resStartStop_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
uint8_t v_collapsed_boxed_1982_; uint8_t v_clsEnabled_boxed_1983_; lean_object* v_res_1984_; 
v_collapsed_boxed_1982_ = lean_unbox(v_collapsed_1970_);
v_clsEnabled_boxed_1983_ = lean_unbox(v_clsEnabled_1973_);
v_res_1984_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v_cls_1969_, v_collapsed_boxed_1982_, v_tag_1971_, v_opts_1972_, v_clsEnabled_boxed_1983_, v_oldTraces_1974_, v_msg_1975_, v_resStartStop_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec_ref(v_opts_1972_);
return v_res_1984_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2(void){
_start:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1988_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_1989_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__1));
v___x_1990_ = l_Lean_Name_append(v___x_1989_, v___x_1988_);
return v___x_1990_;
}
}
static double _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3(void){
_start:
{
lean_object* v___x_1991_; double v___x_1992_; 
v___x_1991_ = lean_unsigned_to_nat(1000000000u);
v___x_1992_ = lean_float_of_nat(v___x_1991_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(lean_object* v_cfg_1993_, lean_object* v_act_1994_, lean_object* v_allowFailure_1995_, lean_object* v_cand_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_){
_start:
{
lean_object* v_fst_2002_; lean_object* v_snd_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2289_; 
v_fst_2002_ = lean_ctor_get(v_cand_1996_, 0);
v_snd_2003_ = lean_ctor_get(v_cand_1996_, 1);
v_isSharedCheck_2289_ = !lean_is_exclusive(v_cand_1996_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2005_ = v_cand_1996_;
v_isShared_2006_ = v_isSharedCheck_2289_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_snd_2003_);
lean_inc(v_fst_2002_);
lean_dec(v_cand_1996_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2289_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v_options_2007_; uint8_t v_hasTrace_2008_; 
v_options_2007_ = lean_ctor_get(v_a_1999_, 2);
v_hasTrace_2008_ = lean_ctor_get_uint8(v_options_2007_, sizeof(void*)*1);
if (v_hasTrace_2008_ == 0)
{
lean_object* v_fst_2009_; lean_object* v_snd_2010_; lean_object* v_fst_2011_; lean_object* v_snd_2012_; lean_object* v___x_2013_; lean_object* v_cache_2014_; lean_object* v_zetaDeltaFVarIds_2015_; lean_object* v_postponed_2016_; lean_object* v_diag_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2065_; 
lean_del_object(v___x_2005_);
v_fst_2009_ = lean_ctor_get(v_fst_2002_, 0);
lean_inc(v_fst_2009_);
v_snd_2010_ = lean_ctor_get(v_fst_2002_, 1);
lean_inc(v_snd_2010_);
lean_dec(v_fst_2002_);
v_fst_2011_ = lean_ctor_get(v_snd_2003_, 0);
lean_inc(v_fst_2011_);
v_snd_2012_ = lean_ctor_get(v_snd_2003_, 1);
lean_inc(v_snd_2012_);
lean_dec(v_snd_2003_);
v___x_2013_ = lean_st_ref_take(v_a_1998_);
v_cache_2014_ = lean_ctor_get(v___x_2013_, 1);
v_zetaDeltaFVarIds_2015_ = lean_ctor_get(v___x_2013_, 2);
v_postponed_2016_ = lean_ctor_get(v___x_2013_, 3);
v_diag_2017_ = lean_ctor_get(v___x_2013_, 4);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2065_ == 0)
{
lean_object* v_unused_2066_; 
v_unused_2066_ = lean_ctor_get(v___x_2013_, 0);
lean_dec(v_unused_2066_);
v___x_2019_ = v___x_2013_;
v_isShared_2020_ = v_isSharedCheck_2065_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_diag_2017_);
lean_inc(v_postponed_2016_);
lean_inc(v_zetaDeltaFVarIds_2015_);
lean_inc(v_cache_2014_);
lean_dec(v___x_2013_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2065_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v_snd_2010_);
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_snd_2010_);
lean_ctor_set(v_reuseFailAlloc_2064_, 1, v_cache_2014_);
lean_ctor_set(v_reuseFailAlloc_2064_, 2, v_zetaDeltaFVarIds_2015_);
lean_ctor_set(v_reuseFailAlloc_2064_, 3, v_postponed_2016_);
lean_ctor_set(v_reuseFailAlloc_2064_, 4, v_diag_2017_);
v___x_2022_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
lean_object* v___x_2023_; uint8_t v___x_2024_; lean_object* v___x_2025_; 
v___x_2023_ = lean_st_ref_set(v_a_1998_, v___x_2022_);
v___x_2024_ = lean_unbox(v_snd_2012_);
lean_dec(v_snd_2012_);
v___x_2025_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_2011_, v___x_2024_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_a_2026_);
lean_dec_ref(v___x_2025_);
v___x_2027_ = lean_box(0);
lean_inc(v_fst_2009_);
v___x_2028_ = l_Lean_MVarId_apply(v_fst_2009_, v_a_2026_, v_cfg_1993_, v___x_2027_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v_a_2029_; lean_object* v___x_2030_; 
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
lean_inc_n(v_a_2029_, 2);
lean_dec_ref(v___x_2028_);
lean_inc(v_a_2000_);
lean_inc_ref(v_a_1999_);
lean_inc(v_a_1998_);
lean_inc_ref(v_a_1997_);
v___x_2030_ = lean_apply_6(v_act_1994_, v_a_2029_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, lean_box(0));
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_dec(v_a_2029_);
lean_dec(v_fst_2009_);
lean_dec_ref(v_allowFailure_1995_);
return v___x_2030_;
}
else
{
lean_object* v_a_2031_; uint8_t v___y_2033_; uint8_t v___x_2054_; 
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
lean_inc(v_a_2031_);
v___x_2054_ = l_Lean_Exception_isInterrupt(v_a_2031_);
if (v___x_2054_ == 0)
{
uint8_t v___x_2055_; 
v___x_2055_ = l_Lean_Exception_isRuntime(v_a_2031_);
v___y_2033_ = v___x_2055_;
goto v___jp_2032_;
}
else
{
lean_dec(v_a_2031_);
v___y_2033_ = v___x_2054_;
goto v___jp_2032_;
}
v___jp_2032_:
{
if (v___y_2033_ == 0)
{
lean_object* v___x_2034_; 
lean_dec_ref(v___x_2030_);
lean_inc(v_a_2000_);
lean_inc_ref(v_a_1999_);
lean_inc(v_a_1998_);
lean_inc_ref(v_a_1997_);
v___x_2034_ = lean_apply_6(v_allowFailure_1995_, v_fst_2009_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, lean_box(0));
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2045_; 
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2037_ = v___x_2034_;
v_isShared_2038_ = v_isSharedCheck_2045_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2034_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2045_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
uint8_t v___x_2039_; 
v___x_2039_ = lean_unbox(v_a_2035_);
lean_dec(v_a_2035_);
if (v___x_2039_ == 0)
{
lean_object* v___x_2040_; lean_object* v___x_2041_; 
lean_del_object(v___x_2037_);
lean_dec(v_a_2029_);
v___x_2040_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1);
v___x_2041_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2040_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_);
return v___x_2041_;
}
else
{
lean_object* v___x_2043_; 
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 0, v_a_2029_);
v___x_2043_ = v___x_2037_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2029_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
else
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2053_; 
lean_dec(v_a_2029_);
v_a_2046_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2048_ = v___x_2034_;
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_2034_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2051_; 
if (v_isShared_2049_ == 0)
{
v___x_2051_ = v___x_2048_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_a_2046_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
else
{
lean_dec(v_a_2029_);
lean_dec(v_fst_2009_);
lean_dec_ref(v_allowFailure_1995_);
return v___x_2030_;
}
}
}
}
else
{
lean_dec(v_fst_2009_);
lean_dec_ref(v_allowFailure_1995_);
lean_dec_ref(v_act_1994_);
return v___x_2028_;
}
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
lean_dec(v_fst_2009_);
lean_dec_ref(v_allowFailure_1995_);
lean_dec_ref(v_act_1994_);
lean_dec_ref(v_cfg_1993_);
v_a_2056_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_2025_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2025_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2056_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
}
}
else
{
lean_object* v_fst_2067_; lean_object* v_snd_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2288_; 
v_fst_2067_ = lean_ctor_get(v_fst_2002_, 0);
v_snd_2068_ = lean_ctor_get(v_fst_2002_, 1);
v_isSharedCheck_2288_ = !lean_is_exclusive(v_fst_2002_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2070_ = v_fst_2002_;
v_isShared_2071_ = v_isSharedCheck_2288_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_snd_2068_);
lean_inc(v_fst_2067_);
lean_dec(v_fst_2002_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2288_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v_fst_2072_; lean_object* v_snd_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2287_; 
v_fst_2072_ = lean_ctor_get(v_snd_2003_, 0);
v_snd_2073_ = lean_ctor_get(v_snd_2003_, 1);
v_isSharedCheck_2287_ = !lean_is_exclusive(v_snd_2003_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2075_ = v_snd_2003_;
v_isShared_2076_ = v_isSharedCheck_2287_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_snd_2073_);
lean_inc(v_fst_2072_);
lean_dec(v_snd_2003_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2287_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v_inheritedTraceOptions_2077_; lean_object* v___f_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; uint8_t v___x_2082_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v_a_2086_; lean_object* v___y_2103_; lean_object* v___y_2104_; lean_object* v_a_2105_; lean_object* v___y_2108_; lean_object* v___y_2109_; lean_object* v_a_2110_; lean_object* v___y_2113_; lean_object* v___y_2114_; lean_object* v___y_2115_; lean_object* v___y_2119_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v___y_2122_; uint8_t v___y_2123_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v_a_2133_; lean_object* v___y_2145_; lean_object* v___y_2146_; lean_object* v_a_2147_; lean_object* v___y_2150_; lean_object* v___y_2151_; lean_object* v_a_2152_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2161_; lean_object* v___y_2162_; lean_object* v___y_2163_; lean_object* v___y_2164_; uint8_t v___y_2165_; 
v_inheritedTraceOptions_2077_ = lean_ctor_get(v_a_1999_, 13);
lean_inc(v_snd_2073_);
lean_inc(v_fst_2072_);
v___f_2078_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2078_, 0, v_fst_2072_);
lean_closure_set(v___f_2078_, 1, v_snd_2073_);
v___x_2079_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_2080_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__4));
v___x_2081_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2);
v___x_2082_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2077_, v_options_2007_, v___x_2081_);
if (v___x_2082_ == 0)
{
lean_object* v___x_2231_; uint8_t v___x_2232_; 
v___x_2231_ = l_Lean_trace_profiler;
v___x_2232_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_2007_, v___x_2231_);
if (v___x_2232_ == 0)
{
lean_object* v___x_2233_; lean_object* v_cache_2234_; lean_object* v_zetaDeltaFVarIds_2235_; lean_object* v_postponed_2236_; lean_object* v_diag_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2285_; 
lean_dec_ref(v___f_2078_);
lean_del_object(v___x_2075_);
lean_del_object(v___x_2070_);
lean_del_object(v___x_2005_);
v___x_2233_ = lean_st_ref_take(v_a_1998_);
v_cache_2234_ = lean_ctor_get(v___x_2233_, 1);
v_zetaDeltaFVarIds_2235_ = lean_ctor_get(v___x_2233_, 2);
v_postponed_2236_ = lean_ctor_get(v___x_2233_, 3);
v_diag_2237_ = lean_ctor_get(v___x_2233_, 4);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2285_ == 0)
{
lean_object* v_unused_2286_; 
v_unused_2286_ = lean_ctor_get(v___x_2233_, 0);
lean_dec(v_unused_2286_);
v___x_2239_ = v___x_2233_;
v_isShared_2240_ = v_isSharedCheck_2285_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_diag_2237_);
lean_inc(v_postponed_2236_);
lean_inc(v_zetaDeltaFVarIds_2235_);
lean_inc(v_cache_2234_);
lean_dec(v___x_2233_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2285_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2242_; 
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 0, v_snd_2068_);
v___x_2242_ = v___x_2239_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_snd_2068_);
lean_ctor_set(v_reuseFailAlloc_2284_, 1, v_cache_2234_);
lean_ctor_set(v_reuseFailAlloc_2284_, 2, v_zetaDeltaFVarIds_2235_);
lean_ctor_set(v_reuseFailAlloc_2284_, 3, v_postponed_2236_);
lean_ctor_set(v_reuseFailAlloc_2284_, 4, v_diag_2237_);
v___x_2242_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
lean_object* v___x_2243_; uint8_t v___x_2244_; lean_object* v___x_2245_; 
v___x_2243_ = lean_st_ref_set(v_a_1998_, v___x_2242_);
v___x_2244_ = lean_unbox(v_snd_2073_);
lean_dec(v_snd_2073_);
v___x_2245_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_2072_, v___x_2244_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v_a_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
v_a_2246_ = lean_ctor_get(v___x_2245_, 0);
lean_inc(v_a_2246_);
lean_dec_ref(v___x_2245_);
v___x_2247_ = lean_box(0);
lean_inc(v_fst_2067_);
v___x_2248_ = l_Lean_MVarId_apply(v_fst_2067_, v_a_2246_, v_cfg_1993_, v___x_2247_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_);
if (lean_obj_tag(v___x_2248_) == 0)
{
lean_object* v_a_2249_; lean_object* v___x_2250_; 
v_a_2249_ = lean_ctor_get(v___x_2248_, 0);
lean_inc_n(v_a_2249_, 2);
lean_dec_ref(v___x_2248_);
lean_inc(v_a_2000_);
lean_inc_ref(v_a_1999_);
lean_inc(v_a_1998_);
lean_inc_ref(v_a_1997_);
v___x_2250_ = lean_apply_6(v_act_1994_, v_a_2249_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, lean_box(0));
if (lean_obj_tag(v___x_2250_) == 0)
{
lean_dec(v_a_2249_);
lean_dec(v_fst_2067_);
lean_dec_ref(v_allowFailure_1995_);
return v___x_2250_;
}
else
{
lean_object* v_a_2251_; uint8_t v___y_2253_; uint8_t v___x_2274_; 
v_a_2251_ = lean_ctor_get(v___x_2250_, 0);
lean_inc(v_a_2251_);
v___x_2274_ = l_Lean_Exception_isInterrupt(v_a_2251_);
if (v___x_2274_ == 0)
{
uint8_t v___x_2275_; 
v___x_2275_ = l_Lean_Exception_isRuntime(v_a_2251_);
v___y_2253_ = v___x_2275_;
goto v___jp_2252_;
}
else
{
lean_dec(v_a_2251_);
v___y_2253_ = v___x_2274_;
goto v___jp_2252_;
}
v___jp_2252_:
{
if (v___y_2253_ == 0)
{
lean_object* v___x_2254_; 
lean_dec_ref(v___x_2250_);
lean_inc(v_a_2000_);
lean_inc_ref(v_a_1999_);
lean_inc(v_a_1998_);
lean_inc_ref(v_a_1997_);
v___x_2254_ = lean_apply_6(v_allowFailure_1995_, v_fst_2067_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, lean_box(0));
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2265_; 
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2257_ = v___x_2254_;
v_isShared_2258_ = v_isSharedCheck_2265_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2254_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2265_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
uint8_t v___x_2259_; 
v___x_2259_ = lean_unbox(v_a_2255_);
lean_dec(v_a_2255_);
if (v___x_2259_ == 0)
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
lean_del_object(v___x_2257_);
lean_dec(v_a_2249_);
v___x_2260_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1);
v___x_2261_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2260_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_);
return v___x_2261_;
}
else
{
lean_object* v___x_2263_; 
if (v_isShared_2258_ == 0)
{
lean_ctor_set(v___x_2257_, 0, v_a_2249_);
v___x_2263_ = v___x_2257_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_a_2249_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
lean_dec(v_a_2249_);
v_a_2266_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___x_2254_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2254_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2266_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
else
{
lean_dec(v_a_2249_);
lean_dec(v_fst_2067_);
lean_dec_ref(v_allowFailure_1995_);
return v___x_2250_;
}
}
}
}
else
{
lean_dec(v_fst_2067_);
lean_dec_ref(v_allowFailure_1995_);
lean_dec_ref(v_act_1994_);
return v___x_2248_;
}
}
else
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
lean_dec(v_fst_2067_);
lean_dec_ref(v_allowFailure_1995_);
lean_dec_ref(v_act_1994_);
lean_dec_ref(v_cfg_1993_);
v_a_2276_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2245_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2245_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2281_; 
if (v_isShared_2279_ == 0)
{
v___x_2281_ = v___x_2278_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2276_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
}
}
else
{
goto v___jp_2172_;
}
}
else
{
goto v___jp_2172_;
}
v___jp_2083_:
{
lean_object* v___x_2087_; double v___x_2088_; double v___x_2089_; double v___x_2090_; double v___x_2091_; double v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2096_; 
v___x_2087_ = lean_io_mono_nanos_now();
v___x_2088_ = lean_float_of_nat(v___y_2084_);
v___x_2089_ = lean_float_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3);
v___x_2090_ = lean_float_div(v___x_2088_, v___x_2089_);
v___x_2091_ = lean_float_of_nat(v___x_2087_);
v___x_2092_ = lean_float_div(v___x_2091_, v___x_2089_);
v___x_2093_ = lean_box_float(v___x_2090_);
v___x_2094_ = lean_box_float(v___x_2092_);
if (v_isShared_2076_ == 0)
{
lean_ctor_set(v___x_2075_, 1, v___x_2094_);
lean_ctor_set(v___x_2075_, 0, v___x_2093_);
v___x_2096_ = v___x_2075_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v___x_2093_);
lean_ctor_set(v_reuseFailAlloc_2101_, 1, v___x_2094_);
v___x_2096_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
lean_object* v___x_2098_; 
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 1, v___x_2096_);
lean_ctor_set(v___x_2070_, 0, v_a_2086_);
v___x_2098_ = v___x_2070_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2086_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v___x_2096_);
v___x_2098_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
lean_object* v___x_2099_; 
v___x_2099_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v___x_2079_, v_hasTrace_2008_, v___x_2080_, v_options_2007_, v___x_2082_, v___y_2085_, v___f_2078_, v___x_2098_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_);
return v___x_2099_;
}
}
}
v___jp_2102_:
{
lean_object* v___x_2106_; 
v___x_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2106_, 0, v_a_2105_);
v___y_2084_ = v___y_2103_;
v___y_2085_ = v___y_2104_;
v_a_2086_ = v___x_2106_;
goto v___jp_2083_;
}
v___jp_2107_:
{
lean_object* v___x_2111_; 
v___x_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2111_, 0, v_a_2110_);
v___y_2084_ = v___y_2108_;
v___y_2085_ = v___y_2109_;
v_a_2086_ = v___x_2111_;
goto v___jp_2083_;
}
v___jp_2112_:
{
if (lean_obj_tag(v___y_2115_) == 0)
{
lean_object* v_a_2116_; 
v_a_2116_ = lean_ctor_get(v___y_2115_, 0);
lean_inc(v_a_2116_);
lean_dec_ref(v___y_2115_);
v___y_2103_ = v___y_2113_;
v___y_2104_ = v___y_2114_;
v_a_2105_ = v_a_2116_;
goto v___jp_2102_;
}
else
{
lean_object* v_a_2117_; 
v_a_2117_ = lean_ctor_get(v___y_2115_, 0);
lean_inc(v_a_2117_);
lean_dec_ref(v___y_2115_);
v___y_2108_ = v___y_2113_;
v___y_2109_ = v___y_2114_;
v_a_2110_ = v_a_2117_;
goto v___jp_2107_;
}
}
v___jp_2118_:
{
if (v___y_2123_ == 0)
{
lean_object* v___x_2124_; 
lean_dec_ref(v___y_2120_);
lean_inc(v_a_2000_);
lean_inc_ref(v_a_1999_);
lean_inc(v_a_1998_);
lean_inc_ref(v_a_1997_);
v___x_2124_ = lean_apply_6(v_allowFailure_1995_, v_fst_2067_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, lean_box(0));
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; uint8_t v___x_2126_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_a_2125_);
lean_dec_ref(v___x_2124_);
v___x_2126_ = lean_unbox(v_a_2125_);
lean_dec(v_a_2125_);
if (v___x_2126_ == 0)
{
lean_object* v___x_2127_; lean_object* v___x_2128_; 
lean_dec(v___y_2119_);
v___x_2127_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1);
v___x_2128_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2127_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_);
v___y_2113_ = v___y_2121_;
v___y_2114_ = v___y_2122_;
v___y_2115_ = v___x_2128_;
goto v___jp_2112_;
}
else
{
v___y_2103_ = v___y_2121_;
v___y_2104_ = v___y_2122_;
v_a_2105_ = v___y_2119_;
goto v___jp_2102_;
}
}
else
{
lean_object* v_a_2129_; 
lean_dec(v___y_2119_);
v_a_2129_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_a_2129_);
lean_dec_ref(v___x_2124_);
v___y_2108_ = v___y_2121_;
v___y_2109_ = v___y_2122_;
v_a_2110_ = v_a_2129_;
goto v___jp_2107_;
}
}
else
{
lean_dec(v___y_2119_);
lean_dec(v_fst_2067_);
lean_dec_ref(v_allowFailure_1995_);
v___y_2108_ = v___y_2121_;
v___y_2109_ = v___y_2122_;
v_a_2110_ = v___y_2120_;
goto v___jp_2107_;
}
}
v___jp_2130_:
{
lean_object* v___x_2134_; double v___x_2135_; double v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2140_; 
v___x_2134_ = lean_io_get_num_heartbeats();
v___x_2135_ = lean_float_of_nat(v___y_2131_);
v___x_2136_ = lean_float_of_nat(v___x_2134_);
v___x_2137_ = lean_box_float(v___x_2135_);
v___x_2138_ = lean_box_float(v___x_2136_);
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 1, v___x_2138_);
lean_ctor_set(v___x_2005_, 0, v___x_2137_);
v___x_2140_ = v___x_2005_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2137_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v___x_2138_);
v___x_2140_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2141_, 0, v_a_2133_);
lean_ctor_set(v___x_2141_, 1, v___x_2140_);
v___x_2142_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v___x_2079_, v_hasTrace_2008_, v___x_2080_, v_options_2007_, v___x_2082_, v___y_2132_, v___f_2078_, v___x_2141_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_);
return v___x_2142_;
}
}
v___jp_2144_:
{
lean_object* v___x_2148_; 
v___x_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2148_, 0, v_a_2147_);
v___y_2131_ = v___y_2145_;
v___y_2132_ = v___y_2146_;
v_a_2133_ = v___x_2148_;
goto v___jp_2130_;
}
v___jp_2149_:
{
lean_object* v___x_2153_; 
v___x_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2153_, 0, v_a_2152_);
v___y_2131_ = v___y_2150_;
v___y_2132_ = v___y_2151_;
v_a_2133_ = v___x_2153_;
goto v___jp_2130_;
}
v___jp_2154_:
{
if (lean_obj_tag(v___y_2157_) == 0)
{
lean_object* v_a_2158_; 
v_a_2158_ = lean_ctor_get(v___y_2157_, 0);
lean_inc(v_a_2158_);
lean_dec_ref(v___y_2157_);
v___y_2145_ = v___y_2155_;
v___y_2146_ = v___y_2156_;
v_a_2147_ = v_a_2158_;
goto v___jp_2144_;
}
else
{
lean_object* v_a_2159_; 
v_a_2159_ = lean_ctor_get(v___y_2157_, 0);
lean_inc(v_a_2159_);
lean_dec_ref(v___y_2157_);
v___y_2150_ = v___y_2155_;
v___y_2151_ = v___y_2156_;
v_a_2152_ = v_a_2159_;
goto v___jp_2149_;
}
}
v___jp_2160_:
{
if (v___y_2165_ == 0)
{
lean_object* v___x_2166_; 
lean_dec_ref(v___y_2161_);
lean_inc(v_a_2000_);
lean_inc_ref(v_a_1999_);
lean_inc(v_a_1998_);
lean_inc_ref(v_a_1997_);
v___x_2166_ = lean_apply_6(v_allowFailure_1995_, v_fst_2067_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, lean_box(0));
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_a_2167_; uint8_t v___x_2168_; 
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_a_2167_);
lean_dec_ref(v___x_2166_);
v___x_2168_ = lean_unbox(v_a_2167_);
lean_dec(v_a_2167_);
if (v___x_2168_ == 0)
{
lean_object* v___x_2169_; lean_object* v___x_2170_; 
lean_dec(v___y_2162_);
v___x_2169_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1);
v___x_2170_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2169_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_);
v___y_2155_ = v___y_2163_;
v___y_2156_ = v___y_2164_;
v___y_2157_ = v___x_2170_;
goto v___jp_2154_;
}
else
{
v___y_2145_ = v___y_2163_;
v___y_2146_ = v___y_2164_;
v_a_2147_ = v___y_2162_;
goto v___jp_2144_;
}
}
else
{
lean_object* v_a_2171_; 
lean_dec(v___y_2162_);
v_a_2171_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_a_2171_);
lean_dec_ref(v___x_2166_);
v___y_2150_ = v___y_2163_;
v___y_2151_ = v___y_2164_;
v_a_2152_ = v_a_2171_;
goto v___jp_2149_;
}
}
else
{
lean_dec(v___y_2162_);
lean_dec(v_fst_2067_);
lean_dec_ref(v_allowFailure_1995_);
v___y_2150_ = v___y_2163_;
v___y_2151_ = v___y_2164_;
v_a_2152_ = v___y_2161_;
goto v___jp_2149_;
}
}
v___jp_2172_:
{
lean_object* v___x_2173_; lean_object* v_a_2174_; lean_object* v___x_2175_; uint8_t v___x_2176_; 
v___x_2173_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v_a_2000_);
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
lean_inc(v_a_2174_);
lean_dec_ref(v___x_2173_);
v___x_2175_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2176_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_2007_, v___x_2175_);
if (v___x_2176_ == 0)
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v_cache_2179_; lean_object* v_zetaDeltaFVarIds_2180_; lean_object* v_postponed_2181_; lean_object* v_diag_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2202_; 
lean_del_object(v___x_2005_);
v___x_2177_ = lean_io_mono_nanos_now();
v___x_2178_ = lean_st_ref_take(v_a_1998_);
v_cache_2179_ = lean_ctor_get(v___x_2178_, 1);
v_zetaDeltaFVarIds_2180_ = lean_ctor_get(v___x_2178_, 2);
v_postponed_2181_ = lean_ctor_get(v___x_2178_, 3);
v_diag_2182_ = lean_ctor_get(v___x_2178_, 4);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2202_ == 0)
{
lean_object* v_unused_2203_; 
v_unused_2203_ = lean_ctor_get(v___x_2178_, 0);
lean_dec(v_unused_2203_);
v___x_2184_ = v___x_2178_;
v_isShared_2185_ = v_isSharedCheck_2202_;
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
v_isShared_2185_ = v_isSharedCheck_2202_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
lean_ctor_set(v___x_2184_, 0, v_snd_2068_);
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_snd_2068_);
lean_ctor_set(v_reuseFailAlloc_2201_, 1, v_cache_2179_);
lean_ctor_set(v_reuseFailAlloc_2201_, 2, v_zetaDeltaFVarIds_2180_);
lean_ctor_set(v_reuseFailAlloc_2201_, 3, v_postponed_2181_);
lean_ctor_set(v_reuseFailAlloc_2201_, 4, v_diag_2182_);
v___x_2187_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
lean_object* v___x_2188_; uint8_t v___x_2189_; lean_object* v___x_2190_; 
v___x_2188_ = lean_st_ref_set(v_a_1998_, v___x_2187_);
v___x_2189_ = lean_unbox(v_snd_2073_);
lean_dec(v_snd_2073_);
v___x_2190_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_2072_, v___x_2189_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_a_2191_);
lean_dec_ref(v___x_2190_);
v___x_2192_ = lean_box(0);
lean_inc(v_fst_2067_);
v___x_2193_ = l_Lean_MVarId_apply(v_fst_2067_, v_a_2191_, v_cfg_1993_, v___x_2192_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; lean_object* v___x_2195_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
lean_inc_n(v_a_2194_, 2);
lean_dec_ref(v___x_2193_);
lean_inc(v_a_2000_);
lean_inc_ref(v_a_1999_);
lean_inc(v_a_1998_);
lean_inc_ref(v_a_1997_);
v___x_2195_ = lean_apply_6(v_act_1994_, v_a_2194_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, lean_box(0));
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; 
lean_dec(v_a_2194_);
lean_dec(v_fst_2067_);
lean_dec_ref(v_allowFailure_1995_);
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2196_);
lean_dec_ref(v___x_2195_);
v___y_2103_ = v___x_2177_;
v___y_2104_ = v_a_2174_;
v_a_2105_ = v_a_2196_;
goto v___jp_2102_;
}
else
{
lean_object* v_a_2197_; uint8_t v___x_2198_; 
v_a_2197_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2197_);
lean_dec_ref(v___x_2195_);
v___x_2198_ = l_Lean_Exception_isInterrupt(v_a_2197_);
if (v___x_2198_ == 0)
{
uint8_t v___x_2199_; 
lean_inc(v_a_2197_);
v___x_2199_ = l_Lean_Exception_isRuntime(v_a_2197_);
v___y_2119_ = v_a_2194_;
v___y_2120_ = v_a_2197_;
v___y_2121_ = v___x_2177_;
v___y_2122_ = v_a_2174_;
v___y_2123_ = v___x_2199_;
goto v___jp_2118_;
}
else
{
v___y_2119_ = v_a_2194_;
v___y_2120_ = v_a_2197_;
v___y_2121_ = v___x_2177_;
v___y_2122_ = v_a_2174_;
v___y_2123_ = v___x_2198_;
goto v___jp_2118_;
}
}
}
else
{
lean_dec(v_fst_2067_);
lean_dec_ref(v_allowFailure_1995_);
lean_dec_ref(v_act_1994_);
v___y_2113_ = v___x_2177_;
v___y_2114_ = v_a_2174_;
v___y_2115_ = v___x_2193_;
goto v___jp_2112_;
}
}
else
{
lean_object* v_a_2200_; 
lean_dec(v_fst_2067_);
lean_dec_ref(v_allowFailure_1995_);
lean_dec_ref(v_act_1994_);
lean_dec_ref(v_cfg_1993_);
v_a_2200_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_a_2200_);
lean_dec_ref(v___x_2190_);
v___y_2108_ = v___x_2177_;
v___y_2109_ = v_a_2174_;
v_a_2110_ = v_a_2200_;
goto v___jp_2107_;
}
}
}
}
else
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v_cache_2206_; lean_object* v_zetaDeltaFVarIds_2207_; lean_object* v_postponed_2208_; lean_object* v_diag_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2229_; 
lean_del_object(v___x_2075_);
lean_del_object(v___x_2070_);
v___x_2204_ = lean_io_get_num_heartbeats();
v___x_2205_ = lean_st_ref_take(v_a_1998_);
v_cache_2206_ = lean_ctor_get(v___x_2205_, 1);
v_zetaDeltaFVarIds_2207_ = lean_ctor_get(v___x_2205_, 2);
v_postponed_2208_ = lean_ctor_get(v___x_2205_, 3);
v_diag_2209_ = lean_ctor_get(v___x_2205_, 4);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2229_ == 0)
{
lean_object* v_unused_2230_; 
v_unused_2230_ = lean_ctor_get(v___x_2205_, 0);
lean_dec(v_unused_2230_);
v___x_2211_ = v___x_2205_;
v_isShared_2212_ = v_isSharedCheck_2229_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_diag_2209_);
lean_inc(v_postponed_2208_);
lean_inc(v_zetaDeltaFVarIds_2207_);
lean_inc(v_cache_2206_);
lean_dec(v___x_2205_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2229_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 0, v_snd_2068_);
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_snd_2068_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v_cache_2206_);
lean_ctor_set(v_reuseFailAlloc_2228_, 2, v_zetaDeltaFVarIds_2207_);
lean_ctor_set(v_reuseFailAlloc_2228_, 3, v_postponed_2208_);
lean_ctor_set(v_reuseFailAlloc_2228_, 4, v_diag_2209_);
v___x_2214_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
lean_object* v___x_2215_; uint8_t v___x_2216_; lean_object* v___x_2217_; 
v___x_2215_ = lean_st_ref_set(v_a_1998_, v___x_2214_);
v___x_2216_ = lean_unbox(v_snd_2073_);
lean_dec(v_snd_2073_);
v___x_2217_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_2072_, v___x_2216_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2218_);
lean_dec_ref(v___x_2217_);
v___x_2219_ = lean_box(0);
lean_inc(v_fst_2067_);
v___x_2220_ = l_Lean_MVarId_apply(v_fst_2067_, v_a_2218_, v_cfg_1993_, v___x_2219_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; lean_object* v___x_2222_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc_n(v_a_2221_, 2);
lean_dec_ref(v___x_2220_);
lean_inc(v_a_2000_);
lean_inc_ref(v_a_1999_);
lean_inc(v_a_1998_);
lean_inc_ref(v_a_1997_);
v___x_2222_ = lean_apply_6(v_act_1994_, v_a_2221_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, lean_box(0));
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_object* v_a_2223_; 
lean_dec(v_a_2221_);
lean_dec(v_fst_2067_);
lean_dec_ref(v_allowFailure_1995_);
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
lean_inc(v_a_2223_);
lean_dec_ref(v___x_2222_);
v___y_2145_ = v___x_2204_;
v___y_2146_ = v_a_2174_;
v_a_2147_ = v_a_2223_;
goto v___jp_2144_;
}
else
{
lean_object* v_a_2224_; uint8_t v___x_2225_; 
v_a_2224_ = lean_ctor_get(v___x_2222_, 0);
lean_inc(v_a_2224_);
lean_dec_ref(v___x_2222_);
v___x_2225_ = l_Lean_Exception_isInterrupt(v_a_2224_);
if (v___x_2225_ == 0)
{
uint8_t v___x_2226_; 
lean_inc(v_a_2224_);
v___x_2226_ = l_Lean_Exception_isRuntime(v_a_2224_);
v___y_2161_ = v_a_2224_;
v___y_2162_ = v_a_2221_;
v___y_2163_ = v___x_2204_;
v___y_2164_ = v_a_2174_;
v___y_2165_ = v___x_2226_;
goto v___jp_2160_;
}
else
{
v___y_2161_ = v_a_2224_;
v___y_2162_ = v_a_2221_;
v___y_2163_ = v___x_2204_;
v___y_2164_ = v_a_2174_;
v___y_2165_ = v___x_2225_;
goto v___jp_2160_;
}
}
}
else
{
lean_dec(v_fst_2067_);
lean_dec_ref(v_allowFailure_1995_);
lean_dec_ref(v_act_1994_);
v___y_2155_ = v___x_2204_;
v___y_2156_ = v_a_2174_;
v___y_2157_ = v___x_2220_;
goto v___jp_2154_;
}
}
else
{
lean_object* v_a_2227_; 
lean_dec(v_fst_2067_);
lean_dec_ref(v_allowFailure_1995_);
lean_dec_ref(v_act_1994_);
lean_dec_ref(v_cfg_1993_);
v_a_2227_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2227_);
lean_dec_ref(v___x_2217_);
v___y_2150_ = v___x_2204_;
v___y_2151_ = v_a_2174_;
v_a_2152_ = v_a_2227_;
goto v___jp_2149_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___boxed(lean_object* v_cfg_2290_, lean_object* v_act_2291_, lean_object* v_allowFailure_2292_, lean_object* v_cand_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_){
_start:
{
lean_object* v_res_2299_; 
v_res_2299_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(v_cfg_2290_, v_act_2291_, v_allowFailure_2292_, v_cand_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_);
lean_dec(v_a_2297_);
lean_dec_ref(v_a_2296_);
lean_dec(v_a_2295_);
lean_dec_ref(v_a_2294_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(lean_object* v_00_u03b1_2300_, lean_object* v_x_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4___redArg(v_x_2301_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2308_, lean_object* v_x_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(v_00_u03b1_2308_, v_x_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(lean_object* v_act_2318_, lean_object* v_a_2319_, uint8_t v_collectAll_2320_, lean_object* v_as_2321_, size_t v_sz_2322_, size_t v_i_2323_, lean_object* v_b_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v_a_2331_; uint8_t v___x_2335_; 
v___x_2335_ = lean_usize_dec_lt(v_i_2323_, v_sz_2322_);
if (v___x_2335_ == 0)
{
lean_object* v___x_2336_; 
lean_dec_ref(v_act_2318_);
v___x_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2336_, 0, v_b_2324_);
return v___x_2336_;
}
else
{
lean_object* v_snd_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2410_; 
v_snd_2337_ = lean_ctor_get(v_b_2324_, 1);
v_isSharedCheck_2410_ = !lean_is_exclusive(v_b_2324_);
if (v_isSharedCheck_2410_ == 0)
{
lean_object* v_unused_2411_; 
v_unused_2411_ = lean_ctor_get(v_b_2324_, 0);
lean_dec(v_unused_2411_);
v___x_2339_ = v_b_2324_;
v_isShared_2340_ = v_isSharedCheck_2410_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_snd_2337_);
lean_dec(v_b_2324_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2410_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2341_; lean_object* v_a_2342_; lean_object* v___x_2343_; 
v___x_2341_ = lean_box(0);
v_a_2342_ = lean_array_uget_borrowed(v_as_2321_, v_i_2323_);
lean_inc_ref(v_act_2318_);
lean_inc(v___y_2328_);
lean_inc_ref(v___y_2327_);
lean_inc(v___y_2326_);
lean_inc_ref(v___y_2325_);
lean_inc(v_a_2342_);
v___x_2343_ = lean_apply_6(v_act_2318_, v_a_2342_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, lean_box(0));
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2373_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2346_ = v___x_2343_;
v_isShared_2347_ = v_isSharedCheck_2373_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2343_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2373_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
uint8_t v___y_2366_; uint8_t v___x_2372_; 
v___x_2372_ = l_List_isEmpty___redArg(v_a_2344_);
if (v___x_2372_ == 0)
{
v___y_2366_ = v___x_2372_;
goto v___jp_2365_;
}
else
{
if (v_collectAll_2320_ == 0)
{
v___y_2366_ = v___x_2372_;
goto v___jp_2365_;
}
else
{
lean_del_object(v___x_2346_);
goto v___jp_2348_;
}
}
v___jp_2348_:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2349_ = lean_st_ref_get(v___y_2326_);
v___x_2350_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2319_, v___y_2326_, v___y_2328_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_mctx_2351_; lean_object* v___x_2353_; 
lean_dec_ref(v___x_2350_);
v_mctx_2351_ = lean_ctor_get(v___x_2349_, 0);
lean_inc_ref(v_mctx_2351_);
lean_dec(v___x_2349_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 1, v_mctx_2351_);
lean_ctor_set(v___x_2339_, 0, v_a_2344_);
v___x_2353_ = v___x_2339_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2344_);
lean_ctor_set(v_reuseFailAlloc_2356_, 1, v_mctx_2351_);
v___x_2353_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2354_ = lean_array_push(v_snd_2337_, v___x_2353_);
v___x_2355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2341_);
lean_ctor_set(v___x_2355_, 1, v___x_2354_);
v_a_2331_ = v___x_2355_;
goto v___jp_2330_;
}
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
lean_dec(v___x_2349_);
lean_dec(v_a_2344_);
lean_del_object(v___x_2339_);
lean_dec(v_snd_2337_);
lean_dec_ref(v_act_2318_);
v_a_2357_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2350_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2350_);
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
v___jp_2365_:
{
if (v___y_2366_ == 0)
{
lean_del_object(v___x_2346_);
goto v___jp_2348_;
}
else
{
lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2370_; 
lean_dec(v_a_2344_);
lean_del_object(v___x_2339_);
lean_dec_ref(v_act_2318_);
v___x_2367_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0___closed__0));
v___x_2368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2367_);
lean_ctor_set(v___x_2368_, 1, v_snd_2337_);
if (v_isShared_2347_ == 0)
{
lean_ctor_set(v___x_2346_, 0, v___x_2368_);
v___x_2370_ = v___x_2346_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v___x_2368_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
}
else
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2409_; 
v_a_2374_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2376_ = v___x_2343_;
v_isShared_2377_ = v_isSharedCheck_2409_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_2343_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2409_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
uint8_t v___y_2379_; uint8_t v___x_2407_; 
v___x_2407_ = l_Lean_Exception_isInterrupt(v_a_2374_);
if (v___x_2407_ == 0)
{
uint8_t v___x_2408_; 
lean_inc(v_a_2374_);
v___x_2408_ = l_Lean_Exception_isRuntime(v_a_2374_);
v___y_2379_ = v___x_2408_;
goto v___jp_2378_;
}
else
{
v___y_2379_ = v___x_2407_;
goto v___jp_2378_;
}
v___jp_2378_:
{
if (v___y_2379_ == 0)
{
lean_object* v___x_2380_; 
lean_del_object(v___x_2376_);
v___x_2380_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2319_, v___y_2326_, v___y_2328_);
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2394_; 
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2394_ == 0)
{
lean_object* v_unused_2395_; 
v_unused_2395_ = lean_ctor_get(v___x_2380_, 0);
lean_dec(v_unused_2395_);
v___x_2382_ = v___x_2380_;
v_isShared_2383_ = v_isSharedCheck_2394_;
goto v_resetjp_2381_;
}
else
{
lean_dec(v___x_2380_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2394_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
uint8_t v___x_2384_; 
v___x_2384_ = l_Lean_Meta_LibrarySearch_isAbortSpeculation(v_a_2374_);
lean_dec(v_a_2374_);
if (v___x_2384_ == 0)
{
lean_object* v___x_2386_; 
lean_del_object(v___x_2382_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v___x_2341_);
v___x_2386_ = v___x_2339_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v___x_2341_);
lean_ctor_set(v_reuseFailAlloc_2387_, 1, v_snd_2337_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
v_a_2331_ = v___x_2386_;
goto v___jp_2330_;
}
}
else
{
lean_object* v___x_2389_; 
lean_dec_ref(v_act_2318_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v___x_2341_);
v___x_2389_ = v___x_2339_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v___x_2341_);
lean_ctor_set(v_reuseFailAlloc_2393_, 1, v_snd_2337_);
v___x_2389_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
lean_object* v___x_2391_; 
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 0, v___x_2389_);
v___x_2391_ = v___x_2382_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v___x_2389_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
}
else
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2403_; 
lean_dec(v_a_2374_);
lean_del_object(v___x_2339_);
lean_dec(v_snd_2337_);
lean_dec_ref(v_act_2318_);
v_a_2396_ = lean_ctor_get(v___x_2380_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2398_ = v___x_2380_;
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2380_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2401_; 
if (v_isShared_2399_ == 0)
{
v___x_2401_ = v___x_2398_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2396_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
else
{
lean_object* v___x_2405_; 
lean_del_object(v___x_2339_);
lean_dec(v_snd_2337_);
lean_dec_ref(v_act_2318_);
if (v_isShared_2377_ == 0)
{
v___x_2405_ = v___x_2376_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2374_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
}
}
}
}
v___jp_2330_:
{
size_t v___x_2332_; size_t v___x_2333_; 
v___x_2332_ = ((size_t)1ULL);
v___x_2333_ = lean_usize_add(v_i_2323_, v___x_2332_);
v_i_2323_ = v___x_2333_;
v_b_2324_ = v_a_2331_;
goto _start;
}
}
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
lean_dec_ref(v_a_2413_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryOnEach(lean_object* v_act_2433_, lean_object* v_candidates_2434_, uint8_t v_collectAll_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_){
_start:
{
lean_object* v___x_2441_; 
v___x_2441_ = l_Lean_Meta_saveState___redArg(v_a_2437_, v_a_2439_);
if (lean_obj_tag(v___x_2441_) == 0)
{
lean_object* v_a_2442_; lean_object* v___x_2443_; size_t v_sz_2444_; size_t v___x_2445_; lean_object* v___x_2446_; 
v_a_2442_ = lean_ctor_get(v___x_2441_, 0);
lean_inc(v_a_2442_);
lean_dec_ref(v___x_2441_);
v___x_2443_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryOnEach___closed__1));
v_sz_2444_ = lean_array_size(v_candidates_2434_);
v___x_2445_ = ((size_t)0ULL);
v___x_2446_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(v_act_2433_, v_a_2442_, v_collectAll_2435_, v_candidates_2434_, v_sz_2444_, v___x_2445_, v___x_2443_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_);
lean_dec(v_a_2442_);
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
lean_dec_ref(v_fst_2451_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryOnEach___boxed(lean_object* v_act_2478_, lean_object* v_candidates_2479_, lean_object* v_collectAll_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_){
_start:
{
uint8_t v_collectAll_boxed_2486_; lean_object* v_res_2487_; 
v_collectAll_boxed_2486_ = lean_unbox(v_collectAll_2480_);
v_res_2487_ = l_Lean_Meta_LibrarySearch_tryOnEach(v_act_2478_, v_candidates_2479_, v_collectAll_boxed_2486_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_);
lean_dec(v_a_2484_);
lean_dec_ref(v_a_2483_);
lean_dec(v_a_2482_);
lean_dec_ref(v_a_2481_);
lean_dec_ref(v_candidates_2479_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg(){
_start:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2489_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0, &l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0_once, _init_l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0);
v___x_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2489_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg___boxed(lean_object* v___y_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg();
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0(lean_object* v_00_u03b1_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
lean_object* v___x_2499_; 
v___x_2499_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg();
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___boxed(lean_object* v_00_u03b1_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0(v_00_u03b1_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(lean_object* v_category_2507_, lean_object* v_opts_2508_, lean_object* v_act_2509_, lean_object* v_decl_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; 
lean_inc(v___y_2514_);
lean_inc_ref(v___y_2513_);
lean_inc(v___y_2512_);
lean_inc_ref(v___y_2511_);
v___x_2516_ = lean_apply_4(v_act_2509_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_);
v___x_2517_ = l_Lean_profileitIOUnsafe___redArg(v_category_2507_, v_opts_2508_, v___x_2516_, v_decl_2510_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg___boxed(lean_object* v_category_2518_, lean_object* v_opts_2519_, lean_object* v_act_2520_, lean_object* v_decl_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v_category_2518_, v_opts_2519_, v_act_2520_, v_decl_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec_ref(v_opts_2519_);
lean_dec_ref(v_category_2518_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3(lean_object* v_00_u03b1_2528_, lean_object* v_category_2529_, lean_object* v_opts_2530_, lean_object* v_act_2531_, lean_object* v_decl_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
lean_object* v___x_2538_; 
v___x_2538_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v_category_2529_, v_opts_2530_, v_act_2531_, v_decl_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
return v___x_2538_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___boxed(lean_object* v_00_u03b1_2539_, lean_object* v_category_2540_, lean_object* v_opts_2541_, lean_object* v_act_2542_, lean_object* v_decl_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3(v_00_u03b1_2539_, v_category_2540_, v_opts_2541_, v_act_2542_, v_decl_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
lean_dec_ref(v_opts_2541_);
lean_dec_ref(v_category_2540_);
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0(lean_object* v_a_2550_, lean_object* v___x_2551_, lean_object* v_tactic_2552_, lean_object* v_allowFailure_2553_, lean_object* v_cand_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v___x_2560_; 
lean_inc(v___y_2558_);
lean_inc_ref(v___y_2557_);
lean_inc(v___y_2556_);
lean_inc_ref(v___y_2555_);
v___x_2560_ = lean_apply_5(v_a_2550_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, lean_box(0));
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_object* v_a_2561_; uint8_t v___x_2562_; 
v_a_2561_ = lean_ctor_get(v___x_2560_, 0);
lean_inc(v_a_2561_);
lean_dec_ref(v___x_2560_);
v___x_2562_ = lean_unbox(v_a_2561_);
lean_dec(v_a_2561_);
if (v___x_2562_ == 0)
{
lean_object* v___x_2563_; 
v___x_2563_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(v___x_2551_, v_tactic_2552_, v_allowFailure_2553_, v_cand_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
return v___x_2563_;
}
else
{
lean_object* v___x_2564_; lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
lean_dec_ref(v_cand_2554_);
lean_dec_ref(v_allowFailure_2553_);
lean_dec_ref(v_tactic_2552_);
lean_dec_ref(v___x_2551_);
v___x_2564_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg();
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2567_ = v___x_2564_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2564_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2565_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
else
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2580_; 
lean_dec_ref(v_cand_2554_);
lean_dec_ref(v_allowFailure_2553_);
lean_dec_ref(v_tactic_2552_);
lean_dec_ref(v___x_2551_);
v_a_2573_ = lean_ctor_get(v___x_2560_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2575_ = v___x_2560_;
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2560_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2578_; 
if (v_isShared_2576_ == 0)
{
v___x_2578_ = v___x_2575_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_a_2573_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed(lean_object* v_a_2581_, lean_object* v___x_2582_, lean_object* v_tactic_2583_, lean_object* v_allowFailure_2584_, lean_object* v_cand_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0(v_a_2581_, v___x_2582_, v_tactic_2583_, v_allowFailure_2584_, v_cand_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
return v_res_2591_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(lean_object* v_as_2592_, size_t v_i_2593_, size_t v_stop_2594_){
_start:
{
uint8_t v___x_2595_; 
v___x_2595_ = lean_usize_dec_eq(v_i_2593_, v_stop_2594_);
if (v___x_2595_ == 0)
{
lean_object* v___x_2596_; lean_object* v_fst_2597_; uint8_t v___x_2598_; 
v___x_2596_ = lean_array_uget_borrowed(v_as_2592_, v_i_2593_);
v_fst_2597_ = lean_ctor_get(v___x_2596_, 0);
v___x_2598_ = l_List_isEmpty___redArg(v_fst_2597_);
if (v___x_2598_ == 0)
{
size_t v___x_2599_; size_t v___x_2600_; 
v___x_2599_ = ((size_t)1ULL);
v___x_2600_ = lean_usize_add(v_i_2593_, v___x_2599_);
v_i_2593_ = v___x_2600_;
goto _start;
}
else
{
return v___x_2598_;
}
}
else
{
uint8_t v___x_2602_; 
v___x_2602_ = 0;
return v___x_2602_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2___boxed(lean_object* v_as_2603_, lean_object* v_i_2604_, lean_object* v_stop_2605_){
_start:
{
size_t v_i_boxed_2606_; size_t v_stop_boxed_2607_; uint8_t v_res_2608_; lean_object* v_r_2609_; 
v_i_boxed_2606_ = lean_unbox_usize(v_i_2604_);
lean_dec(v_i_2604_);
v_stop_boxed_2607_ = lean_unbox_usize(v_stop_2605_);
lean_dec(v_stop_2605_);
v_res_2608_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_as_2603_, v_i_boxed_2606_, v_stop_boxed_2607_);
lean_dec_ref(v_as_2603_);
v_r_2609_ = lean_box(v_res_2608_);
return v_r_2609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(lean_object* v_goal_2610_, lean_object* v___x_2611_, size_t v_sz_2612_, size_t v_i_2613_, lean_object* v_bs_2614_){
_start:
{
uint8_t v___x_2615_; 
v___x_2615_ = lean_usize_dec_lt(v_i_2613_, v_sz_2612_);
if (v___x_2615_ == 0)
{
lean_dec_ref(v___x_2611_);
lean_dec(v_goal_2610_);
return v_bs_2614_;
}
else
{
lean_object* v_v_2616_; lean_object* v___x_2617_; lean_object* v_bs_x27_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; size_t v___x_2621_; size_t v___x_2622_; lean_object* v___x_2623_; 
v_v_2616_ = lean_array_uget(v_bs_2614_, v_i_2613_);
v___x_2617_ = lean_unsigned_to_nat(0u);
v_bs_x27_2618_ = lean_array_uset(v_bs_2614_, v_i_2613_, v___x_2617_);
lean_inc_ref(v___x_2611_);
lean_inc(v_goal_2610_);
v___x_2619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2619_, 0, v_goal_2610_);
lean_ctor_set(v___x_2619_, 1, v___x_2611_);
v___x_2620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2619_);
lean_ctor_set(v___x_2620_, 1, v_v_2616_);
v___x_2621_ = ((size_t)1ULL);
v___x_2622_ = lean_usize_add(v_i_2613_, v___x_2621_);
v___x_2623_ = lean_array_uset(v_bs_x27_2618_, v_i_2613_, v___x_2620_);
v_i_2613_ = v___x_2622_;
v_bs_2614_ = v___x_2623_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1___boxed(lean_object* v_goal_2625_, lean_object* v___x_2626_, lean_object* v_sz_2627_, lean_object* v_i_2628_, lean_object* v_bs_2629_){
_start:
{
size_t v_sz_boxed_2630_; size_t v_i_boxed_2631_; lean_object* v_res_2632_; 
v_sz_boxed_2630_ = lean_unbox_usize(v_sz_2627_);
lean_dec(v_sz_2627_);
v_i_boxed_2631_ = lean_unbox_usize(v_i_2628_);
lean_dec(v_i_2628_);
v_res_2632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2625_, v___x_2626_, v_sz_boxed_2630_, v_i_boxed_2631_, v_bs_2629_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1(lean_object* v_leavePercentHeartbeats_2634_, lean_object* v_goal_2635_, lean_object* v___x_2636_, lean_object* v_tactic_2637_, lean_object* v_allowFailure_2638_, uint8_t v_collectAll_2639_, uint8_t v_includeStar_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v___x_2649_; 
v___x_2649_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercentHeartbeats_2634_, v___y_2643_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_a_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_a_2650_);
lean_dec_ref(v___x_2649_);
v___x_2651_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___closed__0));
lean_inc(v_goal_2635_);
v___x_2652_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v___x_2651_, v_goal_2635_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; lean_object* v___f_2654_; lean_object* v___x_2655_; 
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2653_);
lean_dec_ref(v___x_2652_);
v___f_2654_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2654_, 0, v_a_2650_);
lean_closure_set(v___f_2654_, 1, v___x_2636_);
lean_closure_set(v___f_2654_, 2, v_tactic_2637_);
lean_closure_set(v___f_2654_, 3, v_allowFailure_2638_);
lean_inc_ref(v___f_2654_);
v___x_2655_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2654_, v_a_2653_, v_collectAll_2639_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
lean_dec(v_a_2653_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v_a_2656_; 
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_a_2656_);
if (lean_obj_tag(v_a_2656_) == 0)
{
lean_dec_ref(v___x_2655_);
lean_dec_ref(v___f_2654_);
lean_dec(v_goal_2635_);
goto v___jp_2646_;
}
else
{
lean_object* v_val_2657_; lean_object* v___x_2706_; lean_object* v___x_2707_; uint8_t v___x_2708_; 
v_val_2657_ = lean_ctor_get(v_a_2656_, 0);
v___x_2706_ = lean_unsigned_to_nat(0u);
v___x_2707_ = lean_array_get_size(v_val_2657_);
v___x_2708_ = lean_nat_dec_lt(v___x_2706_, v___x_2707_);
if (v___x_2708_ == 0)
{
goto v___jp_2702_;
}
else
{
if (v___x_2708_ == 0)
{
goto v___jp_2702_;
}
else
{
size_t v___x_2709_; size_t v___x_2710_; uint8_t v___x_2711_; 
v___x_2709_ = ((size_t)0ULL);
v___x_2710_ = lean_usize_of_nat(v___x_2707_);
v___x_2711_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_val_2657_, v___x_2709_, v___x_2710_);
if (v___x_2711_ == 0)
{
goto v___jp_2702_;
}
else
{
lean_dec_ref(v_a_2656_);
lean_dec_ref(v___f_2654_);
lean_dec(v_goal_2635_);
return v___x_2655_;
}
}
}
v___jp_2658_:
{
if (v_includeStar_2640_ == 0)
{
lean_dec_ref(v_a_2656_);
lean_dec_ref(v___f_2654_);
lean_dec(v_goal_2635_);
return v___x_2655_;
}
else
{
lean_object* v___x_2659_; 
lean_dec_ref(v___x_2655_);
v___x_2659_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2693_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2662_ = v___x_2659_;
v_isShared_2663_ = v_isSharedCheck_2693_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2659_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2693_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; uint8_t v___x_2666_; 
v___x_2664_ = lean_array_get_size(v_a_2660_);
v___x_2665_ = lean_unsigned_to_nat(0u);
v___x_2666_ = lean_nat_dec_eq(v___x_2664_, v___x_2665_);
if (v___x_2666_ == 0)
{
lean_object* v___x_2667_; lean_object* v_mctx_2668_; size_t v_sz_2669_; size_t v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
lean_inc(v_val_2657_);
lean_del_object(v___x_2662_);
lean_dec_ref(v_a_2656_);
v___x_2667_ = lean_st_ref_get(v___y_2642_);
v_mctx_2668_ = lean_ctor_get(v___x_2667_, 0);
lean_inc_ref(v_mctx_2668_);
lean_dec(v___x_2667_);
v_sz_2669_ = lean_array_size(v_a_2660_);
v___x_2670_ = ((size_t)0ULL);
v___x_2671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2635_, v_mctx_2668_, v_sz_2669_, v___x_2670_, v_a_2660_);
v___x_2672_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2654_, v___x_2671_, v_collectAll_2639_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
lean_dec_ref(v___x_2671_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2689_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2675_ = v___x_2672_;
v_isShared_2676_ = v_isSharedCheck_2689_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2672_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2689_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
if (lean_obj_tag(v_a_2673_) == 0)
{
lean_del_object(v___x_2675_);
lean_dec(v_val_2657_);
goto v___jp_2646_;
}
else
{
lean_object* v_val_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2688_; 
v_val_2677_ = lean_ctor_get(v_a_2673_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v_a_2673_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2679_ = v_a_2673_;
v_isShared_2680_ = v_isSharedCheck_2688_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_val_2677_);
lean_dec(v_a_2673_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2688_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2681_; lean_object* v___x_2683_; 
v___x_2681_ = l_Array_append___redArg(v_val_2657_, v_val_2677_);
lean_dec(v_val_2677_);
if (v_isShared_2680_ == 0)
{
lean_ctor_set(v___x_2679_, 0, v___x_2681_);
v___x_2683_ = v___x_2679_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v___x_2681_);
v___x_2683_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
lean_object* v___x_2685_; 
if (v_isShared_2676_ == 0)
{
lean_ctor_set(v___x_2675_, 0, v___x_2683_);
v___x_2685_ = v___x_2675_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2683_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
}
}
}
else
{
lean_dec(v_val_2657_);
return v___x_2672_;
}
}
else
{
lean_object* v___x_2691_; 
lean_dec(v_a_2660_);
lean_dec_ref(v___f_2654_);
lean_dec(v_goal_2635_);
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 0, v_a_2656_);
v___x_2691_ = v___x_2662_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2656_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
}
else
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2701_; 
lean_dec_ref(v_a_2656_);
lean_dec_ref(v___f_2654_);
lean_dec(v_goal_2635_);
v_a_2694_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2696_ = v___x_2659_;
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2659_);
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
v___jp_2702_:
{
if (v_collectAll_2639_ == 0)
{
lean_object* v___x_2703_; lean_object* v___x_2704_; uint8_t v___x_2705_; 
v___x_2703_ = lean_array_get_size(v_val_2657_);
v___x_2704_ = lean_unsigned_to_nat(0u);
v___x_2705_ = lean_nat_dec_eq(v___x_2703_, v___x_2704_);
if (v___x_2705_ == 0)
{
lean_dec_ref(v_a_2656_);
lean_dec_ref(v___f_2654_);
lean_dec(v_goal_2635_);
return v___x_2655_;
}
else
{
goto v___jp_2658_;
}
}
else
{
goto v___jp_2658_;
}
}
}
}
else
{
lean_dec_ref(v___f_2654_);
lean_dec(v_goal_2635_);
return v___x_2655_;
}
}
else
{
lean_object* v_a_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2719_; 
lean_dec(v_a_2650_);
lean_dec_ref(v_allowFailure_2638_);
lean_dec_ref(v_tactic_2637_);
lean_dec_ref(v___x_2636_);
lean_dec(v_goal_2635_);
v_a_2712_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2714_ = v___x_2652_;
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_a_2712_);
lean_dec(v___x_2652_);
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
lean_dec_ref(v_allowFailure_2638_);
lean_dec_ref(v_tactic_2637_);
lean_dec_ref(v___x_2636_);
lean_dec(v_goal_2635_);
v_a_2720_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2649_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2649_);
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
v___jp_2646_:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2647_ = lean_box(0);
v___x_2648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2647_);
return v___x_2648_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed(lean_object* v_leavePercentHeartbeats_2728_, lean_object* v_goal_2729_, lean_object* v___x_2730_, lean_object* v_tactic_2731_, lean_object* v_allowFailure_2732_, lean_object* v_collectAll_2733_, lean_object* v_includeStar_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_){
_start:
{
uint8_t v_collectAll_boxed_2740_; uint8_t v_includeStar_boxed_2741_; lean_object* v_res_2742_; 
v_collectAll_boxed_2740_ = lean_unbox(v_collectAll_2733_);
v_includeStar_boxed_2741_ = lean_unbox(v_includeStar_2734_);
v_res_2742_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1(v_leavePercentHeartbeats_2728_, v_goal_2729_, v___x_2730_, v_tactic_2731_, v_allowFailure_2732_, v_collectAll_boxed_2740_, v_includeStar_boxed_2741_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v_leavePercentHeartbeats_2728_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2(lean_object* v_goal_2743_, lean_object* v_x_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v___x_2750_; 
v___x_2750_ = l_Lean_MVarId_getType(v_goal_2743_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2759_; 
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2753_ = v___x_2750_;
v_isShared_2754_ = v_isSharedCheck_2759_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2750_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2759_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2755_; lean_object* v___x_2757_; 
v___x_2755_ = l_Lean_MessageData_ofExpr(v_a_2751_);
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 0, v___x_2755_);
v___x_2757_ = v___x_2753_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2755_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
else
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
v_a_2760_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v___x_2750_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2750_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2760_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2___boxed(lean_object* v_goal_2768_, lean_object* v_x_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2(v_goal_2768_, v_x_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec_ref(v_x_2769_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4(lean_object* v_leavePercentHeartbeats_2776_, lean_object* v_goal_2777_, lean_object* v___x_2778_, lean_object* v_tactic_2779_, lean_object* v_allowFailure_2780_, uint8_t v_collectAll_2781_, uint8_t v_includeStar_2782_, uint8_t v___x_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_){
_start:
{
lean_object* v___x_2792_; 
v___x_2792_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercentHeartbeats_2776_, v___y_2786_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v_a_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
lean_inc(v_a_2793_);
lean_dec_ref(v___x_2792_);
v___x_2794_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___closed__0));
lean_inc(v_goal_2777_);
v___x_2795_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v___x_2794_, v_goal_2777_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_);
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_object* v_a_2796_; lean_object* v___f_2797_; lean_object* v___x_2798_; 
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
lean_inc(v_a_2796_);
lean_dec_ref(v___x_2795_);
v___f_2797_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2797_, 0, v_a_2793_);
lean_closure_set(v___f_2797_, 1, v___x_2778_);
lean_closure_set(v___f_2797_, 2, v_tactic_2779_);
lean_closure_set(v___f_2797_, 3, v_allowFailure_2780_);
lean_inc_ref(v___f_2797_);
v___x_2798_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2797_, v_a_2796_, v_collectAll_2781_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_);
lean_dec(v_a_2796_);
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_object* v_a_2799_; 
v_a_2799_ = lean_ctor_get(v___x_2798_, 0);
lean_inc(v_a_2799_);
if (lean_obj_tag(v_a_2799_) == 0)
{
lean_dec_ref(v___x_2798_);
lean_dec_ref(v___f_2797_);
lean_dec(v_goal_2777_);
goto v___jp_2789_;
}
else
{
lean_object* v_val_2800_; uint8_t v___y_2846_; lean_object* v___x_2850_; lean_object* v___x_2851_; uint8_t v___x_2852_; 
v_val_2800_ = lean_ctor_get(v_a_2799_, 0);
v___x_2850_ = lean_unsigned_to_nat(0u);
v___x_2851_ = lean_array_get_size(v_val_2800_);
v___x_2852_ = lean_nat_dec_lt(v___x_2850_, v___x_2851_);
if (v___x_2852_ == 0)
{
v___y_2846_ = v___x_2783_;
goto v___jp_2845_;
}
else
{
if (v___x_2852_ == 0)
{
v___y_2846_ = v___x_2783_;
goto v___jp_2845_;
}
else
{
size_t v___x_2853_; size_t v___x_2854_; uint8_t v___x_2855_; 
v___x_2853_ = ((size_t)0ULL);
v___x_2854_ = lean_usize_of_nat(v___x_2851_);
v___x_2855_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_val_2800_, v___x_2853_, v___x_2854_);
v___y_2846_ = v___x_2855_;
goto v___jp_2845_;
}
}
v___jp_2801_:
{
if (v_includeStar_2782_ == 0)
{
lean_dec_ref(v_a_2799_);
lean_dec_ref(v___f_2797_);
lean_dec(v_goal_2777_);
return v___x_2798_;
}
else
{
lean_object* v___x_2802_; 
lean_dec_ref(v___x_2798_);
v___x_2802_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2836_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2805_ = v___x_2802_;
v_isShared_2806_ = v_isSharedCheck_2836_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v___x_2802_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2836_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; uint8_t v___x_2809_; 
v___x_2807_ = lean_array_get_size(v_a_2803_);
v___x_2808_ = lean_unsigned_to_nat(0u);
v___x_2809_ = lean_nat_dec_eq(v___x_2807_, v___x_2808_);
if (v___x_2809_ == 0)
{
lean_object* v___x_2810_; lean_object* v_mctx_2811_; size_t v_sz_2812_; size_t v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
lean_inc(v_val_2800_);
lean_del_object(v___x_2805_);
lean_dec_ref(v_a_2799_);
v___x_2810_ = lean_st_ref_get(v___y_2785_);
v_mctx_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc_ref(v_mctx_2811_);
lean_dec(v___x_2810_);
v_sz_2812_ = lean_array_size(v_a_2803_);
v___x_2813_ = ((size_t)0ULL);
v___x_2814_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2777_, v_mctx_2811_, v_sz_2812_, v___x_2813_, v_a_2803_);
v___x_2815_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2797_, v___x_2814_, v_collectAll_2781_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_);
lean_dec_ref(v___x_2814_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2832_; 
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2818_ = v___x_2815_;
v_isShared_2819_ = v_isSharedCheck_2832_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2815_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2832_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
if (lean_obj_tag(v_a_2816_) == 0)
{
lean_del_object(v___x_2818_);
lean_dec(v_val_2800_);
goto v___jp_2789_;
}
else
{
lean_object* v_val_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2831_; 
v_val_2820_ = lean_ctor_get(v_a_2816_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v_a_2816_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2822_ = v_a_2816_;
v_isShared_2823_ = v_isSharedCheck_2831_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_val_2820_);
lean_dec(v_a_2816_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2831_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2824_; lean_object* v___x_2826_; 
v___x_2824_ = l_Array_append___redArg(v_val_2800_, v_val_2820_);
lean_dec(v_val_2820_);
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 0, v___x_2824_);
v___x_2826_ = v___x_2822_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v___x_2824_);
v___x_2826_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
lean_object* v___x_2828_; 
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 0, v___x_2826_);
v___x_2828_ = v___x_2818_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v___x_2826_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
}
}
}
else
{
lean_dec(v_val_2800_);
return v___x_2815_;
}
}
else
{
lean_object* v___x_2834_; 
lean_dec(v_a_2803_);
lean_dec_ref(v___f_2797_);
lean_dec(v_goal_2777_);
if (v_isShared_2806_ == 0)
{
lean_ctor_set(v___x_2805_, 0, v_a_2799_);
v___x_2834_ = v___x_2805_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2799_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
}
else
{
lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2844_; 
lean_dec_ref(v_a_2799_);
lean_dec_ref(v___f_2797_);
lean_dec(v_goal_2777_);
v_a_2837_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2839_ = v___x_2802_;
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2802_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2842_; 
if (v_isShared_2840_ == 0)
{
v___x_2842_ = v___x_2839_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_a_2837_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
}
}
}
v___jp_2845_:
{
if (v___y_2846_ == 0)
{
if (v_collectAll_2781_ == 0)
{
lean_object* v___x_2847_; lean_object* v___x_2848_; uint8_t v___x_2849_; 
v___x_2847_ = lean_array_get_size(v_val_2800_);
v___x_2848_ = lean_unsigned_to_nat(0u);
v___x_2849_ = lean_nat_dec_eq(v___x_2847_, v___x_2848_);
if (v___x_2849_ == 0)
{
lean_dec_ref(v_a_2799_);
lean_dec_ref(v___f_2797_);
lean_dec(v_goal_2777_);
return v___x_2798_;
}
else
{
goto v___jp_2801_;
}
}
else
{
goto v___jp_2801_;
}
}
else
{
lean_dec_ref(v_a_2799_);
lean_dec_ref(v___f_2797_);
lean_dec(v_goal_2777_);
return v___x_2798_;
}
}
}
}
else
{
lean_dec_ref(v___f_2797_);
lean_dec(v_goal_2777_);
return v___x_2798_;
}
}
else
{
lean_object* v_a_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2863_; 
lean_dec(v_a_2793_);
lean_dec_ref(v_allowFailure_2780_);
lean_dec_ref(v_tactic_2779_);
lean_dec_ref(v___x_2778_);
lean_dec(v_goal_2777_);
v_a_2856_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2858_ = v___x_2795_;
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_a_2856_);
lean_dec(v___x_2795_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2861_; 
if (v_isShared_2859_ == 0)
{
v___x_2861_ = v___x_2858_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_a_2856_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
lean_dec_ref(v_allowFailure_2780_);
lean_dec_ref(v_tactic_2779_);
lean_dec_ref(v___x_2778_);
lean_dec(v_goal_2777_);
v_a_2864_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___x_2792_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2792_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
v___jp_2789_:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2790_ = lean_box(0);
v___x_2791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2790_);
return v___x_2791_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4___boxed(lean_object* v_leavePercentHeartbeats_2872_, lean_object* v_goal_2873_, lean_object* v___x_2874_, lean_object* v_tactic_2875_, lean_object* v_allowFailure_2876_, lean_object* v_collectAll_2877_, lean_object* v_includeStar_2878_, lean_object* v___x_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
uint8_t v_collectAll_boxed_2885_; uint8_t v_includeStar_boxed_2886_; uint8_t v___x_15848__boxed_2887_; lean_object* v_res_2888_; 
v_collectAll_boxed_2885_ = lean_unbox(v_collectAll_2877_);
v_includeStar_boxed_2886_ = lean_unbox(v_includeStar_2878_);
v___x_15848__boxed_2887_ = lean_unbox(v___x_2879_);
v_res_2888_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4(v_leavePercentHeartbeats_2872_, v_goal_2873_, v___x_2874_, v_tactic_2875_, v_allowFailure_2876_, v_collectAll_boxed_2885_, v_includeStar_boxed_2886_, v___x_15848__boxed_2887_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
lean_dec(v_leavePercentHeartbeats_2872_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__5(lean_object* v_leavePercentHeartbeats_2889_, lean_object* v_goal_2890_, lean_object* v___x_2891_, lean_object* v_tactic_2892_, lean_object* v_allowFailure_2893_, uint8_t v_collectAll_2894_, uint8_t v_includeStar_2895_, uint8_t v___x_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
lean_object* v___x_2905_; 
v___x_2905_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercentHeartbeats_2889_, v___y_2899_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_a_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc(v_a_2906_);
lean_dec_ref(v___x_2905_);
v___x_2907_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___closed__0));
lean_inc(v_goal_2890_);
v___x_2908_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v___x_2907_, v_goal_2890_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_object* v_a_2909_; lean_object* v___f_2910_; lean_object* v___x_2911_; 
v_a_2909_ = lean_ctor_get(v___x_2908_, 0);
lean_inc(v_a_2909_);
lean_dec_ref(v___x_2908_);
v___f_2910_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2910_, 0, v_a_2906_);
lean_closure_set(v___f_2910_, 1, v___x_2891_);
lean_closure_set(v___f_2910_, 2, v_tactic_2892_);
lean_closure_set(v___f_2910_, 3, v_allowFailure_2893_);
lean_inc_ref(v___f_2910_);
v___x_2911_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2910_, v_a_2909_, v_collectAll_2894_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
lean_dec(v_a_2909_);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v_a_2912_; 
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
lean_inc(v_a_2912_);
if (lean_obj_tag(v_a_2912_) == 0)
{
lean_dec_ref(v___x_2911_);
lean_dec_ref(v___f_2910_);
lean_dec(v_goal_2890_);
goto v___jp_2902_;
}
else
{
lean_object* v_val_2913_; lean_object* v___x_2963_; lean_object* v___x_2964_; uint8_t v___x_2965_; 
v_val_2913_ = lean_ctor_get(v_a_2912_, 0);
v___x_2963_ = lean_unsigned_to_nat(0u);
v___x_2964_ = lean_array_get_size(v_val_2913_);
v___x_2965_ = lean_nat_dec_lt(v___x_2963_, v___x_2964_);
if (v___x_2965_ == 0)
{
goto v___jp_2959_;
}
else
{
if (v___x_2965_ == 0)
{
goto v___jp_2959_;
}
else
{
size_t v___x_2966_; size_t v___x_2967_; uint8_t v___x_2968_; 
v___x_2966_ = ((size_t)0ULL);
v___x_2967_ = lean_usize_of_nat(v___x_2964_);
v___x_2968_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_val_2913_, v___x_2966_, v___x_2967_);
if (v___x_2968_ == 0)
{
goto v___jp_2959_;
}
else
{
if (v___x_2896_ == 0)
{
goto v___jp_2958_;
}
else
{
lean_dec_ref(v_a_2912_);
lean_dec_ref(v___f_2910_);
lean_dec(v_goal_2890_);
return v___x_2911_;
}
}
}
}
v___jp_2914_:
{
lean_object* v___x_2915_; 
v___x_2915_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2949_; 
v_a_2916_ = lean_ctor_get(v___x_2915_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2918_ = v___x_2915_;
v_isShared_2919_ = v_isSharedCheck_2949_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2915_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2949_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; uint8_t v___x_2922_; 
v___x_2920_ = lean_array_get_size(v_a_2916_);
v___x_2921_ = lean_unsigned_to_nat(0u);
v___x_2922_ = lean_nat_dec_eq(v___x_2920_, v___x_2921_);
if (v___x_2922_ == 0)
{
lean_object* v___x_2923_; lean_object* v_mctx_2924_; size_t v_sz_2925_; size_t v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; 
lean_inc(v_val_2913_);
lean_del_object(v___x_2918_);
lean_dec_ref(v_a_2912_);
v___x_2923_ = lean_st_ref_get(v___y_2898_);
v_mctx_2924_ = lean_ctor_get(v___x_2923_, 0);
lean_inc_ref(v_mctx_2924_);
lean_dec(v___x_2923_);
v_sz_2925_ = lean_array_size(v_a_2916_);
v___x_2926_ = ((size_t)0ULL);
v___x_2927_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2890_, v_mctx_2924_, v_sz_2925_, v___x_2926_, v_a_2916_);
v___x_2928_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2910_, v___x_2927_, v_collectAll_2894_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
lean_dec_ref(v___x_2927_);
if (lean_obj_tag(v___x_2928_) == 0)
{
lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2945_; 
v_a_2929_ = lean_ctor_get(v___x_2928_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2931_ = v___x_2928_;
v_isShared_2932_ = v_isSharedCheck_2945_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2929_);
lean_dec(v___x_2928_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2945_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
if (lean_obj_tag(v_a_2929_) == 0)
{
lean_del_object(v___x_2931_);
lean_dec(v_val_2913_);
goto v___jp_2902_;
}
else
{
lean_object* v_val_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2944_; 
v_val_2933_ = lean_ctor_get(v_a_2929_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v_a_2929_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2935_ = v_a_2929_;
v_isShared_2936_ = v_isSharedCheck_2944_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_val_2933_);
lean_dec(v_a_2929_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2944_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2937_; lean_object* v___x_2939_; 
v___x_2937_ = l_Array_append___redArg(v_val_2913_, v_val_2933_);
lean_dec(v_val_2933_);
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 0, v___x_2937_);
v___x_2939_ = v___x_2935_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2937_);
v___x_2939_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
lean_object* v___x_2941_; 
if (v_isShared_2932_ == 0)
{
lean_ctor_set(v___x_2931_, 0, v___x_2939_);
v___x_2941_ = v___x_2931_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v___x_2939_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
}
}
}
else
{
lean_dec(v_val_2913_);
return v___x_2928_;
}
}
else
{
lean_object* v___x_2947_; 
lean_dec(v_a_2916_);
lean_dec_ref(v___f_2910_);
lean_dec(v_goal_2890_);
if (v_isShared_2919_ == 0)
{
lean_ctor_set(v___x_2918_, 0, v_a_2912_);
v___x_2947_ = v___x_2918_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2912_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
}
else
{
lean_object* v_a_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2957_; 
lean_dec_ref(v_a_2912_);
lean_dec_ref(v___f_2910_);
lean_dec(v_goal_2890_);
v_a_2950_ = lean_ctor_get(v___x_2915_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2952_ = v___x_2915_;
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_a_2950_);
lean_dec(v___x_2915_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2955_; 
if (v_isShared_2953_ == 0)
{
v___x_2955_ = v___x_2952_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_a_2950_);
v___x_2955_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
return v___x_2955_;
}
}
}
}
v___jp_2958_:
{
if (v_includeStar_2895_ == 0)
{
if (v___x_2896_ == 0)
{
lean_dec_ref(v___x_2911_);
goto v___jp_2914_;
}
else
{
lean_dec_ref(v_a_2912_);
lean_dec_ref(v___f_2910_);
lean_dec(v_goal_2890_);
return v___x_2911_;
}
}
else
{
lean_dec_ref(v___x_2911_);
goto v___jp_2914_;
}
}
v___jp_2959_:
{
if (v_collectAll_2894_ == 0)
{
if (v___x_2896_ == 0)
{
goto v___jp_2958_;
}
else
{
lean_object* v___x_2960_; lean_object* v___x_2961_; uint8_t v___x_2962_; 
v___x_2960_ = lean_array_get_size(v_val_2913_);
v___x_2961_ = lean_unsigned_to_nat(0u);
v___x_2962_ = lean_nat_dec_eq(v___x_2960_, v___x_2961_);
if (v___x_2962_ == 0)
{
lean_dec_ref(v_a_2912_);
lean_dec_ref(v___f_2910_);
lean_dec(v_goal_2890_);
return v___x_2911_;
}
else
{
goto v___jp_2958_;
}
}
}
else
{
goto v___jp_2958_;
}
}
}
}
else
{
lean_dec_ref(v___f_2910_);
lean_dec(v_goal_2890_);
return v___x_2911_;
}
}
else
{
lean_object* v_a_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2976_; 
lean_dec(v_a_2906_);
lean_dec_ref(v_allowFailure_2893_);
lean_dec_ref(v_tactic_2892_);
lean_dec_ref(v___x_2891_);
lean_dec(v_goal_2890_);
v_a_2969_ = lean_ctor_get(v___x_2908_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2971_ = v___x_2908_;
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_a_2969_);
lean_dec(v___x_2908_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___x_2974_; 
if (v_isShared_2972_ == 0)
{
v___x_2974_ = v___x_2971_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_a_2969_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
}
}
else
{
lean_object* v_a_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2984_; 
lean_dec_ref(v_allowFailure_2893_);
lean_dec_ref(v_tactic_2892_);
lean_dec_ref(v___x_2891_);
lean_dec(v_goal_2890_);
v_a_2977_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2979_ = v___x_2905_;
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_a_2977_);
lean_dec(v___x_2905_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2982_; 
if (v_isShared_2980_ == 0)
{
v___x_2982_ = v___x_2979_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_a_2977_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
}
v___jp_2902_:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; 
v___x_2903_ = lean_box(0);
v___x_2904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2903_);
return v___x_2904_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__5___boxed(lean_object* v_leavePercentHeartbeats_2985_, lean_object* v_goal_2986_, lean_object* v___x_2987_, lean_object* v_tactic_2988_, lean_object* v_allowFailure_2989_, lean_object* v_collectAll_2990_, lean_object* v_includeStar_2991_, lean_object* v___x_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
uint8_t v_collectAll_boxed_2998_; uint8_t v_includeStar_boxed_2999_; uint8_t v___x_16037__boxed_3000_; lean_object* v_res_3001_; 
v_collectAll_boxed_2998_ = lean_unbox(v_collectAll_2990_);
v_includeStar_boxed_2999_ = lean_unbox(v_includeStar_2991_);
v___x_16037__boxed_3000_ = lean_unbox(v___x_2992_);
v_res_3001_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__5(v_leavePercentHeartbeats_2985_, v_goal_2986_, v___x_2987_, v_tactic_2988_, v_allowFailure_2989_, v_collectAll_boxed_2998_, v_includeStar_boxed_2999_, v___x_16037__boxed_3000_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v_leavePercentHeartbeats_2985_);
return v_res_3001_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(lean_object* v_e_3002_){
_start:
{
if (lean_obj_tag(v_e_3002_) == 0)
{
uint8_t v___x_3003_; 
v___x_3003_ = 2;
return v___x_3003_;
}
else
{
lean_object* v_a_3004_; 
v_a_3004_ = lean_ctor_get(v_e_3002_, 0);
if (lean_obj_tag(v_a_3004_) == 0)
{
uint8_t v___x_3005_; 
v___x_3005_ = 1;
return v___x_3005_;
}
else
{
uint8_t v___x_3006_; 
v___x_3006_ = 0;
return v___x_3006_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4___boxed(lean_object* v_e_3007_){
_start:
{
uint8_t v_res_3008_; lean_object* v_r_3009_; 
v_res_3008_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(v_e_3007_);
lean_dec_ref(v_e_3007_);
v_r_3009_ = lean_box(v_res_3008_);
return v_r_3009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(lean_object* v_cls_3010_, uint8_t v_collapsed_3011_, lean_object* v_tag_3012_, lean_object* v_opts_3013_, uint8_t v_clsEnabled_3014_, lean_object* v_oldTraces_3015_, lean_object* v_msg_3016_, lean_object* v_resStartStop_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_){
_start:
{
lean_object* v_fst_3023_; lean_object* v_snd_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3122_; 
v_fst_3023_ = lean_ctor_get(v_resStartStop_3017_, 0);
v_snd_3024_ = lean_ctor_get(v_resStartStop_3017_, 1);
v_isSharedCheck_3122_ = !lean_is_exclusive(v_resStartStop_3017_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3026_ = v_resStartStop_3017_;
v_isShared_3027_ = v_isSharedCheck_3122_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_snd_3024_);
lean_inc(v_fst_3023_);
lean_dec(v_resStartStop_3017_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3122_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v_data_3031_; lean_object* v_fst_3042_; lean_object* v_snd_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3121_; 
v_fst_3042_ = lean_ctor_get(v_snd_3024_, 0);
v_snd_3043_ = lean_ctor_get(v_snd_3024_, 1);
v_isSharedCheck_3121_ = !lean_is_exclusive(v_snd_3024_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3045_ = v_snd_3024_;
v_isShared_3046_ = v_isSharedCheck_3121_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_snd_3043_);
lean_inc(v_fst_3042_);
lean_dec(v_snd_3024_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3121_;
goto v_resetjp_3044_;
}
v___jp_3028_:
{
lean_object* v___x_3032_; 
lean_inc(v___y_3030_);
v___x_3032_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3(v_oldTraces_3015_, v_data_3031_, v___y_3030_, v___y_3029_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v___x_3033_; 
lean_dec_ref(v___x_3032_);
v___x_3033_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4___redArg(v_fst_3023_);
return v___x_3033_;
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
lean_dec(v_fst_3023_);
v_a_3034_ = lean_ctor_get(v___x_3032_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3036_ = v___x_3032_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_3032_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3034_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
}
v_resetjp_3044_:
{
lean_object* v___x_3047_; uint8_t v___x_3048_; lean_object* v___y_3050_; lean_object* v_a_3051_; uint8_t v___y_3075_; double v___y_3106_; 
v___x_3047_ = l_Lean_trace_profiler;
v___x_3048_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_3013_, v___x_3047_);
if (v___x_3048_ == 0)
{
v___y_3075_ = v___x_3048_;
goto v___jp_3074_;
}
else
{
lean_object* v___x_3111_; uint8_t v___x_3112_; 
v___x_3111_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3112_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_3013_, v___x_3111_);
if (v___x_3112_ == 0)
{
lean_object* v___x_3113_; lean_object* v___x_3114_; double v___x_3115_; double v___x_3116_; double v___x_3117_; 
v___x_3113_ = l_Lean_trace_profiler_threshold;
v___x_3114_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_3013_, v___x_3113_);
v___x_3115_ = lean_float_of_nat(v___x_3114_);
v___x_3116_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3);
v___x_3117_ = lean_float_div(v___x_3115_, v___x_3116_);
v___y_3106_ = v___x_3117_;
goto v___jp_3105_;
}
else
{
lean_object* v___x_3118_; lean_object* v___x_3119_; double v___x_3120_; 
v___x_3118_ = l_Lean_trace_profiler_threshold;
v___x_3119_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_3013_, v___x_3118_);
v___x_3120_ = lean_float_of_nat(v___x_3119_);
v___y_3106_ = v___x_3120_;
goto v___jp_3105_;
}
}
v___jp_3049_:
{
uint8_t v_result_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3057_; 
v_result_3052_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(v_fst_3023_);
v___x_3053_ = l_Lean_TraceResult_toEmoji(v_result_3052_);
v___x_3054_ = l_Lean_stringToMessageData(v___x_3053_);
v___x_3055_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3);
if (v_isShared_3046_ == 0)
{
lean_ctor_set_tag(v___x_3045_, 7);
lean_ctor_set(v___x_3045_, 1, v___x_3055_);
lean_ctor_set(v___x_3045_, 0, v___x_3054_);
v___x_3057_ = v___x_3045_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v___x_3054_);
lean_ctor_set(v_reuseFailAlloc_3068_, 1, v___x_3055_);
v___x_3057_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
lean_object* v_m_3059_; 
if (v_isShared_3027_ == 0)
{
lean_ctor_set_tag(v___x_3026_, 7);
lean_ctor_set(v___x_3026_, 1, v_a_3051_);
lean_ctor_set(v___x_3026_, 0, v___x_3057_);
v_m_3059_ = v___x_3026_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v___x_3057_);
lean_ctor_set(v_reuseFailAlloc_3067_, 1, v_a_3051_);
v_m_3059_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; double v___x_3062_; lean_object* v_data_3063_; 
v___x_3060_ = lean_box(v_result_3052_);
v___x_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3060_);
v___x_3062_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0);
lean_inc_ref(v_tag_3012_);
lean_inc_ref(v___x_3061_);
lean_inc(v_cls_3010_);
v_data_3063_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3063_, 0, v_cls_3010_);
lean_ctor_set(v_data_3063_, 1, v___x_3061_);
lean_ctor_set(v_data_3063_, 2, v_tag_3012_);
lean_ctor_set_float(v_data_3063_, sizeof(void*)*3, v___x_3062_);
lean_ctor_set_float(v_data_3063_, sizeof(void*)*3 + 8, v___x_3062_);
lean_ctor_set_uint8(v_data_3063_, sizeof(void*)*3 + 16, v_collapsed_3011_);
if (v___x_3048_ == 0)
{
lean_dec_ref(v___x_3061_);
lean_dec(v_snd_3043_);
lean_dec(v_fst_3042_);
lean_dec_ref(v_tag_3012_);
lean_dec(v_cls_3010_);
v___y_3029_ = v_m_3059_;
v___y_3030_ = v___y_3050_;
v_data_3031_ = v_data_3063_;
goto v___jp_3028_;
}
else
{
lean_object* v_data_3064_; double v___x_3065_; double v___x_3066_; 
lean_dec_ref(v_data_3063_);
v_data_3064_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3064_, 0, v_cls_3010_);
lean_ctor_set(v_data_3064_, 1, v___x_3061_);
lean_ctor_set(v_data_3064_, 2, v_tag_3012_);
v___x_3065_ = lean_unbox_float(v_fst_3042_);
lean_dec(v_fst_3042_);
lean_ctor_set_float(v_data_3064_, sizeof(void*)*3, v___x_3065_);
v___x_3066_ = lean_unbox_float(v_snd_3043_);
lean_dec(v_snd_3043_);
lean_ctor_set_float(v_data_3064_, sizeof(void*)*3 + 8, v___x_3066_);
lean_ctor_set_uint8(v_data_3064_, sizeof(void*)*3 + 16, v_collapsed_3011_);
v___y_3029_ = v_m_3059_;
v___y_3030_ = v___y_3050_;
v_data_3031_ = v_data_3064_;
goto v___jp_3028_;
}
}
}
}
v___jp_3069_:
{
lean_object* v_ref_3070_; lean_object* v___x_3071_; 
v_ref_3070_ = lean_ctor_get(v___y_3020_, 5);
lean_inc(v___y_3021_);
lean_inc_ref(v___y_3020_);
lean_inc(v___y_3019_);
lean_inc_ref(v___y_3018_);
lean_inc(v_fst_3023_);
v___x_3071_ = lean_apply_6(v_msg_3016_, v_fst_3023_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, lean_box(0));
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_object* v_a_3072_; 
v_a_3072_ = lean_ctor_get(v___x_3071_, 0);
lean_inc(v_a_3072_);
lean_dec_ref(v___x_3071_);
v___y_3050_ = v_ref_3070_;
v_a_3051_ = v_a_3072_;
goto v___jp_3049_;
}
else
{
lean_object* v___x_3073_; 
lean_dec_ref(v___x_3071_);
v___x_3073_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2);
v___y_3050_ = v_ref_3070_;
v_a_3051_ = v___x_3073_;
goto v___jp_3049_;
}
}
v___jp_3074_:
{
if (v_clsEnabled_3014_ == 0)
{
if (v___y_3075_ == 0)
{
lean_object* v___x_3076_; lean_object* v_traceState_3077_; lean_object* v_env_3078_; lean_object* v_nextMacroScope_3079_; lean_object* v_ngen_3080_; lean_object* v_auxDeclNGen_3081_; lean_object* v_cache_3082_; lean_object* v_messages_3083_; lean_object* v_infoState_3084_; lean_object* v_snapshotTasks_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3104_; 
lean_del_object(v___x_3045_);
lean_dec(v_snd_3043_);
lean_dec(v_fst_3042_);
lean_del_object(v___x_3026_);
lean_dec_ref(v_msg_3016_);
lean_dec_ref(v_tag_3012_);
lean_dec(v_cls_3010_);
v___x_3076_ = lean_st_ref_take(v___y_3021_);
v_traceState_3077_ = lean_ctor_get(v___x_3076_, 4);
v_env_3078_ = lean_ctor_get(v___x_3076_, 0);
v_nextMacroScope_3079_ = lean_ctor_get(v___x_3076_, 1);
v_ngen_3080_ = lean_ctor_get(v___x_3076_, 2);
v_auxDeclNGen_3081_ = lean_ctor_get(v___x_3076_, 3);
v_cache_3082_ = lean_ctor_get(v___x_3076_, 5);
v_messages_3083_ = lean_ctor_get(v___x_3076_, 6);
v_infoState_3084_ = lean_ctor_get(v___x_3076_, 7);
v_snapshotTasks_3085_ = lean_ctor_get(v___x_3076_, 8);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3076_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3087_ = v___x_3076_;
v_isShared_3088_ = v_isSharedCheck_3104_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_snapshotTasks_3085_);
lean_inc(v_infoState_3084_);
lean_inc(v_messages_3083_);
lean_inc(v_cache_3082_);
lean_inc(v_traceState_3077_);
lean_inc(v_auxDeclNGen_3081_);
lean_inc(v_ngen_3080_);
lean_inc(v_nextMacroScope_3079_);
lean_inc(v_env_3078_);
lean_dec(v___x_3076_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3104_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
uint64_t v_tid_3089_; lean_object* v_traces_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3103_; 
v_tid_3089_ = lean_ctor_get_uint64(v_traceState_3077_, sizeof(void*)*1);
v_traces_3090_ = lean_ctor_get(v_traceState_3077_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v_traceState_3077_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3092_ = v_traceState_3077_;
v_isShared_3093_ = v_isSharedCheck_3103_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_traces_3090_);
lean_dec(v_traceState_3077_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3103_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3094_; lean_object* v___x_3096_; 
v___x_3094_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3015_, v_traces_3090_);
lean_dec_ref(v_traces_3090_);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 0, v___x_3094_);
v___x_3096_ = v___x_3092_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v___x_3094_);
lean_ctor_set_uint64(v_reuseFailAlloc_3102_, sizeof(void*)*1, v_tid_3089_);
v___x_3096_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
lean_object* v___x_3098_; 
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 4, v___x_3096_);
v___x_3098_ = v___x_3087_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_env_3078_);
lean_ctor_set(v_reuseFailAlloc_3101_, 1, v_nextMacroScope_3079_);
lean_ctor_set(v_reuseFailAlloc_3101_, 2, v_ngen_3080_);
lean_ctor_set(v_reuseFailAlloc_3101_, 3, v_auxDeclNGen_3081_);
lean_ctor_set(v_reuseFailAlloc_3101_, 4, v___x_3096_);
lean_ctor_set(v_reuseFailAlloc_3101_, 5, v_cache_3082_);
lean_ctor_set(v_reuseFailAlloc_3101_, 6, v_messages_3083_);
lean_ctor_set(v_reuseFailAlloc_3101_, 7, v_infoState_3084_);
lean_ctor_set(v_reuseFailAlloc_3101_, 8, v_snapshotTasks_3085_);
v___x_3098_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3099_ = lean_st_ref_set(v___y_3021_, v___x_3098_);
v___x_3100_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4___redArg(v_fst_3023_);
return v___x_3100_;
}
}
}
}
}
else
{
goto v___jp_3069_;
}
}
else
{
goto v___jp_3069_;
}
}
v___jp_3105_:
{
double v___x_3107_; double v___x_3108_; double v___x_3109_; uint8_t v___x_3110_; 
v___x_3107_ = lean_unbox_float(v_snd_3043_);
v___x_3108_ = lean_unbox_float(v_fst_3042_);
v___x_3109_ = lean_float_sub(v___x_3107_, v___x_3108_);
v___x_3110_ = lean_float_decLt(v___y_3106_, v___x_3109_);
v___y_3075_ = v___x_3110_;
goto v___jp_3074_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4___boxed(lean_object* v_cls_3123_, lean_object* v_collapsed_3124_, lean_object* v_tag_3125_, lean_object* v_opts_3126_, lean_object* v_clsEnabled_3127_, lean_object* v_oldTraces_3128_, lean_object* v_msg_3129_, lean_object* v_resStartStop_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
uint8_t v_collapsed_boxed_3136_; uint8_t v_clsEnabled_boxed_3137_; lean_object* v_res_3138_; 
v_collapsed_boxed_3136_ = lean_unbox(v_collapsed_3124_);
v_clsEnabled_boxed_3137_ = lean_unbox(v_clsEnabled_3127_);
v_res_3138_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v_cls_3123_, v_collapsed_boxed_3136_, v_tag_3125_, v_opts_3126_, v_clsEnabled_boxed_3137_, v_oldTraces_3128_, v_msg_3129_, v_resStartStop_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec_ref(v_opts_3126_);
return v_res_3138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(lean_object* v_goal_3142_, lean_object* v_tactic_3143_, lean_object* v_allowFailure_3144_, lean_object* v_leavePercentHeartbeats_3145_, uint8_t v_includeStar_3146_, uint8_t v_collectAll_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_){
_start:
{
lean_object* v_options_3153_; lean_object* v_inheritedTraceOptions_3154_; uint8_t v_hasTrace_3155_; lean_object* v___x_3156_; 
v_options_3153_ = lean_ctor_get(v_a_3150_, 2);
v_inheritedTraceOptions_3154_ = lean_ctor_get(v_a_3150_, 13);
v_hasTrace_3155_ = lean_ctor_get_uint8(v_options_3153_, sizeof(void*)*1);
v___x_3156_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
if (v_hasTrace_3155_ == 0)
{
lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___f_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3157_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___closed__0));
v___x_3158_ = lean_box(v_collectAll_3147_);
v___x_3159_ = lean_box(v_includeStar_3146_);
v___f_3160_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed), 12, 7);
lean_closure_set(v___f_3160_, 0, v_leavePercentHeartbeats_3145_);
lean_closure_set(v___f_3160_, 1, v_goal_3142_);
lean_closure_set(v___f_3160_, 2, v___x_3157_);
lean_closure_set(v___f_3160_, 3, v_tactic_3143_);
lean_closure_set(v___f_3160_, 4, v_allowFailure_3144_);
lean_closure_set(v___f_3160_, 5, v___x_3158_);
lean_closure_set(v___f_3160_, 6, v___x_3159_);
v___x_3161_ = lean_box(0);
v___x_3162_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_3156_, v_options_3153_, v___f_3160_, v___x_3161_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_);
return v___x_3162_;
}
else
{
lean_object* v___f_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; uint8_t v___x_3167_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v_a_3171_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v_a_3186_; 
lean_inc(v_goal_3142_);
v___f_3163_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2___boxed), 7, 1);
lean_closure_set(v___f_3163_, 0, v_goal_3142_);
v___x_3164_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_3165_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__4));
v___x_3166_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2);
v___x_3167_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3154_, v_options_3153_, v___x_3166_);
if (v___x_3167_ == 0)
{
lean_object* v___x_3250_; uint8_t v___x_3251_; 
v___x_3250_ = l_Lean_trace_profiler;
v___x_3251_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_3153_, v___x_3250_);
if (v___x_3251_ == 0)
{
uint8_t v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___f_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
lean_dec_ref(v___f_3163_);
v___x_3252_ = 0;
v___x_3253_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3253_, 0, v___x_3252_);
lean_ctor_set_uint8(v___x_3253_, 1, v_hasTrace_3155_);
lean_ctor_set_uint8(v___x_3253_, 2, v_hasTrace_3155_);
lean_ctor_set_uint8(v___x_3253_, 3, v_hasTrace_3155_);
v___x_3254_ = lean_box(v_collectAll_3147_);
v___x_3255_ = lean_box(v_includeStar_3146_);
v___x_3256_ = lean_box(v___x_3251_);
v___f_3257_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4___boxed), 13, 8);
lean_closure_set(v___f_3257_, 0, v_leavePercentHeartbeats_3145_);
lean_closure_set(v___f_3257_, 1, v_goal_3142_);
lean_closure_set(v___f_3257_, 2, v___x_3253_);
lean_closure_set(v___f_3257_, 3, v_tactic_3143_);
lean_closure_set(v___f_3257_, 4, v_allowFailure_3144_);
lean_closure_set(v___f_3257_, 5, v___x_3254_);
lean_closure_set(v___f_3257_, 6, v___x_3255_);
lean_closure_set(v___f_3257_, 7, v___x_3256_);
v___x_3258_ = lean_box(0);
v___x_3259_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_3156_, v_options_3153_, v___f_3257_, v___x_3258_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_);
return v___x_3259_;
}
else
{
goto v___jp_3195_;
}
}
else
{
goto v___jp_3195_;
}
v___jp_3168_:
{
lean_object* v___x_3172_; double v___x_3173_; double v___x_3174_; double v___x_3175_; double v___x_3176_; double v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3172_ = lean_io_mono_nanos_now();
v___x_3173_ = lean_float_of_nat(v___y_3169_);
v___x_3174_ = lean_float_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3);
v___x_3175_ = lean_float_div(v___x_3173_, v___x_3174_);
v___x_3176_ = lean_float_of_nat(v___x_3172_);
v___x_3177_ = lean_float_div(v___x_3176_, v___x_3174_);
v___x_3178_ = lean_box_float(v___x_3175_);
v___x_3179_ = lean_box_float(v___x_3177_);
v___x_3180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3178_);
lean_ctor_set(v___x_3180_, 1, v___x_3179_);
v___x_3181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3181_, 0, v_a_3171_);
lean_ctor_set(v___x_3181_, 1, v___x_3180_);
v___x_3182_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v___x_3164_, v_hasTrace_3155_, v___x_3165_, v_options_3153_, v___x_3167_, v___y_3170_, v___f_3163_, v___x_3181_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_);
return v___x_3182_;
}
v___jp_3183_:
{
lean_object* v___x_3187_; double v___x_3188_; double v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3187_ = lean_io_get_num_heartbeats();
v___x_3188_ = lean_float_of_nat(v___y_3184_);
v___x_3189_ = lean_float_of_nat(v___x_3187_);
v___x_3190_ = lean_box_float(v___x_3188_);
v___x_3191_ = lean_box_float(v___x_3189_);
v___x_3192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3190_);
lean_ctor_set(v___x_3192_, 1, v___x_3191_);
v___x_3193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3193_, 0, v_a_3186_);
lean_ctor_set(v___x_3193_, 1, v___x_3192_);
v___x_3194_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v___x_3164_, v_hasTrace_3155_, v___x_3165_, v_options_3153_, v___x_3167_, v___y_3185_, v___f_3163_, v___x_3193_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_);
return v___x_3194_;
}
v___jp_3195_:
{
lean_object* v___x_3196_; lean_object* v_a_3197_; lean_object* v___x_3198_; uint8_t v___x_3199_; 
v___x_3196_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v_a_3151_);
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
lean_inc(v_a_3197_);
lean_dec_ref(v___x_3196_);
v___x_3198_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3199_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_3153_, v___x_3198_);
if (v___x_3199_ == 0)
{
lean_object* v___x_3200_; uint8_t v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___f_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3200_ = lean_io_mono_nanos_now();
v___x_3201_ = 0;
v___x_3202_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3202_, 0, v___x_3201_);
lean_ctor_set_uint8(v___x_3202_, 1, v_hasTrace_3155_);
lean_ctor_set_uint8(v___x_3202_, 2, v_hasTrace_3155_);
lean_ctor_set_uint8(v___x_3202_, 3, v_hasTrace_3155_);
v___x_3203_ = lean_box(v_collectAll_3147_);
v___x_3204_ = lean_box(v_includeStar_3146_);
v___x_3205_ = lean_box(v___x_3199_);
v___f_3206_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4___boxed), 13, 8);
lean_closure_set(v___f_3206_, 0, v_leavePercentHeartbeats_3145_);
lean_closure_set(v___f_3206_, 1, v_goal_3142_);
lean_closure_set(v___f_3206_, 2, v___x_3202_);
lean_closure_set(v___f_3206_, 3, v_tactic_3143_);
lean_closure_set(v___f_3206_, 4, v_allowFailure_3144_);
lean_closure_set(v___f_3206_, 5, v___x_3203_);
lean_closure_set(v___f_3206_, 6, v___x_3204_);
lean_closure_set(v___f_3206_, 7, v___x_3205_);
v___x_3207_ = lean_box(0);
v___x_3208_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_3156_, v_options_3153_, v___f_3206_, v___x_3207_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3216_; 
v_a_3209_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3211_ = v___x_3208_;
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3208_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3214_; 
if (v_isShared_3212_ == 0)
{
lean_ctor_set_tag(v___x_3211_, 1);
v___x_3214_ = v___x_3211_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_a_3209_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
v___y_3169_ = v___x_3200_;
v___y_3170_ = v_a_3197_;
v_a_3171_ = v___x_3214_;
goto v___jp_3168_;
}
}
}
else
{
lean_object* v_a_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3224_; 
v_a_3217_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3219_ = v___x_3208_;
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___x_3208_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v___x_3222_; 
if (v_isShared_3220_ == 0)
{
lean_ctor_set_tag(v___x_3219_, 0);
v___x_3222_ = v___x_3219_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_a_3217_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
v___y_3169_ = v___x_3200_;
v___y_3170_ = v_a_3197_;
v_a_3171_ = v___x_3222_;
goto v___jp_3168_;
}
}
}
}
else
{
lean_object* v___x_3225_; uint8_t v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___f_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
v___x_3225_ = lean_io_get_num_heartbeats();
v___x_3226_ = 0;
v___x_3227_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3227_, 0, v___x_3226_);
lean_ctor_set_uint8(v___x_3227_, 1, v___x_3199_);
lean_ctor_set_uint8(v___x_3227_, 2, v___x_3199_);
lean_ctor_set_uint8(v___x_3227_, 3, v___x_3199_);
v___x_3228_ = lean_box(v_collectAll_3147_);
v___x_3229_ = lean_box(v_includeStar_3146_);
v___x_3230_ = lean_box(v___x_3199_);
v___f_3231_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__5___boxed), 13, 8);
lean_closure_set(v___f_3231_, 0, v_leavePercentHeartbeats_3145_);
lean_closure_set(v___f_3231_, 1, v_goal_3142_);
lean_closure_set(v___f_3231_, 2, v___x_3227_);
lean_closure_set(v___f_3231_, 3, v_tactic_3143_);
lean_closure_set(v___f_3231_, 4, v_allowFailure_3144_);
lean_closure_set(v___f_3231_, 5, v___x_3228_);
lean_closure_set(v___f_3231_, 6, v___x_3229_);
lean_closure_set(v___f_3231_, 7, v___x_3230_);
v___x_3232_ = lean_box(0);
v___x_3233_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_3156_, v_options_3153_, v___f_3231_, v___x_3232_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_);
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
v_a_3234_ = lean_ctor_get(v___x_3233_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3233_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3233_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3233_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
lean_ctor_set_tag(v___x_3236_, 1);
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
v___y_3184_ = v___x_3225_;
v___y_3185_ = v_a_3197_;
v_a_3186_ = v___x_3239_;
goto v___jp_3183_;
}
}
}
else
{
lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3249_; 
v_a_3242_ = lean_ctor_get(v___x_3233_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3233_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3244_ = v___x_3233_;
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v___x_3233_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3247_; 
if (v_isShared_3245_ == 0)
{
lean_ctor_set_tag(v___x_3244_, 0);
v___x_3247_ = v___x_3244_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_a_3242_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
v___y_3184_ = v___x_3225_;
v___y_3185_ = v_a_3197_;
v_a_3186_ = v___x_3247_;
goto v___jp_3183_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___boxed(lean_object* v_goal_3260_, lean_object* v_tactic_3261_, lean_object* v_allowFailure_3262_, lean_object* v_leavePercentHeartbeats_3263_, lean_object* v_includeStar_3264_, lean_object* v_collectAll_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_){
_start:
{
uint8_t v_includeStar_boxed_3271_; uint8_t v_collectAll_boxed_3272_; lean_object* v_res_3273_; 
v_includeStar_boxed_3271_ = lean_unbox(v_includeStar_3264_);
v_collectAll_boxed_3272_ = lean_unbox(v_collectAll_3265_);
v_res_3273_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(v_goal_3260_, v_tactic_3261_, v_allowFailure_3262_, v_leavePercentHeartbeats_3263_, v_includeStar_boxed_3271_, v_collectAll_boxed_3272_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_);
lean_dec(v_a_3269_);
lean_dec_ref(v_a_3268_);
lean_dec(v_a_3267_);
lean_dec_ref(v_a_3266_);
return v_res_3273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearch(lean_object* v_goal_3274_, lean_object* v_tactic_3275_, lean_object* v_allowFailure_3276_, lean_object* v_leavePercentHeartbeats_3277_, uint8_t v_includeStar_3278_, uint8_t v_collectAll_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_){
_start:
{
lean_object* v___x_3285_; 
v___x_3285_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(v_goal_3274_, v_tactic_3275_, v_allowFailure_3276_, v_leavePercentHeartbeats_3277_, v_includeStar_3278_, v_collectAll_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_);
return v___x_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearch___boxed(lean_object* v_goal_3286_, lean_object* v_tactic_3287_, lean_object* v_allowFailure_3288_, lean_object* v_leavePercentHeartbeats_3289_, lean_object* v_includeStar_3290_, lean_object* v_collectAll_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_){
_start:
{
uint8_t v_includeStar_boxed_3297_; uint8_t v_collectAll_boxed_3298_; lean_object* v_res_3299_; 
v_includeStar_boxed_3297_ = lean_unbox(v_includeStar_3290_);
v_collectAll_boxed_3298_ = lean_unbox(v_collectAll_3291_);
v_res_3299_ = l_Lean_Meta_LibrarySearch_librarySearch(v_goal_3286_, v_tactic_3287_, v_allowFailure_3288_, v_leavePercentHeartbeats_3289_, v_includeStar_boxed_3297_, v_collectAll_boxed_3298_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_);
lean_dec(v_a_3295_);
lean_dec_ref(v_a_3294_);
lean_dec(v_a_3293_);
lean_dec_ref(v_a_3292_);
return v_res_3299_;
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
res = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_641666102____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_defaultLibSearchState = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_defaultLibSearchState);
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_instInhabitedLibSearchState = _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_instInhabitedLibSearchState();
lean_mark_persistent(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_instInhabitedLibSearchState);
res = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_ext = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_ext);
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_constantsPerImportTask = _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_constantsPerImportTask();
lean_mark_persistent(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_constantsPerImportTask);
res = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2_();
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
