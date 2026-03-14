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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapForallTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
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
lean_object* l_Lean_Meta_getTransparency___redArg(lean_object*);
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
static const lean_ctor_object l_Lean_Meta_LibrarySearch_grindDischarger___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*11 + 32, .m_other = 11, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1)),((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(10000) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1048576) << 1) | 1)),((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 0, 1, 0, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 1, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 1, 0, 1, 1)}};
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
static const lean_ctor_object l_Lean_Meta_LibrarySearch_tryDischarger___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 16, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_LibrarySearch_tryDischarger___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_LibrarySearch_tryDischarger___closed__12_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 0, 0, 0, 1),LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 0, 0, 0, 0, 0)}};
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__4_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__6___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_grindDischarger(lean_object* v_mvarId_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v___y_148_; uint8_t v___y_149_; lean_object* v_a_154_; lean_object* v___y_158_; lean_object* v___x_168_; 
lean_inc(v_mvarId_141_);
v___x_168_ = l_Lean_MVarId_getType(v_mvarId_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v_a_169_; lean_object* v___x_170_; 
v_a_169_ = lean_ctor_get(v___x_168_, 0);
lean_inc(v_a_169_);
lean_dec_ref(v___x_168_);
lean_inc(v_a_145_);
lean_inc_ref(v_a_144_);
lean_inc(v_a_143_);
lean_inc_ref(v_a_142_);
lean_inc(v_a_169_);
v___x_170_ = l_Lean_Meta_getLevel(v_a_169_, v_a_142_, v_a_143_, v_a_144_, v_a_145_);
if (lean_obj_tag(v___x_170_) == 0)
{
lean_object* v_a_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v_a_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_a_171_);
lean_dec_ref(v___x_170_);
v___x_172_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_grindDischarger___closed__2));
v___x_173_ = lean_box(0);
v___x_174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_174_, 0, v_a_171_);
lean_ctor_set(v___x_174_, 1, v___x_173_);
v___x_175_ = l_Lean_Expr_const___override(v___x_172_, v___x_174_);
v___x_176_ = l_Lean_Expr_app___override(v___x_175_, v_a_169_);
v___x_177_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_grindDischarger___closed__3));
v___x_178_ = lean_box(0);
lean_inc(v_a_145_);
lean_inc_ref(v_a_144_);
lean_inc(v_a_143_);
lean_inc_ref(v_a_142_);
v___x_179_ = l_Lean_MVarId_apply(v_mvarId_141_, v___x_176_, v___x_177_, v___x_178_, v_a_142_, v_a_143_, v_a_144_, v_a_145_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_a_180_);
lean_dec_ref(v___x_179_);
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
lean_dec_ref(v_a_180_);
v___x_183_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_grindDischarger___closed__4));
lean_inc(v_a_145_);
lean_inc_ref(v_a_144_);
lean_inc(v_a_143_);
lean_inc_ref(v_a_142_);
v___x_184_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_183_, v_a_142_, v_a_143_, v_a_144_, v_a_145_);
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
v___x_189_ = l_Lean_Meta_Grind_main(v_head_182_, v_a_185_, v_a_142_, v_a_143_, v_a_144_, v_a_145_);
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
lean_dec_ref(v___x_189_);
v_a_154_ = v_a_205_;
goto v___jp_153_;
}
}
}
else
{
lean_object* v_a_207_; 
lean_dec(v_head_182_);
lean_dec(v_a_145_);
lean_dec_ref(v_a_144_);
lean_dec(v_a_143_);
lean_dec_ref(v_a_142_);
v_a_207_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_a_207_);
lean_dec_ref(v___x_184_);
v_a_154_ = v_a_207_;
goto v___jp_153_;
}
}
else
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_Meta_LibrarySearch_grindDischarger___lam__0(v_a_180_, v_a_142_, v_a_143_, v_a_144_, v_a_145_);
lean_dec(v_a_145_);
lean_dec_ref(v_a_144_);
lean_dec(v_a_143_);
lean_dec_ref(v_a_142_);
lean_dec_ref(v_a_180_);
v___y_158_ = v___x_208_;
goto v___jp_157_;
}
}
else
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_Meta_LibrarySearch_grindDischarger___lam__0(v_a_180_, v_a_142_, v_a_143_, v_a_144_, v_a_145_);
lean_dec(v_a_145_);
lean_dec_ref(v_a_144_);
lean_dec(v_a_143_);
lean_dec_ref(v_a_142_);
lean_dec(v_a_180_);
v___y_158_ = v___x_209_;
goto v___jp_157_;
}
}
else
{
lean_object* v_a_210_; 
lean_dec(v_a_145_);
lean_dec_ref(v_a_144_);
lean_dec(v_a_143_);
lean_dec_ref(v_a_142_);
v_a_210_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_a_210_);
lean_dec_ref(v___x_179_);
v_a_154_ = v_a_210_;
goto v___jp_153_;
}
}
else
{
lean_object* v_a_211_; 
lean_dec(v_a_169_);
lean_dec(v_a_145_);
lean_dec_ref(v_a_144_);
lean_dec(v_a_143_);
lean_dec_ref(v_a_142_);
lean_dec(v_mvarId_141_);
v_a_211_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_a_211_);
lean_dec_ref(v___x_170_);
v_a_154_ = v_a_211_;
goto v___jp_153_;
}
}
else
{
lean_object* v_a_212_; 
lean_dec(v_a_145_);
lean_dec_ref(v_a_144_);
lean_dec(v_a_143_);
lean_dec_ref(v_a_142_);
lean_dec(v_mvarId_141_);
v_a_212_ = lean_ctor_get(v___x_168_, 0);
lean_inc(v_a_212_);
lean_dec_ref(v___x_168_);
v_a_154_ = v_a_212_;
goto v___jp_153_;
}
v___jp_147_:
{
if (v___y_149_ == 0)
{
lean_object* v___x_150_; lean_object* v___x_151_; 
lean_dec_ref(v___y_148_);
v___x_150_ = lean_box(0);
v___x_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
return v___x_151_;
}
else
{
lean_object* v___x_152_; 
v___x_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_152_, 0, v___y_148_);
return v___x_152_;
}
}
v___jp_153_:
{
uint8_t v___x_155_; 
v___x_155_ = l_Lean_Exception_isInterrupt(v_a_154_);
if (v___x_155_ == 0)
{
uint8_t v___x_156_; 
lean_inc_ref(v_a_154_);
v___x_156_ = l_Lean_Exception_isRuntime(v_a_154_);
v___y_148_ = v_a_154_;
v___y_149_ = v___x_156_;
goto v___jp_147_;
}
else
{
v___y_148_ = v_a_154_;
v___y_149_ = v___x_155_;
goto v___jp_147_;
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
uint8_t v___x_4039__boxed_224_; uint8_t v_res_225_; lean_object* v_r_226_; 
v___x_4039__boxed_224_ = lean_unbox(v___x_222_);
v_res_225_ = l_Lean_Meta_LibrarySearch_tryDischarger___lam__1(v___x_4039__boxed_224_, v_x_223_);
lean_dec(v_x_223_);
v_r_226_ = lean_box(v_res_225_);
return v_r_226_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_tryDischarger___closed__11(void){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Array_mkArray0(lean_box(0));
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryDischarger(lean_object* v_mvarId_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_){
_start:
{
lean_object* v___y_270_; uint8_t v___y_271_; lean_object* v_a_276_; lean_object* v___y_280_; lean_object* v___x_290_; 
lean_inc(v_mvarId_263_);
v___x_290_ = l_Lean_MVarId_getType(v_mvarId_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v_a_291_; lean_object* v___x_292_; 
v_a_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_a_291_);
lean_dec_ref(v___x_290_);
lean_inc(v_a_267_);
lean_inc_ref(v_a_266_);
lean_inc(v_a_265_);
lean_inc_ref(v_a_264_);
lean_inc(v_a_291_);
v___x_292_ = l_Lean_Meta_getLevel(v_a_291_, v_a_264_, v_a_265_, v_a_266_, v_a_267_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; uint8_t v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
lean_inc(v_a_293_);
lean_dec_ref(v___x_292_);
v___x_294_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryDischarger___closed__1));
v___x_295_ = lean_box(0);
v___x_296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_296_, 0, v_a_293_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = l_Lean_Expr_const___override(v___x_294_, v___x_296_);
v___x_298_ = l_Lean_Expr_app___override(v___x_297_, v_a_291_);
v___x_299_ = 0;
v___x_300_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_grindDischarger___closed__3));
v___x_301_ = lean_box(0);
lean_inc(v_a_267_);
lean_inc_ref(v_a_266_);
lean_inc(v_a_265_);
lean_inc_ref(v_a_264_);
v___x_302_ = l_Lean_MVarId_apply(v_mvarId_263_, v___x_298_, v___x_300_, v___x_301_, v_a_264_, v_a_265_, v_a_266_, v_a_267_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_353_; 
v_a_303_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_353_ == 0)
{
v___x_305_ = v___x_302_;
v_isShared_306_ = v_isSharedCheck_353_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_302_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_353_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
if (lean_obj_tag(v_a_303_) == 1)
{
lean_object* v_tail_307_; 
v_tail_307_ = lean_ctor_get(v_a_303_, 1);
if (lean_obj_tag(v_tail_307_) == 0)
{
lean_object* v_head_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_349_; 
lean_inc(v_tail_307_);
v_head_308_ = lean_ctor_get(v_a_303_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v_a_303_);
if (v_isSharedCheck_349_ == 0)
{
lean_object* v_unused_350_; 
v_unused_350_ = lean_ctor_get(v_a_303_, 1);
lean_dec(v_unused_350_);
v___x_310_ = v_a_303_;
v_isShared_311_ = v_isSharedCheck_349_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_head_308_);
lean_dec(v_a_303_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_349_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v_ref_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_317_; 
v_ref_312_ = lean_ctor_get(v_a_266_, 5);
v___x_313_ = l_Lean_SourceInfo_fromRef(v_ref_312_, v___x_299_);
v___x_314_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryDischarger___closed__5));
v___x_315_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryDischarger___closed__6));
lean_inc(v___x_313_);
if (v_isShared_311_ == 0)
{
lean_ctor_set_tag(v___x_310_, 2);
lean_ctor_set(v___x_310_, 1, v___x_315_);
lean_ctor_set(v___x_310_, 0, v___x_313_);
v___x_317_ = v___x_310_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_313_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v___x_315_);
v___x_317_ = v_reuseFailAlloc_348_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_318_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryDischarger___closed__8));
v___x_319_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryDischarger___closed__10));
v___x_320_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_tryDischarger___closed__11, &l_Lean_Meta_LibrarySearch_tryDischarger___closed__11_once, _init_l_Lean_Meta_LibrarySearch_tryDischarger___closed__11);
lean_inc(v___x_313_);
v___x_321_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_321_, 0, v___x_313_);
lean_ctor_set(v___x_321_, 1, v___x_319_);
lean_ctor_set(v___x_321_, 2, v___x_320_);
lean_inc(v___x_313_);
v___x_322_ = l_Lean_Syntax_node1(v___x_313_, v___x_318_, v___x_321_);
v___x_323_ = l_Lean_Syntax_node2(v___x_313_, v___x_314_, v___x_317_, v___x_322_);
v___x_324_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_324_, 0, v___x_323_);
v___x_325_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSuppressedMessages___boxed), 11, 2);
lean_closure_set(v___x_325_, 0, lean_box(0));
lean_closure_set(v___x_325_, 1, v___x_324_);
v___x_326_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_run___boxed), 9, 2);
lean_closure_set(v___x_326_, 0, v_head_308_);
lean_closure_set(v___x_326_, 1, v___x_325_);
v___x_327_ = lean_box(1);
v___x_328_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryDischarger___closed__13));
v___x_329_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_329_, 0, v___x_295_);
lean_ctor_set(v___x_329_, 1, v___x_327_);
lean_ctor_set(v___x_329_, 2, v_tail_307_);
lean_ctor_set(v___x_329_, 3, v___x_295_);
lean_ctor_set(v___x_329_, 4, v___x_295_);
lean_ctor_set(v___x_329_, 5, v___x_327_);
lean_ctor_set(v___x_329_, 6, v___x_295_);
v___x_330_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_326_, v___x_328_, v___x_329_, v_a_264_, v_a_265_, v_a_266_, v_a_267_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_346_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_346_ == 0)
{
v___x_333_ = v___x_330_;
v_isShared_334_ = v_isSharedCheck_346_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_330_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_346_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v_fst_335_; uint8_t v___x_336_; 
v_fst_335_ = lean_ctor_get(v_a_331_, 0);
lean_inc(v_fst_335_);
lean_dec(v_a_331_);
v___x_336_ = l_List_isEmpty___redArg(v_fst_335_);
lean_dec(v_fst_335_);
if (v___x_336_ == 0)
{
lean_object* v___x_338_; 
lean_del_object(v___x_305_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_301_);
v___x_338_ = v___x_333_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_301_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
else
{
lean_object* v___x_341_; 
if (v_isShared_306_ == 0)
{
lean_ctor_set_tag(v___x_305_, 1);
lean_ctor_set(v___x_305_, 0, v_tail_307_);
v___x_341_ = v___x_305_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_tail_307_);
v___x_341_ = v_reuseFailAlloc_345_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
lean_object* v___x_343_; 
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_341_);
v___x_343_ = v___x_333_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_341_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
}
else
{
lean_object* v_a_347_; 
lean_del_object(v___x_305_);
v_a_347_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_a_347_);
lean_dec_ref(v___x_330_);
v_a_276_ = v_a_347_;
goto v___jp_275_;
}
}
}
}
else
{
lean_object* v___x_351_; 
lean_del_object(v___x_305_);
v___x_351_ = l_Lean_Meta_LibrarySearch_grindDischarger___lam__0(v_a_303_, v_a_264_, v_a_265_, v_a_266_, v_a_267_);
lean_dec(v_a_267_);
lean_dec_ref(v_a_266_);
lean_dec(v_a_265_);
lean_dec_ref(v_a_264_);
lean_dec_ref(v_a_303_);
v___y_280_ = v___x_351_;
goto v___jp_279_;
}
}
else
{
lean_object* v___x_352_; 
lean_del_object(v___x_305_);
v___x_352_ = l_Lean_Meta_LibrarySearch_grindDischarger___lam__0(v_a_303_, v_a_264_, v_a_265_, v_a_266_, v_a_267_);
lean_dec(v_a_267_);
lean_dec_ref(v_a_266_);
lean_dec(v_a_265_);
lean_dec_ref(v_a_264_);
lean_dec(v_a_303_);
v___y_280_ = v___x_352_;
goto v___jp_279_;
}
}
}
else
{
lean_object* v_a_354_; 
lean_dec(v_a_267_);
lean_dec_ref(v_a_266_);
lean_dec(v_a_265_);
lean_dec_ref(v_a_264_);
v_a_354_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_a_354_);
lean_dec_ref(v___x_302_);
v_a_276_ = v_a_354_;
goto v___jp_275_;
}
}
else
{
lean_object* v_a_355_; 
lean_dec(v_a_291_);
lean_dec(v_a_267_);
lean_dec_ref(v_a_266_);
lean_dec(v_a_265_);
lean_dec_ref(v_a_264_);
lean_dec(v_mvarId_263_);
v_a_355_ = lean_ctor_get(v___x_292_, 0);
lean_inc(v_a_355_);
lean_dec_ref(v___x_292_);
v_a_276_ = v_a_355_;
goto v___jp_275_;
}
}
else
{
lean_object* v_a_356_; 
lean_dec(v_a_267_);
lean_dec_ref(v_a_266_);
lean_dec(v_a_265_);
lean_dec_ref(v_a_264_);
lean_dec(v_mvarId_263_);
v_a_356_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_a_356_);
lean_dec_ref(v___x_290_);
v_a_276_ = v_a_356_;
goto v___jp_275_;
}
v___jp_269_:
{
if (v___y_271_ == 0)
{
lean_object* v___x_272_; lean_object* v___x_273_; 
lean_dec_ref(v___y_270_);
v___x_272_ = lean_box(0);
v___x_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
return v___x_273_;
}
else
{
lean_object* v___x_274_; 
v___x_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_274_, 0, v___y_270_);
return v___x_274_;
}
}
v___jp_275_:
{
uint8_t v___x_277_; 
v___x_277_ = l_Lean_Exception_isInterrupt(v_a_276_);
if (v___x_277_ == 0)
{
uint8_t v___x_278_; 
lean_inc_ref(v_a_276_);
v___x_278_ = l_Lean_Exception_isRuntime(v_a_276_);
v___y_270_ = v_a_276_;
v___y_271_ = v___x_278_;
goto v___jp_269_;
}
else
{
v___y_270_ = v_a_276_;
v___y_271_ = v___x_277_;
goto v___jp_269_;
}
}
v___jp_279_:
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_289_; 
v_a_281_ = lean_ctor_get(v___y_280_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___y_280_);
if (v_isSharedCheck_289_ == 0)
{
v___x_283_ = v___y_280_;
v_isShared_284_ = v_isSharedCheck_289_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___y_280_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_289_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v_a_285_; lean_object* v___x_287_; 
v_a_285_ = lean_ctor_get(v_a_281_, 0);
lean_inc(v_a_285_);
lean_dec(v_a_281_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 0, v_a_285_);
v___x_287_ = v___x_283_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_a_285_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryDischarger___boxed(lean_object* v_mvarId_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_Meta_LibrarySearch_tryDischarger(v_mvarId_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(lean_object* v_msgData_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v___x_370_; lean_object* v_env_371_; lean_object* v___x_372_; lean_object* v_mctx_373_; lean_object* v_lctx_374_; lean_object* v_options_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_370_ = lean_st_ref_get(v___y_368_);
v_env_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc_ref(v_env_371_);
lean_dec(v___x_370_);
v___x_372_ = lean_st_ref_get(v___y_366_);
v_mctx_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc_ref(v_mctx_373_);
lean_dec(v___x_372_);
v_lctx_374_ = lean_ctor_get(v___y_365_, 2);
v_options_375_ = lean_ctor_get(v___y_367_, 2);
lean_inc_ref(v_options_375_);
lean_inc_ref(v_lctx_374_);
v___x_376_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_376_, 0, v_env_371_);
lean_ctor_set(v___x_376_, 1, v_mctx_373_);
lean_ctor_set(v___x_376_, 2, v_lctx_374_);
lean_ctor_set(v___x_376_, 3, v_options_375_);
v___x_377_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
lean_ctor_set(v___x_377_, 1, v_msgData_364_);
v___x_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0___boxed(lean_object* v_msgData_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(v_msgData_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(lean_object* v_msg_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v_ref_392_; lean_object* v___x_393_; lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_402_; 
v_ref_392_ = lean_ctor_get(v___y_389_, 5);
v___x_393_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(v_msg_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
v_a_394_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_402_ == 0)
{
v___x_396_ = v___x_393_;
v_isShared_397_ = v_isSharedCheck_402_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_393_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_402_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_398_; lean_object* v___x_400_; 
lean_inc(v_ref_392_);
v___x_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_398_, 0, v_ref_392_);
lean_ctor_set(v___x_398_, 1, v_a_394_);
if (v_isShared_397_ == 0)
{
lean_ctor_set_tag(v___x_396_, 1);
lean_ctor_set(v___x_396_, 0, v___x_398_);
v___x_400_ = v___x_396_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_398_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg___boxed(lean_object* v_msg_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v_msg_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
return v_res_409_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__0));
v___x_412_ = l_Lean_stringToMessageData(v___x_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__0(lean_object* v_x_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1);
v___x_420_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_419_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__0___boxed(lean_object* v_x_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_Meta_LibrarySearch_solveByElim___lam__0(v_x_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v_x_421_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__1(lean_object* v_x_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
uint8_t v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_434_ = 0;
v___x_435_ = lean_box(v___x_434_);
v___x_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__1___boxed(lean_object* v_x_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_Meta_LibrarySearch_solveByElim___lam__1(v_x_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v_x_437_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__2(lean_object* v_x_444_, lean_object* v_x_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = lean_box(0);
v___x_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__2___boxed(lean_object* v_x_453_, lean_object* v_x_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lean_Meta_LibrarySearch_solveByElim___lam__2(v_x_453_, v_x_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v_x_454_);
lean_dec(v_x_453_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim(lean_object* v_required_468_, uint8_t v_exfalso_469_, lean_object* v_goals_470_, lean_object* v_maxDepth_471_, uint8_t v_grind_472_, uint8_t v_try_x3f_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_Meta_getTransparency___redArg(v_a_474_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; lean_object* v___f_481_; lean_object* v___f_482_; lean_object* v___f_483_; uint8_t v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; lean_object* v___y_488_; lean_object* v___x_507_; lean_object* v___x_508_; uint8_t v___x_509_; lean_object* v___x_510_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_a_480_);
lean_dec_ref(v___x_479_);
v___f_481_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__0));
v___f_482_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__1));
v___f_483_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__2));
v___x_484_ = 1;
v___x_485_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_485_, 0, v_maxDepth_471_);
lean_ctor_set(v___x_485_, 1, v___f_483_);
lean_ctor_set(v___x_485_, 2, v___f_482_);
lean_ctor_set(v___x_485_, 3, v___f_481_);
lean_ctor_set_uint8(v___x_485_, sizeof(void*)*4, v___x_484_);
v___x_486_ = 0;
v___x_507_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_grindDischarger___closed__3));
v___x_508_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_508_, 0, v___x_485_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
v___x_509_ = lean_unbox(v_a_480_);
lean_dec(v_a_480_);
lean_ctor_set_uint8(v___x_508_, sizeof(void*)*2, v___x_509_);
lean_ctor_set_uint8(v___x_508_, sizeof(void*)*2 + 1, v___x_484_);
lean_ctor_set_uint8(v___x_508_, sizeof(void*)*2 + 2, v_exfalso_469_);
v___x_510_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_510_, 0, v___x_508_);
lean_ctor_set_uint8(v___x_510_, sizeof(void*)*1, v___x_484_);
lean_ctor_set_uint8(v___x_510_, sizeof(void*)*1 + 1, v___x_484_);
lean_ctor_set_uint8(v___x_510_, sizeof(void*)*1 + 2, v___x_486_);
lean_ctor_set_uint8(v___x_510_, sizeof(void*)*1 + 3, v___x_486_);
if (v_try_x3f_473_ == 0)
{
if (v_grind_472_ == 0)
{
v___y_488_ = v___x_510_;
goto v___jp_487_;
}
else
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__4));
v___x_512_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v___x_510_, v___x_511_);
v___y_488_ = v___x_512_;
goto v___jp_487_;
}
}
else
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__5));
v___x_514_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v___x_510_, v___x_513_);
v___y_488_ = v___x_514_;
goto v___jp_487_;
}
v___jp_487_:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_489_ = lean_box(0);
v___x_490_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__3));
lean_inc_ref(v_a_476_);
v___x_491_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v___x_486_, v___x_486_, v___x_489_, v___x_489_, v___x_490_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v_a_492_; lean_object* v_fst_493_; lean_object* v_snd_494_; uint8_t v___x_495_; 
v_a_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_a_492_);
lean_dec_ref(v___x_491_);
v_fst_493_ = lean_ctor_get(v_a_492_, 0);
lean_inc(v_fst_493_);
v_snd_494_ = lean_ctor_get(v_a_492_, 1);
lean_inc(v_snd_494_);
lean_dec(v_a_492_);
v___x_495_ = l_List_isEmpty___redArg(v_required_468_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(v___y_488_, v_required_468_);
v___x_497_ = l_Lean_Meta_SolveByElim_solveByElim(v___x_496_, v_fst_493_, v_snd_494_, v_goals_470_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
return v___x_497_;
}
else
{
lean_object* v___x_498_; 
lean_dec(v_required_468_);
v___x_498_ = l_Lean_Meta_SolveByElim_solveByElim(v___y_488_, v_fst_493_, v_snd_494_, v_goals_470_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
return v___x_498_;
}
}
else
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
lean_dec_ref(v___y_488_);
lean_dec(v_a_477_);
lean_dec_ref(v_a_476_);
lean_dec(v_a_475_);
lean_dec_ref(v_a_474_);
lean_dec(v_goals_470_);
lean_dec(v_required_468_);
v_a_499_ = lean_ctor_get(v___x_491_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v___x_491_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_491_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
}
else
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_522_; 
lean_dec(v_a_477_);
lean_dec_ref(v_a_476_);
lean_dec(v_a_475_);
lean_dec_ref(v_a_474_);
lean_dec(v_maxDepth_471_);
lean_dec(v_goals_470_);
lean_dec(v_required_468_);
v_a_515_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_522_ == 0)
{
v___x_517_ = v___x_479_;
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_479_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___boxed(lean_object* v_required_523_, lean_object* v_exfalso_524_, lean_object* v_goals_525_, lean_object* v_maxDepth_526_, lean_object* v_grind_527_, lean_object* v_try_x3f_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_){
_start:
{
uint8_t v_exfalso_boxed_534_; uint8_t v_grind_boxed_535_; uint8_t v_try_x3f_boxed_536_; lean_object* v_res_537_; 
v_exfalso_boxed_534_ = lean_unbox(v_exfalso_524_);
v_grind_boxed_535_ = lean_unbox(v_grind_527_);
v_try_x3f_boxed_536_ = lean_unbox(v_try_x3f_528_);
v_res_537_ = l_Lean_Meta_LibrarySearch_solveByElim(v_required_523_, v_exfalso_boxed_534_, v_goals_525_, v_maxDepth_526_, v_grind_boxed_535_, v_try_x3f_boxed_536_, v_a_529_, v_a_530_, v_a_531_, v_a_532_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0(lean_object* v_00_u03b1_538_, lean_object* v_msg_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v_msg_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___boxed(lean_object* v_00_u03b1_546_, lean_object* v_msg_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0(v_00_u03b1_546_, v_msg_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(uint8_t v_x_554_){
_start:
{
switch(v_x_554_)
{
case 0:
{
lean_object* v___x_555_; 
v___x_555_ = lean_unsigned_to_nat(0u);
return v___x_555_;
}
case 1:
{
lean_object* v___x_556_; 
v___x_556_ = lean_unsigned_to_nat(1u);
return v___x_556_;
}
default: 
{
lean_object* v___x_557_; 
v___x_557_ = lean_unsigned_to_nat(2u);
return v___x_557_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx___boxed(lean_object* v_x_558_){
_start:
{
uint8_t v_x_boxed_559_; lean_object* v_res_560_; 
v_x_boxed_559_ = lean_unbox(v_x_558_);
v_res_560_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(v_x_boxed_559_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_toCtorIdx(uint8_t v_x_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(v_x_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_toCtorIdx___boxed(lean_object* v_x_563_){
_start:
{
uint8_t v_x_4__boxed_564_; lean_object* v_res_565_; 
v_x_4__boxed_564_ = lean_unbox(v_x_563_);
v_res_565_ = l_Lean_Meta_LibrarySearch_DeclMod_toCtorIdx(v_x_4__boxed_564_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___redArg(lean_object* v_k_566_){
_start:
{
lean_inc(v_k_566_);
return v_k_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___redArg___boxed(lean_object* v_k_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___redArg(v_k_567_);
lean_dec(v_k_567_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim(lean_object* v_motive_569_, lean_object* v_ctorIdx_570_, uint8_t v_t_571_, lean_object* v_h_572_, lean_object* v_k_573_){
_start:
{
lean_inc(v_k_573_);
return v_k_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___boxed(lean_object* v_motive_574_, lean_object* v_ctorIdx_575_, lean_object* v_t_576_, lean_object* v_h_577_, lean_object* v_k_578_){
_start:
{
uint8_t v_t_boxed_579_; lean_object* v_res_580_; 
v_t_boxed_579_ = lean_unbox(v_t_576_);
v_res_580_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorElim(v_motive_574_, v_ctorIdx_575_, v_t_boxed_579_, v_h_577_, v_k_578_);
lean_dec(v_k_578_);
lean_dec(v_ctorIdx_575_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim___redArg(lean_object* v_none_581_){
_start:
{
lean_inc(v_none_581_);
return v_none_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim___redArg___boxed(lean_object* v_none_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_Meta_LibrarySearch_DeclMod_none_elim___redArg(v_none_582_);
lean_dec(v_none_582_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim(lean_object* v_motive_584_, uint8_t v_t_585_, lean_object* v_h_586_, lean_object* v_none_587_){
_start:
{
lean_inc(v_none_587_);
return v_none_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim___boxed(lean_object* v_motive_588_, lean_object* v_t_589_, lean_object* v_h_590_, lean_object* v_none_591_){
_start:
{
uint8_t v_t_boxed_592_; lean_object* v_res_593_; 
v_t_boxed_592_ = lean_unbox(v_t_589_);
v_res_593_ = l_Lean_Meta_LibrarySearch_DeclMod_none_elim(v_motive_588_, v_t_boxed_592_, v_h_590_, v_none_591_);
lean_dec(v_none_591_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___redArg(lean_object* v_mp_594_){
_start:
{
lean_inc(v_mp_594_);
return v_mp_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___redArg___boxed(lean_object* v_mp_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___redArg(v_mp_595_);
lean_dec(v_mp_595_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim(lean_object* v_motive_597_, uint8_t v_t_598_, lean_object* v_h_599_, lean_object* v_mp_600_){
_start:
{
lean_inc(v_mp_600_);
return v_mp_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___boxed(lean_object* v_motive_601_, lean_object* v_t_602_, lean_object* v_h_603_, lean_object* v_mp_604_){
_start:
{
uint8_t v_t_boxed_605_; lean_object* v_res_606_; 
v_t_boxed_605_ = lean_unbox(v_t_602_);
v_res_606_ = l_Lean_Meta_LibrarySearch_DeclMod_mp_elim(v_motive_601_, v_t_boxed_605_, v_h_603_, v_mp_604_);
lean_dec(v_mp_604_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___redArg(lean_object* v_mpr_607_){
_start:
{
lean_inc(v_mpr_607_);
return v_mpr_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___redArg___boxed(lean_object* v_mpr_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___redArg(v_mpr_608_);
lean_dec(v_mpr_608_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim(lean_object* v_motive_610_, uint8_t v_t_611_, lean_object* v_h_612_, lean_object* v_mpr_613_){
_start:
{
lean_inc(v_mpr_613_);
return v_mpr_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___boxed(lean_object* v_motive_614_, lean_object* v_t_615_, lean_object* v_h_616_, lean_object* v_mpr_617_){
_start:
{
uint8_t v_t_boxed_618_; lean_object* v_res_619_; 
v_t_boxed_618_ = lean_unbox(v_t_615_);
v_res_619_ = l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim(v_motive_614_, v_t_boxed_618_, v_h_616_, v_mpr_617_);
lean_dec(v_mpr_617_);
return v_res_619_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_DeclMod_ofNat(lean_object* v_n_620_){
_start:
{
lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_621_ = lean_unsigned_to_nat(0u);
v___x_622_ = lean_nat_dec_le(v_n_620_, v___x_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_623_ = lean_unsigned_to_nat(1u);
v___x_624_ = lean_nat_dec_le(v_n_620_, v___x_623_);
if (v___x_624_ == 0)
{
uint8_t v___x_625_; 
v___x_625_ = 2;
return v___x_625_;
}
else
{
uint8_t v___x_626_; 
v___x_626_ = 1;
return v___x_626_;
}
}
else
{
uint8_t v___x_627_; 
v___x_627_ = 0;
return v___x_627_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ofNat___boxed(lean_object* v_n_628_){
_start:
{
uint8_t v_res_629_; lean_object* v_r_630_; 
v_res_629_ = l_Lean_Meta_LibrarySearch_DeclMod_ofNat(v_n_628_);
lean_dec(v_n_628_);
v_r_630_ = lean_box(v_res_629_);
return v_r_630_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_instDecidableEqDeclMod(uint8_t v_x_631_, uint8_t v_y_632_){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_633_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(v_x_631_);
v___x_634_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(v_y_632_);
v___x_635_ = lean_nat_dec_eq(v___x_633_, v___x_634_);
lean_dec(v___x_634_);
lean_dec(v___x_633_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_instDecidableEqDeclMod___boxed(lean_object* v_x_636_, lean_object* v_y_637_){
_start:
{
uint8_t v_x_13__boxed_638_; uint8_t v_y_14__boxed_639_; uint8_t v_res_640_; lean_object* v_r_641_; 
v_x_13__boxed_638_ = lean_unbox(v_x_636_);
v_y_14__boxed_639_ = lean_unbox(v_y_637_);
v_res_640_ = l_Lean_Meta_LibrarySearch_instDecidableEqDeclMod(v_x_13__boxed_638_, v_y_14__boxed_639_);
v_r_641_ = lean_box(v_res_640_);
return v_r_641_;
}
}
static uint8_t _init_l_Lean_Meta_LibrarySearch_instInhabitedDeclMod_default(void){
_start:
{
uint8_t v___x_642_; 
v___x_642_ = 0;
return v___x_642_;
}
}
static uint8_t _init_l_Lean_Meta_LibrarySearch_instInhabitedDeclMod(void){
_start:
{
uint8_t v___x_643_; 
v___x_643_ = 0;
return v___x_643_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_instOrdDeclMod_ord(uint8_t v_x_644_, uint8_t v_y_645_){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_646_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(v_x_644_);
v___x_647_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(v_y_645_);
v___x_648_ = lean_nat_dec_lt(v___x_646_, v___x_647_);
if (v___x_648_ == 0)
{
uint8_t v___x_649_; 
v___x_649_ = lean_nat_dec_eq(v___x_646_, v___x_647_);
lean_dec(v___x_647_);
lean_dec(v___x_646_);
if (v___x_649_ == 0)
{
uint8_t v___x_650_; 
v___x_650_ = 2;
return v___x_650_;
}
else
{
uint8_t v___x_651_; 
v___x_651_ = 1;
return v___x_651_;
}
}
else
{
uint8_t v___x_652_; 
lean_dec(v___x_647_);
lean_dec(v___x_646_);
v___x_652_ = 0;
return v___x_652_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_instOrdDeclMod_ord___boxed(lean_object* v_x_653_, lean_object* v_y_654_){
_start:
{
uint8_t v_x_30__boxed_655_; uint8_t v_y_31__boxed_656_; uint8_t v_res_657_; lean_object* v_r_658_; 
v_x_30__boxed_655_ = lean_unbox(v_x_653_);
v_y_31__boxed_656_ = lean_unbox(v_y_654_);
v_res_657_ = l_Lean_Meta_LibrarySearch_instOrdDeclMod_ord(v_x_30__boxed_655_, v_y_31__boxed_656_);
v_r_658_ = lean_box(v_res_657_);
return v_r_658_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_LibrarySearch_instHashableDeclMod_hash(uint8_t v_x_661_){
_start:
{
switch(v_x_661_)
{
case 0:
{
uint64_t v___x_662_; 
v___x_662_ = 0ULL;
return v___x_662_;
}
case 1:
{
uint64_t v___x_663_; 
v___x_663_ = 1ULL;
return v___x_663_;
}
default: 
{
uint64_t v___x_664_; 
v___x_664_ = 2ULL;
return v___x_664_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_instHashableDeclMod_hash___boxed(lean_object* v_x_665_){
_start:
{
uint8_t v_x_40__boxed_666_; uint64_t v_res_667_; lean_object* v_r_668_; 
v_x_40__boxed_666_ = lean_unbox(v_x_665_);
v_res_667_ = l_Lean_Meta_LibrarySearch_instHashableDeclMod_hash(v_x_40__boxed_666_);
v_r_668_ = lean_box_uint64(v_res_667_);
return v_r_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0(lean_object* v_k_671_, lean_object* v_b_672_, lean_object* v_c_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = lean_apply_7(v_k_671_, v_b_672_, v_c_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, lean_box(0));
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0___boxed(lean_object* v_k_680_, lean_object* v_b_681_, lean_object* v_c_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0(v_k_680_, v_b_681_, v_c_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(lean_object* v_type_689_, lean_object* v_k_690_, uint8_t v_cleanupAnnotations_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v___f_697_; uint8_t v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___f_697_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_697_, 0, v_k_690_);
v___x_698_ = 0;
v___x_699_ = lean_box(0);
v___x_700_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_698_, v___x_699_, v_type_689_, v___f_697_, v_cleanupAnnotations_691_, v___x_698_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_700_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_700_);
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
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
v_a_709_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_700_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_700_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___boxed(lean_object* v_type_717_, lean_object* v_k_718_, lean_object* v_cleanupAnnotations_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_725_; lean_object* v_res_726_; 
v_cleanupAnnotations_boxed_725_ = lean_unbox(v_cleanupAnnotations_719_);
v_res_726_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(v_type_717_, v_k_718_, v_cleanupAnnotations_boxed_725_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0(lean_object* v_00_u03b1_727_, lean_object* v_type_728_, lean_object* v_k_729_, uint8_t v_cleanupAnnotations_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(v_type_728_, v_k_729_, v_cleanupAnnotations_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___boxed(lean_object* v_00_u03b1_737_, lean_object* v_type_738_, lean_object* v_k_739_, lean_object* v_cleanupAnnotations_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_746_; lean_object* v_res_747_; 
v_cleanupAnnotations_boxed_746_ = lean_unbox(v_cleanupAnnotations_740_);
v_res_747_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0(v_00_u03b1_737_, v_type_738_, v_k_739_, v_cleanupAnnotations_boxed_746_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0(lean_object* v_name_754_, lean_object* v_x_755_, lean_object* v_type_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
uint8_t v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_762_ = 0;
v___x_763_ = lean_box(v___x_762_);
lean_inc(v_name_754_);
v___x_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_764_, 0, v_name_754_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
lean_inc(v___y_760_);
lean_inc_ref(v___y_759_);
lean_inc(v___y_758_);
lean_inc_ref(v___y_757_);
v___x_765_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_type_756_, v___x_764_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_815_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_815_ == 0)
{
v___x_768_ = v___x_765_;
v_isShared_769_ = v_isSharedCheck_815_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_765_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_815_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v_key_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; 
v_key_770_ = lean_ctor_get(v_a_766_, 0);
v___x_771_ = lean_unsigned_to_nat(1u);
v___x_772_ = lean_mk_empty_array_with_capacity(v___x_771_);
lean_inc(v_a_766_);
v___x_773_ = lean_array_push(v___x_772_, v_a_766_);
v___x_774_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__2));
v___x_775_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_770_, v___x_774_);
if (v___x_775_ == 0)
{
lean_object* v___x_777_; 
lean_dec(v_a_766_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v_name_754_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v___x_773_);
v___x_777_ = v___x_768_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_773_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
else
{
lean_object* v___x_779_; uint8_t v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
lean_del_object(v___x_768_);
v___x_779_ = lean_unsigned_to_nat(0u);
v___x_780_ = 1;
v___x_781_ = lean_box(v___x_780_);
lean_inc(v_name_754_);
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v_name_754_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
lean_inc(v___y_760_);
lean_inc_ref(v___y_759_);
lean_inc(v___y_758_);
lean_inc_ref(v___y_757_);
lean_inc(v_a_766_);
v___x_783_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_a_766_, v___x_779_, v___x_782_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; uint8_t v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_784_);
lean_dec_ref(v___x_783_);
v___x_785_ = 2;
v___x_786_ = lean_box(v___x_785_);
v___x_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_787_, 0, v_name_754_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_a_766_, v___x_771_, v___x_787_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_798_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_798_ == 0)
{
v___x_791_ = v___x_788_;
v_isShared_792_ = v_isSharedCheck_798_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_788_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_798_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_796_; 
v___x_793_ = lean_array_push(v___x_773_, v_a_784_);
v___x_794_ = lean_array_push(v___x_793_, v_a_789_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_794_);
v___x_796_ = v___x_791_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_794_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec(v_a_784_);
lean_dec_ref(v___x_773_);
v_a_799_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_788_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_788_);
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
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
lean_dec_ref(v___x_773_);
lean_dec(v_a_766_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v_name_754_);
v_a_807_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_783_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_783_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_807_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
}
}
else
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v_name_754_);
v_a_816_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___x_765_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_765_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_816_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___boxed(lean_object* v_name_824_, lean_object* v_x_825_, lean_object* v_type_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0(v_name_824_, v_x_825_, v_type_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
lean_dec_ref(v_x_825_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport(lean_object* v_name_835_, lean_object* v_constInfo_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_){
_start:
{
lean_object* v___x_842_; lean_object* v_env_843_; uint8_t v___x_844_; 
v___x_842_ = lean_st_ref_get(v_a_840_);
v_env_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc_ref(v_env_843_);
lean_dec(v___x_842_);
lean_inc(v_name_835_);
v___x_844_ = l_Lean_Linter_isDeprecated(v_env_843_, v_name_835_);
if (v___x_844_ == 0)
{
uint8_t v___x_845_; 
lean_inc(v_name_835_);
v___x_845_ = l_Lean_Name_isMetaprogramming(v_name_835_);
if (v___x_845_ == 0)
{
lean_object* v___f_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___f_846_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___boxed), 8, 1);
lean_closure_set(v___f_846_, 0, v_name_835_);
v___x_847_ = l_Lean_ConstantInfo_type(v_constInfo_836_);
v___x_848_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(v___x_847_, v___f_846_, v___x_845_, v_a_837_, v_a_838_, v_a_839_, v_a_840_);
return v___x_848_;
}
else
{
lean_object* v___x_849_; lean_object* v___x_850_; 
lean_dec(v_a_840_);
lean_dec_ref(v_a_839_);
lean_dec(v_a_838_);
lean_dec_ref(v_a_837_);
lean_dec(v_name_835_);
v___x_849_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___closed__0));
v___x_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
return v___x_850_;
}
}
else
{
lean_object* v___x_851_; lean_object* v___x_852_; 
lean_dec(v_a_840_);
lean_dec_ref(v_a_839_);
lean_dec(v_a_838_);
lean_dec_ref(v_a_837_);
lean_dec(v_name_835_);
v___x_851_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___closed__0));
v___x_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
return v___x_852_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___boxed(lean_object* v_name_853_, lean_object* v_constInfo_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport(v_name_853_, v_constInfo_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
lean_dec_ref(v_constInfo_854_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_641666102____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_862_ = lean_box(0);
v___x_863_ = lean_st_mk_ref(v___x_862_);
v___x_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_641666102____hygCtx___hyg_2____boxed(lean_object* v_a_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_641666102____hygCtx___hyg_2_();
return v_res_866_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_instInhabitedLibSearchState(void){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_defaultLibSearchState;
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___lam__0_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2_(lean_object* v___x_868_){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = lean_st_mk_ref(v___x_868_);
v___x_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___lam__0_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2____boxed(lean_object* v___x_872_, lean_object* v___y_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___lam__0_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2_(v___x_872_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_878_; lean_object* v___f_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_878_ = lean_box(0);
v___f_879_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2_));
v___x_880_ = lean_box(2);
v___x_881_ = l_Lean_registerEnvExtension___redArg(v___f_879_, v___x_878_, v___x_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2____boxed(lean_object* v_a_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2561004661____hygCtx___hyg_2_();
return v_res_883_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_constantsPerImportTask(void){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = lean_unsigned_to_nat(6500u);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___lam__0_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2_(lean_object* v___x_910_){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = lean_st_mk_ref(v___x_910_);
v___x_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___lam__0_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2____boxed(lean_object* v___x_914_, lean_object* v___y_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___lam__0_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2_(v___x_914_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_920_; lean_object* v___f_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_920_ = lean_box(0);
v___f_921_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2_));
v___x_922_ = lean_box(2);
v___x_923_ = l_Lean_registerEnvExtension___redArg(v___f_921_, v___x_920_, v___x_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2____boxed(lean_object* v_a_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_956453063____hygCtx___hyg_2_();
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_libSearchFindDecls(lean_object* v_ty_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v_env_936_; lean_object* v___x_937_; lean_object* v_asyncMode_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_933_ = lean_box(0);
v___x_934_ = lean_st_mk_ref(v___x_933_);
v___x_935_ = lean_st_ref_get(v_a_931_);
v_env_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc_ref(v_env_936_);
lean_dec(v___x_935_);
v___x_937_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_starLemmasExt;
v_asyncMode_938_ = lean_ctor_get(v___x_937_, 2);
lean_inc(v_asyncMode_938_);
v___x_939_ = lean_box(0);
v___x_940_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_934_, v___x_937_, v_env_936_, v_asyncMode_938_, v___x_939_);
lean_dec(v_asyncMode_938_);
v___x_941_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_ext;
v___x_942_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__0));
v___x_943_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_droppedKeys));
v___x_944_ = lean_unsigned_to_nat(6500u);
v___x_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_945_, 0, v___x_940_);
v___x_946_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v___x_941_, v___x_942_, v___x_943_, v___x_944_, v___x_945_, v_ty_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_libSearchFindDecls___boxed(lean_object* v_ty_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_Meta_LibrarySearch_libSearchFindDecls(v_ty_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_);
return v_res_953_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2(void){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_957_ = lean_box(0);
v___x_958_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_getStarLemmas___closed__1));
v___x_959_ = l_Lean_mkConst(v___x_958_, v___x_957_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_getStarLemmas(lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v_env_970_; lean_object* v___x_971_; lean_object* v_asyncMode_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_967_ = lean_box(0);
v___x_968_ = lean_st_mk_ref(v___x_967_);
v___x_969_ = lean_st_ref_get(v_a_965_);
v_env_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc_ref(v_env_970_);
lean_dec(v___x_969_);
v___x_971_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_starLemmasExt;
v_asyncMode_972_ = lean_ctor_get(v___x_971_, 2);
lean_inc(v_asyncMode_972_);
v___x_973_ = lean_box(0);
v___x_974_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_968_, v___x_971_, v_env_970_, v_asyncMode_972_, v___x_973_);
lean_dec(v_asyncMode_972_);
v___x_975_ = lean_st_ref_get(v___x_974_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2, &l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2_once, _init_l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2);
v___x_977_ = l_Lean_Meta_LibrarySearch_libSearchFindDecls(v___x_976_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_990_; 
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_990_ == 0)
{
lean_object* v_unused_991_; 
v_unused_991_ = lean_ctor_get(v___x_977_, 0);
lean_dec(v_unused_991_);
v___x_979_ = v___x_977_;
v_isShared_980_ = v_isSharedCheck_990_;
goto v_resetjp_978_;
}
else
{
lean_dec(v___x_977_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_990_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_981_; 
v___x_981_ = lean_st_ref_get(v___x_974_);
lean_dec(v___x_974_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v___x_982_; lean_object* v___x_984_; 
v___x_982_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_getStarLemmas___closed__3));
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 0, v___x_982_);
v___x_984_ = v___x_979_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_982_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
else
{
lean_object* v_val_986_; lean_object* v___x_988_; 
v_val_986_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_val_986_);
lean_dec_ref(v___x_981_);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 0, v_val_986_);
v___x_988_ = v___x_979_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_val_986_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
else
{
lean_dec(v___x_974_);
return v___x_977_;
}
}
else
{
lean_object* v_val_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
lean_dec(v___x_974_);
lean_dec(v_a_965_);
lean_dec_ref(v_a_964_);
lean_dec(v_a_963_);
lean_dec_ref(v_a_962_);
v_val_992_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___x_975_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_val_992_);
lean_dec(v___x_975_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
lean_ctor_set_tag(v___x_994_, 0);
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_val_992_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_getStarLemmas___boxed(lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0(uint8_t v___x_1006_, lean_object* v___x_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
if (v___x_1006_ == 0)
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Lean_getRemainingHeartbeats___redArg(v___y_1010_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1023_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1016_ = v___x_1013_;
v_isShared_1017_ = v_isSharedCheck_1023_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1013_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1023_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
uint8_t v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1021_; 
v___x_1018_ = lean_nat_dec_lt(v_a_1014_, v___x_1007_);
lean_dec(v_a_1014_);
v___x_1019_ = lean_box(v___x_1018_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v___x_1019_);
v___x_1021_ = v___x_1016_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1019_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
v_a_1024_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1013_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1013_);
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
else
{
uint8_t v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1032_ = 0;
v___x_1033_ = lean_box(v___x_1032_);
v___x_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
return v___x_1034_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0___boxed(lean_object* v___x_1035_, lean_object* v___x_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
uint8_t v___x_744__boxed_1042_; lean_object* v_res_1043_; 
v___x_744__boxed_1042_ = lean_unbox(v___x_1035_);
v_res_1043_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0(v___x_744__boxed_1042_, v___x_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___x_1036_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(lean_object* v_leavePercent_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l_Lean_getMaxHeartbeats___redArg(v_a_1045_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; lean_object* v___x_1049_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_a_1048_);
lean_dec_ref(v___x_1047_);
v___x_1049_ = l_Lean_getRemainingHeartbeats___redArg(v_a_1045_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1064_; 
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1052_ = v___x_1049_;
v_isShared_1053_ = v_isSharedCheck_1064_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1049_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1064_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; lean_object* v___x_1059_; lean_object* v___y_1060_; lean_object* v___x_1062_; 
v___x_1054_ = lean_nat_mul(v_a_1050_, v_leavePercent_1044_);
lean_dec(v_a_1050_);
v___x_1055_ = lean_unsigned_to_nat(100u);
v___x_1056_ = lean_nat_div(v___x_1054_, v___x_1055_);
lean_dec(v___x_1054_);
v___x_1057_ = lean_unsigned_to_nat(0u);
v___x_1058_ = lean_nat_dec_eq(v_a_1048_, v___x_1057_);
lean_dec(v_a_1048_);
v___x_1059_ = lean_box(v___x_1058_);
v___y_1060_ = lean_alloc_closure((void*)(l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___y_1060_, 0, v___x_1059_);
lean_closure_set(v___y_1060_, 1, v___x_1056_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 0, v___y_1060_);
v___x_1062_ = v___x_1052_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___y_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
lean_dec(v_a_1048_);
v_a_1065_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___x_1049_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1049_);
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
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
v_a_1073_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1047_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1047_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___boxed(lean_object* v_leavePercent_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercent_1081_, v_a_1082_);
lean_dec_ref(v_a_1082_);
lean_dec(v_leavePercent_1081_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck(lean_object* v_leavePercent_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercent_1085_, v_a_1088_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___boxed(lean_object* v_leavePercent_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck(v_leavePercent_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
lean_dec(v_a_1094_);
lean_dec_ref(v_a_1093_);
lean_dec(v_leavePercent_1092_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(lean_object* v_upperBound_1099_, lean_object* v_x_1100_, lean_object* v_f_1101_, lean_object* v_y_1102_, lean_object* v_g_1103_, lean_object* v_a_1104_, lean_object* v_b_1105_){
_start:
{
uint8_t v___x_1106_; 
v___x_1106_ = lean_nat_dec_lt(v_a_1104_, v_upperBound_1099_);
if (v___x_1106_ == 0)
{
lean_dec(v_a_1104_);
lean_dec(v_g_1103_);
lean_dec(v_f_1101_);
return v_b_1105_;
}
else
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1107_ = lean_array_fget_borrowed(v_x_1100_, v_a_1104_);
lean_inc(v_f_1101_);
lean_inc(v___x_1107_);
v___x_1108_ = lean_apply_1(v_f_1101_, v___x_1107_);
v___x_1109_ = lean_array_push(v_b_1105_, v___x_1108_);
v___x_1110_ = lean_array_fget_borrowed(v_y_1102_, v_a_1104_);
lean_inc(v_g_1103_);
lean_inc(v___x_1110_);
v___x_1111_ = lean_apply_1(v_g_1103_, v___x_1110_);
v___x_1112_ = lean_array_push(v___x_1109_, v___x_1111_);
v___x_1113_ = lean_unsigned_to_nat(1u);
v___x_1114_ = lean_nat_add(v_a_1104_, v___x_1113_);
lean_dec(v_a_1104_);
v_a_1104_ = v___x_1114_;
v_b_1105_ = v___x_1112_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg___boxed(lean_object* v_upperBound_1116_, lean_object* v_x_1117_, lean_object* v_f_1118_, lean_object* v_y_1119_, lean_object* v_g_1120_, lean_object* v_a_1121_, lean_object* v_b_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(v_upperBound_1116_, v_x_1117_, v_f_1118_, v_y_1119_, v_g_1120_, v_a_1121_, v_b_1122_);
lean_dec_ref(v_y_1119_);
lean_dec_ref(v_x_1117_);
lean_dec(v_upperBound_1116_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(lean_object* v_g_1124_, size_t v_sz_1125_, size_t v_i_1126_, lean_object* v_bs_1127_){
_start:
{
uint8_t v___x_1128_; 
v___x_1128_ = lean_usize_dec_lt(v_i_1126_, v_sz_1125_);
if (v___x_1128_ == 0)
{
lean_dec(v_g_1124_);
return v_bs_1127_;
}
else
{
lean_object* v_v_1129_; lean_object* v___x_1130_; lean_object* v_bs_x27_1131_; lean_object* v___x_1132_; size_t v___x_1133_; size_t v___x_1134_; lean_object* v___x_1135_; 
v_v_1129_ = lean_array_uget(v_bs_1127_, v_i_1126_);
v___x_1130_ = lean_unsigned_to_nat(0u);
v_bs_x27_1131_ = lean_array_uset(v_bs_1127_, v_i_1126_, v___x_1130_);
lean_inc(v_g_1124_);
v___x_1132_ = lean_apply_1(v_g_1124_, v_v_1129_);
v___x_1133_ = ((size_t)1ULL);
v___x_1134_ = lean_usize_add(v_i_1126_, v___x_1133_);
v___x_1135_ = lean_array_uset(v_bs_x27_1131_, v_i_1126_, v___x_1132_);
v_i_1126_ = v___x_1134_;
v_bs_1127_ = v___x_1135_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg___boxed(lean_object* v_g_1137_, lean_object* v_sz_1138_, lean_object* v_i_1139_, lean_object* v_bs_1140_){
_start:
{
size_t v_sz_boxed_1141_; size_t v_i_boxed_1142_; lean_object* v_res_1143_; 
v_sz_boxed_1141_ = lean_unbox_usize(v_sz_1138_);
lean_dec(v_sz_1138_);
v_i_boxed_1142_ = lean_unbox_usize(v_i_1139_);
lean_dec(v_i_1139_);
v_res_1143_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_g_1137_, v_sz_boxed_1141_, v_i_boxed_1142_, v_bs_1140_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith___redArg(lean_object* v_f_1144_, lean_object* v_x_1145_, lean_object* v_g_1146_, lean_object* v_y_1147_){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v_res_1151_; lean_object* v___y_1153_; uint8_t v___x_1167_; 
v___x_1148_ = lean_array_get_size(v_x_1145_);
v___x_1149_ = lean_array_get_size(v_y_1147_);
v___x_1150_ = lean_nat_add(v___x_1148_, v___x_1149_);
v_res_1151_ = lean_mk_empty_array_with_capacity(v___x_1150_);
lean_dec(v___x_1150_);
v___x_1167_ = lean_nat_dec_le(v___x_1148_, v___x_1149_);
if (v___x_1167_ == 0)
{
v___y_1153_ = v___x_1149_;
goto v___jp_1152_;
}
else
{
v___y_1153_ = v___x_1148_;
goto v___jp_1152_;
}
v___jp_1152_:
{
uint8_t v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1154_ = lean_nat_dec_lt(v___y_1153_, v___x_1148_);
v___x_1155_ = lean_unsigned_to_nat(0u);
lean_inc(v_g_1146_);
lean_inc(v_f_1144_);
v___x_1156_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(v___y_1153_, v_x_1145_, v_f_1144_, v_y_1147_, v_g_1146_, v___x_1155_, v_res_1151_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1157_; size_t v_sz_1158_; size_t v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
lean_dec(v_f_1144_);
v___x_1157_ = l_Array_extract___redArg(v_y_1147_, v___y_1153_, v___x_1149_);
v_sz_1158_ = lean_array_size(v___x_1157_);
v___x_1159_ = ((size_t)0ULL);
v___x_1160_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_g_1146_, v_sz_1158_, v___x_1159_, v___x_1157_);
v___x_1161_ = l_Array_append___redArg(v___x_1156_, v___x_1160_);
lean_dec_ref(v___x_1160_);
return v___x_1161_;
}
else
{
lean_object* v___x_1162_; size_t v_sz_1163_; size_t v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
lean_dec(v_g_1146_);
v___x_1162_ = l_Array_extract___redArg(v_x_1145_, v___y_1153_, v___x_1148_);
v_sz_1163_ = lean_array_size(v___x_1162_);
v___x_1164_ = ((size_t)0ULL);
v___x_1165_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_f_1144_, v_sz_1163_, v___x_1164_, v___x_1162_);
v___x_1166_ = l_Array_append___redArg(v___x_1156_, v___x_1165_);
lean_dec_ref(v___x_1165_);
return v___x_1166_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith___redArg___boxed(lean_object* v_f_1168_, lean_object* v_x_1169_, lean_object* v_g_1170_, lean_object* v_y_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_Meta_LibrarySearch_interleaveWith___redArg(v_f_1168_, v_x_1169_, v_g_1170_, v_y_1171_);
lean_dec_ref(v_y_1171_);
lean_dec_ref(v_x_1169_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith(lean_object* v_00_u03b1_1173_, lean_object* v_00_u03b2_1174_, lean_object* v_00_u03b3_1175_, lean_object* v_f_1176_, lean_object* v_x_1177_, lean_object* v_g_1178_, lean_object* v_y_1179_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_Lean_Meta_LibrarySearch_interleaveWith___redArg(v_f_1176_, v_x_1177_, v_g_1178_, v_y_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith___boxed(lean_object* v_00_u03b1_1181_, lean_object* v_00_u03b2_1182_, lean_object* v_00_u03b3_1183_, lean_object* v_f_1184_, lean_object* v_x_1185_, lean_object* v_g_1186_, lean_object* v_y_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Lean_Meta_LibrarySearch_interleaveWith(v_00_u03b1_1181_, v_00_u03b2_1182_, v_00_u03b3_1183_, v_f_1184_, v_x_1185_, v_g_1186_, v_y_1187_);
lean_dec_ref(v_y_1187_);
lean_dec_ref(v_x_1185_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0(lean_object* v_00_u03b2_1189_, lean_object* v_00_u03b3_1190_, lean_object* v_g_1191_, size_t v_sz_1192_, size_t v_i_1193_, lean_object* v_bs_1194_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_g_1191_, v_sz_1192_, v_i_1193_, v_bs_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___boxed(lean_object* v_00_u03b2_1196_, lean_object* v_00_u03b3_1197_, lean_object* v_g_1198_, lean_object* v_sz_1199_, lean_object* v_i_1200_, lean_object* v_bs_1201_){
_start:
{
size_t v_sz_boxed_1202_; size_t v_i_boxed_1203_; lean_object* v_res_1204_; 
v_sz_boxed_1202_ = lean_unbox_usize(v_sz_1199_);
lean_dec(v_sz_1199_);
v_i_boxed_1203_ = lean_unbox_usize(v_i_1200_);
lean_dec(v_i_1200_);
v_res_1204_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0(v_00_u03b2_1196_, v_00_u03b3_1197_, v_g_1198_, v_sz_boxed_1202_, v_i_boxed_1203_, v_bs_1201_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1(lean_object* v_00_u03b3_1205_, lean_object* v_upperBound_1206_, lean_object* v_00_u03b1_1207_, lean_object* v_x_1208_, lean_object* v_f_1209_, lean_object* v_00_u03b2_1210_, lean_object* v_y_1211_, lean_object* v_g_1212_, lean_object* v_inst_1213_, lean_object* v_R_1214_, lean_object* v_a_1215_, lean_object* v_b_1216_, lean_object* v_c_1217_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(v_upperBound_1206_, v_x_1208_, v_f_1209_, v_y_1211_, v_g_1212_, v_a_1215_, v_b_1216_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___boxed(lean_object* v_00_u03b3_1219_, lean_object* v_upperBound_1220_, lean_object* v_00_u03b1_1221_, lean_object* v_x_1222_, lean_object* v_f_1223_, lean_object* v_00_u03b2_1224_, lean_object* v_y_1225_, lean_object* v_g_1226_, lean_object* v_inst_1227_, lean_object* v_R_1228_, lean_object* v_a_1229_, lean_object* v_b_1230_, lean_object* v_c_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1(v_00_u03b3_1219_, v_upperBound_1220_, v_00_u03b1_1221_, v_x_1222_, v_f_1223_, v_00_u03b2_1224_, v_y_1225_, v_g_1226_, v_inst_1227_, v_R_1228_, v_a_1229_, v_b_1230_, v_c_1231_);
lean_dec_ref(v_y_1225_);
lean_dec_ref(v_x_1222_);
lean_dec(v_upperBound_1220_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_));
v___x_1241_ = l_Lean_registerInternalExceptionId(v___x_1240_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2____boxed(lean_object* v_a_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_();
return v_res_1243_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0(void){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1244_ = lean_box(0);
v___x_1245_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_abortSpeculationId;
v___x_1246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
lean_ctor_set(v___x_1246_, 1, v___x_1244_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___redArg(lean_object* v_inst_1247_){
_start:
{
lean_object* v_throw_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v_throw_1248_ = lean_ctor_get(v_inst_1247_, 0);
lean_inc(v_throw_1248_);
lean_dec_ref(v_inst_1247_);
v___x_1249_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0, &l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0_once, _init_l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0);
v___x_1250_ = lean_apply_2(v_throw_1248_, lean_box(0), v___x_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation(lean_object* v_m_1251_, lean_object* v_00_u03b1_1252_, lean_object* v_inst_1253_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = l_Lean_Meta_LibrarySearch_abortSpeculation___redArg(v_inst_1253_);
return v___x_1254_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_isAbortSpeculation(lean_object* v_x_1255_){
_start:
{
if (lean_obj_tag(v_x_1255_) == 1)
{
lean_object* v_id_1256_; lean_object* v___x_1257_; uint8_t v___x_1258_; 
v_id_1256_ = lean_ctor_get(v_x_1255_, 0);
v___x_1257_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_abortSpeculationId;
v___x_1258_ = l_Lean_instBEqInternalExceptionId_beq(v_id_1256_, v___x_1257_);
return v___x_1258_;
}
else
{
uint8_t v___x_1259_; 
v___x_1259_ = 0;
return v___x_1259_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_isAbortSpeculation___boxed(lean_object* v_x_1260_){
_start:
{
uint8_t v_res_1261_; lean_object* v_r_1262_; 
v_res_1261_ = l_Lean_Meta_LibrarySearch_isAbortSpeculation(v_x_1260_);
lean_dec_ref(v_x_1260_);
v_r_1262_ = lean_box(v_res_1261_);
return v_r_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(lean_object* v_x_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l_Lean_Meta_saveState___redArg(v___y_1265_, v___y_1267_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; lean_object* v___x_1271_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1270_);
lean_dec_ref(v___x_1269_);
lean_inc(v___y_1267_);
lean_inc(v___y_1265_);
v___x_1271_ = lean_apply_5(v_x_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, lean_box(0));
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1280_; 
lean_dec(v_a_1270_);
lean_dec(v___y_1267_);
lean_dec(v___y_1265_);
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1274_ = v___x_1271_;
v_isShared_1275_ = v_isSharedCheck_1280_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1271_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1280_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___x_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1276_, 0, v_a_1272_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v___x_1276_);
v___x_1278_ = v___x_1274_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1276_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1310_; 
v_a_1281_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1283_ = v___x_1271_;
v_isShared_1284_ = v_isSharedCheck_1310_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1271_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1310_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
uint8_t v___y_1286_; uint8_t v___x_1308_; 
v___x_1308_ = l_Lean_Exception_isInterrupt(v_a_1281_);
if (v___x_1308_ == 0)
{
uint8_t v___x_1309_; 
lean_inc(v_a_1281_);
v___x_1309_ = l_Lean_Exception_isRuntime(v_a_1281_);
v___y_1286_ = v___x_1309_;
goto v___jp_1285_;
}
else
{
v___y_1286_ = v___x_1308_;
goto v___jp_1285_;
}
v___jp_1285_:
{
if (v___y_1286_ == 0)
{
lean_object* v___x_1287_; 
lean_del_object(v___x_1283_);
lean_dec(v_a_1281_);
v___x_1287_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1270_, v___y_1265_, v___y_1267_);
lean_dec(v___y_1267_);
lean_dec(v___y_1265_);
lean_dec(v_a_1270_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1295_; 
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1295_ == 0)
{
lean_object* v_unused_1296_; 
v_unused_1296_ = lean_ctor_get(v___x_1287_, 0);
lean_dec(v_unused_1296_);
v___x_1289_ = v___x_1287_;
v_isShared_1290_ = v_isSharedCheck_1295_;
goto v_resetjp_1288_;
}
else
{
lean_dec(v___x_1287_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1295_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1291_; lean_object* v___x_1293_; 
v___x_1291_ = lean_box(0);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1291_);
v___x_1293_ = v___x_1289_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
else
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
v_a_1297_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1287_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1287_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1297_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
else
{
lean_object* v___x_1306_; 
lean_dec(v_a_1270_);
lean_dec(v___y_1267_);
lean_dec(v___y_1265_);
if (v_isShared_1284_ == 0)
{
v___x_1306_ = v___x_1283_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1281_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
}
}
else
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec_ref(v_x_1263_);
v_a_1311_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1269_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1269_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg___boxed(lean_object* v_x_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(v_x_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0(lean_object* v_00_u03b1_1326_, lean_object* v_x_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(v_x_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___boxed(lean_object* v_00_u03b1_1334_, lean_object* v_x_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0(v_00_u03b1_1334_, v_x_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(lean_object* v_e_1342_, lean_object* v___y_1343_){
_start:
{
uint8_t v___x_1345_; 
v___x_1345_ = l_Lean_Expr_hasMVar(v_e_1342_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; 
v___x_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1346_, 0, v_e_1342_);
return v___x_1346_;
}
else
{
lean_object* v___x_1347_; lean_object* v_mctx_1348_; lean_object* v___x_1349_; lean_object* v_fst_1350_; lean_object* v_snd_1351_; lean_object* v___x_1352_; lean_object* v_cache_1353_; lean_object* v_zetaDeltaFVarIds_1354_; lean_object* v_postponed_1355_; lean_object* v_diag_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1365_; 
v___x_1347_ = lean_st_ref_get(v___y_1343_);
v_mctx_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc_ref(v_mctx_1348_);
lean_dec(v___x_1347_);
v___x_1349_ = l_Lean_instantiateMVarsCore(v_mctx_1348_, v_e_1342_);
v_fst_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_fst_1350_);
v_snd_1351_ = lean_ctor_get(v___x_1349_, 1);
lean_inc(v_snd_1351_);
lean_dec_ref(v___x_1349_);
v___x_1352_ = lean_st_ref_take(v___y_1343_);
v_cache_1353_ = lean_ctor_get(v___x_1352_, 1);
v_zetaDeltaFVarIds_1354_ = lean_ctor_get(v___x_1352_, 2);
v_postponed_1355_ = lean_ctor_get(v___x_1352_, 3);
v_diag_1356_ = lean_ctor_get(v___x_1352_, 4);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1365_ == 0)
{
lean_object* v_unused_1366_; 
v_unused_1366_ = lean_ctor_get(v___x_1352_, 0);
lean_dec(v_unused_1366_);
v___x_1358_ = v___x_1352_;
v_isShared_1359_ = v_isSharedCheck_1365_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_diag_1356_);
lean_inc(v_postponed_1355_);
lean_inc(v_zetaDeltaFVarIds_1354_);
lean_inc(v_cache_1353_);
lean_dec(v___x_1352_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1365_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 0, v_snd_1351_);
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_snd_1351_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v_cache_1353_);
lean_ctor_set(v_reuseFailAlloc_1364_, 2, v_zetaDeltaFVarIds_1354_);
lean_ctor_set(v_reuseFailAlloc_1364_, 3, v_postponed_1355_);
lean_ctor_set(v_reuseFailAlloc_1364_, 4, v_diag_1356_);
v___x_1361_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = lean_st_ref_set(v___y_1343_, v___x_1361_);
v___x_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1363_, 0, v_fst_1350_);
return v___x_1363_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg___boxed(lean_object* v_e_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(v_e_1367_, v___y_1368_);
lean_dec(v___y_1368_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1(lean_object* v_e_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v___x_1377_; 
v___x_1377_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(v_e_1371_, v___y_1373_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___boxed(lean_object* v_e_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1(v_e_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0(lean_object* v___x_1385_, lean_object* v_x_1386_){
_start:
{
lean_object* v___x_1387_; 
v___x_1387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1385_);
lean_ctor_set(v___x_1387_, 1, v_x_1386_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(lean_object* v___x_1388_, size_t v_sz_1389_, size_t v_i_1390_, lean_object* v_bs_1391_){
_start:
{
uint8_t v___x_1392_; 
v___x_1392_ = lean_usize_dec_lt(v_i_1390_, v_sz_1389_);
if (v___x_1392_ == 0)
{
lean_dec_ref(v___x_1388_);
return v_bs_1391_;
}
else
{
lean_object* v_v_1393_; lean_object* v___x_1394_; lean_object* v_bs_x27_1395_; lean_object* v___x_1396_; size_t v___x_1397_; size_t v___x_1398_; lean_object* v___x_1399_; 
v_v_1393_ = lean_array_uget(v_bs_1391_, v_i_1390_);
v___x_1394_ = lean_unsigned_to_nat(0u);
v_bs_x27_1395_ = lean_array_uset(v_bs_1391_, v_i_1390_, v___x_1394_);
lean_inc_ref(v___x_1388_);
v___x_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1388_);
lean_ctor_set(v___x_1396_, 1, v_v_1393_);
v___x_1397_ = ((size_t)1ULL);
v___x_1398_ = lean_usize_add(v_i_1390_, v___x_1397_);
v___x_1399_ = lean_array_uset(v_bs_x27_1395_, v_i_1390_, v___x_1396_);
v_i_1390_ = v___x_1398_;
v_bs_1391_ = v___x_1399_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2___boxed(lean_object* v___x_1401_, lean_object* v_sz_1402_, lean_object* v_i_1403_, lean_object* v_bs_1404_){
_start:
{
size_t v_sz_boxed_1405_; size_t v_i_boxed_1406_; lean_object* v_res_1407_; 
v_sz_boxed_1405_ = lean_unbox_usize(v_sz_1402_);
lean_dec(v_sz_1402_);
v_i_boxed_1406_ = lean_unbox_usize(v_i_1403_);
lean_dec(v_i_1403_);
v_res_1407_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(v___x_1401_, v_sz_boxed_1405_, v_i_boxed_1406_, v_bs_1404_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearchSymm(lean_object* v_searchFn_1408_, lean_object* v_goal_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_){
_start:
{
lean_object* v___x_1415_; 
lean_inc(v_goal_1409_);
v___x_1415_ = l_Lean_MVarId_getType(v_goal_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1417_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_a_1416_);
lean_dec_ref(v___x_1415_);
lean_inc_ref(v_searchFn_1408_);
lean_inc(v_a_1413_);
lean_inc_ref(v_a_1412_);
lean_inc(v_a_1411_);
lean_inc_ref(v_a_1410_);
v___x_1417_ = lean_apply_6(v_searchFn_1408_, v_a_1416_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, lean_box(0));
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v_a_1418_; lean_object* v___x_1419_; lean_object* v_mctx_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_a_1418_);
lean_dec_ref(v___x_1417_);
v___x_1419_ = lean_st_ref_get(v_a_1411_);
v_mctx_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc_ref(v_mctx_1420_);
lean_dec(v___x_1419_);
lean_inc_ref(v_mctx_1420_);
lean_inc(v_goal_1409_);
v___x_1421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1421_, 0, v_goal_1409_);
lean_ctor_set(v___x_1421_, 1, v_mctx_1420_);
v___x_1422_ = lean_alloc_closure((void*)(l_Lean_MVarId_applySymm___boxed), 6, 1);
lean_closure_set(v___x_1422_, 0, v_goal_1409_);
lean_inc(v_a_1413_);
lean_inc_ref(v_a_1412_);
lean_inc(v_a_1411_);
lean_inc_ref(v_a_1410_);
v___x_1423_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(v___x_1422_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1484_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1426_ = v___x_1423_;
v_isShared_1427_ = v_isSharedCheck_1484_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1423_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1484_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
if (lean_obj_tag(v_a_1424_) == 1)
{
lean_object* v_val_1428_; lean_object* v___x_1429_; 
lean_del_object(v___x_1426_);
v_val_1428_ = lean_ctor_get(v_a_1424_, 0);
lean_inc(v_val_1428_);
lean_dec_ref(v_a_1424_);
lean_inc(v_val_1428_);
v___x_1429_ = l_Lean_MVarId_getType(v_val_1428_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1431_; lean_object* v_a_1432_; lean_object* v___x_1433_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_a_1430_);
lean_dec_ref(v___x_1429_);
v___x_1431_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(v_a_1430_, v_a_1411_);
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_a_1432_);
lean_dec_ref(v___x_1431_);
lean_inc(v_a_1411_);
v___x_1433_ = lean_apply_6(v_searchFn_1408_, v_a_1432_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, lean_box(0));
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1461_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1436_ = v___x_1433_;
v_isShared_1437_ = v_isSharedCheck_1461_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1433_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1461_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v_cache_1440_; lean_object* v_zetaDeltaFVarIds_1441_; lean_object* v_postponed_1442_; lean_object* v_diag_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1459_; 
v___x_1438_ = lean_st_ref_get(v_a_1411_);
v___x_1439_ = lean_st_ref_take(v_a_1411_);
v_cache_1440_ = lean_ctor_get(v___x_1439_, 1);
v_zetaDeltaFVarIds_1441_ = lean_ctor_get(v___x_1439_, 2);
v_postponed_1442_ = lean_ctor_get(v___x_1439_, 3);
v_diag_1443_ = lean_ctor_get(v___x_1439_, 4);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1459_ == 0)
{
lean_object* v_unused_1460_; 
v_unused_1460_ = lean_ctor_get(v___x_1439_, 0);
lean_dec(v_unused_1460_);
v___x_1445_ = v___x_1439_;
v_isShared_1446_ = v_isSharedCheck_1459_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_diag_1443_);
lean_inc(v_postponed_1442_);
lean_inc(v_zetaDeltaFVarIds_1441_);
lean_inc(v_cache_1440_);
lean_dec(v___x_1439_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1459_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 0, v_mctx_1420_);
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_mctx_1420_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v_cache_1440_);
lean_ctor_set(v_reuseFailAlloc_1458_, 2, v_zetaDeltaFVarIds_1441_);
lean_ctor_set(v_reuseFailAlloc_1458_, 3, v_postponed_1442_);
lean_ctor_set(v_reuseFailAlloc_1458_, 4, v_diag_1443_);
v___x_1448_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
lean_object* v___x_1449_; lean_object* v_mctx_1450_; lean_object* v___f_1451_; lean_object* v___x_1452_; lean_object* v___f_1453_; lean_object* v___x_1454_; lean_object* v___x_1456_; 
v___x_1449_ = lean_st_ref_set(v_a_1411_, v___x_1448_);
lean_dec(v_a_1411_);
v_mctx_1450_ = lean_ctor_get(v___x_1438_, 0);
lean_inc_ref(v_mctx_1450_);
lean_dec(v___x_1438_);
v___f_1451_ = lean_alloc_closure((void*)(l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0), 2, 1);
lean_closure_set(v___f_1451_, 0, v___x_1421_);
v___x_1452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1452_, 0, v_val_1428_);
lean_ctor_set(v___x_1452_, 1, v_mctx_1450_);
v___f_1453_ = lean_alloc_closure((void*)(l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0), 2, 1);
lean_closure_set(v___f_1453_, 0, v___x_1452_);
v___x_1454_ = l_Lean_Meta_LibrarySearch_interleaveWith___redArg(v___f_1451_, v_a_1418_, v___f_1453_, v_a_1434_);
lean_dec(v_a_1434_);
lean_dec(v_a_1418_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 0, v___x_1454_);
v___x_1456_ = v___x_1436_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1454_);
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
else
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
lean_dec(v_val_1428_);
lean_dec_ref(v___x_1421_);
lean_dec_ref(v_mctx_1420_);
lean_dec(v_a_1418_);
lean_dec(v_a_1411_);
v_a_1462_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1464_ = v___x_1433_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1433_);
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
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec(v_val_1428_);
lean_dec_ref(v___x_1421_);
lean_dec_ref(v_mctx_1420_);
lean_dec(v_a_1418_);
lean_dec(v_a_1413_);
lean_dec_ref(v_a_1412_);
lean_dec(v_a_1411_);
lean_dec_ref(v_a_1410_);
lean_dec_ref(v_searchFn_1408_);
v_a_1470_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1429_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1429_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
else
{
size_t v_sz_1478_; size_t v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1482_; 
lean_dec(v_a_1424_);
lean_dec_ref(v_mctx_1420_);
lean_dec(v_a_1413_);
lean_dec_ref(v_a_1412_);
lean_dec(v_a_1411_);
lean_dec_ref(v_a_1410_);
lean_dec_ref(v_searchFn_1408_);
v_sz_1478_ = lean_array_size(v_a_1418_);
v___x_1479_ = ((size_t)0ULL);
v___x_1480_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(v___x_1421_, v_sz_1478_, v___x_1479_, v_a_1418_);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 0, v___x_1480_);
v___x_1482_ = v___x_1426_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1480_);
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
lean_dec_ref(v___x_1421_);
lean_dec_ref(v_mctx_1420_);
lean_dec(v_a_1418_);
lean_dec(v_a_1413_);
lean_dec_ref(v_a_1412_);
lean_dec(v_a_1411_);
lean_dec_ref(v_a_1410_);
lean_dec_ref(v_searchFn_1408_);
v_a_1485_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1423_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1423_);
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
lean_dec(v_a_1413_);
lean_dec_ref(v_a_1412_);
lean_dec(v_a_1411_);
lean_dec_ref(v_a_1410_);
lean_dec(v_goal_1409_);
lean_dec_ref(v_searchFn_1408_);
v_a_1493_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1495_ = v___x_1417_;
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___x_1417_);
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
else
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
lean_dec(v_a_1413_);
lean_dec_ref(v_a_1412_);
lean_dec(v_a_1411_);
lean_dec_ref(v_a_1410_);
lean_dec(v_goal_1409_);
lean_dec_ref(v_searchFn_1408_);
v_a_1501_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1503_ = v___x_1415_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1415_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearchSymm___boxed(lean_object* v_searchFn_1509_, lean_object* v_goal_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v_searchFn_1509_, v_goal_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0(lean_object* v_e_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1527_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___closed__1));
v___x_1528_ = lean_unsigned_to_nat(1u);
v___x_1529_ = lean_mk_empty_array_with_capacity(v___x_1528_);
v___x_1530_ = lean_array_push(v___x_1529_, v_e_1521_);
v___x_1531_ = l_Lean_Meta_mkAppM(v___x_1527_, v___x_1530_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___boxed(lean_object* v_e_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0(v_e_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1(lean_object* v_e_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___boxed(lean_object* v_e_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1(v_e_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(lean_object* v_lem_1563_, uint8_t v_mod_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_){
_start:
{
lean_object* v___x_1570_; 
lean_inc_ref(v_a_1567_);
v___x_1570_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_lem_1563_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_);
if (lean_obj_tag(v___x_1570_) == 0)
{
switch(v_mod_1564_)
{
case 0:
{
lean_dec(v_a_1568_);
lean_dec_ref(v_a_1567_);
lean_dec(v_a_1566_);
lean_dec_ref(v_a_1565_);
return v___x_1570_;
}
case 1:
{
lean_object* v_a_1571_; lean_object* v___f_1572_; lean_object* v___x_1573_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_a_1571_);
lean_dec_ref(v___x_1570_);
v___f_1572_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__0));
v___x_1573_ = l_Lean_Meta_mapForallTelescope(v___f_1572_, v_a_1571_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_);
return v___x_1573_;
}
default: 
{
lean_object* v_a_1574_; lean_object* v___f_1575_; lean_object* v___x_1576_; 
v_a_1574_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_a_1574_);
lean_dec_ref(v___x_1570_);
v___f_1575_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__1));
v___x_1576_ = l_Lean_Meta_mapForallTelescope(v___f_1575_, v_a_1574_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_);
return v___x_1576_;
}
}
}
else
{
lean_dec(v_a_1568_);
lean_dec_ref(v_a_1567_);
lean_dec(v_a_1566_);
lean_dec_ref(v_a_1565_);
return v___x_1570_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___boxed(lean_object* v_lem_1577_, lean_object* v_mod_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_){
_start:
{
uint8_t v_mod_boxed_1584_; lean_object* v_res_1585_; 
v_mod_boxed_1584_ = lean_unbox(v_mod_1578_);
v_res_1585_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_lem_1577_, v_mod_boxed_1584_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_);
return v_res_1585_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar(lean_object* v_e_1586_){
_start:
{
switch(lean_obj_tag(v_e_1586_))
{
case 0:
{
uint8_t v___x_1587_; 
v___x_1587_ = 1;
return v___x_1587_;
}
case 1:
{
uint8_t v___x_1588_; 
v___x_1588_ = 1;
return v___x_1588_;
}
case 2:
{
uint8_t v___x_1589_; 
v___x_1589_ = 1;
return v___x_1589_;
}
default: 
{
uint8_t v___x_1590_; 
v___x_1590_ = 0;
return v___x_1590_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar___boxed(lean_object* v_e_1591_){
_start:
{
uint8_t v_res_1592_; lean_object* v_r_1593_; 
v_res_1592_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar(v_e_1591_);
lean_dec_ref(v_e_1591_);
v_r_1593_ = lean_box(v_res_1592_);
return v_r_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(lean_object* v_cls_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v_options_1600_; uint8_t v_hasTrace_1601_; 
v_options_1600_ = lean_ctor_get(v___y_1598_, 2);
v_hasTrace_1601_ = lean_ctor_get_uint8(v_options_1600_, sizeof(void*)*1);
if (v_hasTrace_1601_ == 0)
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
lean_dec(v_cls_1597_);
v___x_1602_ = lean_box(v_hasTrace_1601_);
v___x_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
return v___x_1603_;
}
else
{
lean_object* v_inheritedTraceOptions_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; uint8_t v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v_inheritedTraceOptions_1604_ = lean_ctor_get(v___y_1598_, 13);
v___x_1605_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1));
v___x_1606_ = l_Lean_Name_append(v___x_1605_, v_cls_1597_);
v___x_1607_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1604_, v_options_1600_, v___x_1606_);
lean_dec(v___x_1606_);
v___x_1608_ = lean_box(v___x_1607_);
v___x_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1608_);
return v___x_1609_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___boxed(lean_object* v_cls_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v_cls_1610_, v___y_1611_);
lean_dec_ref(v___y_1611_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0(lean_object* v_cls_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v_cls_1614_, v___y_1617_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___boxed(lean_object* v_cls_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0(v_cls_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
return v_res_1627_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1628_ = lean_unsigned_to_nat(32u);
v___x_1629_ = lean_mk_empty_array_with_capacity(v___x_1628_);
v___x_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
return v___x_1630_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1631_ = ((size_t)5ULL);
v___x_1632_ = lean_unsigned_to_nat(0u);
v___x_1633_ = lean_unsigned_to_nat(32u);
v___x_1634_ = lean_mk_empty_array_with_capacity(v___x_1633_);
v___x_1635_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1___redArg___closed__0);
v___x_1636_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
lean_ctor_set(v___x_1636_, 1, v___x_1634_);
lean_ctor_set(v___x_1636_, 2, v___x_1632_);
lean_ctor_set(v___x_1636_, 3, v___x_1632_);
lean_ctor_set_usize(v___x_1636_, 4, v___x_1631_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1___redArg(lean_object* v___y_1637_){
_start:
{
lean_object* v___x_1639_; lean_object* v_traceState_1640_; lean_object* v_traces_1641_; lean_object* v___x_1642_; lean_object* v_traceState_1643_; lean_object* v_env_1644_; lean_object* v_nextMacroScope_1645_; lean_object* v_ngen_1646_; lean_object* v_auxDeclNGen_1647_; lean_object* v_cache_1648_; lean_object* v_messages_1649_; lean_object* v_infoState_1650_; lean_object* v_snapshotTasks_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1670_; 
v___x_1639_ = lean_st_ref_get(v___y_1637_);
v_traceState_1640_ = lean_ctor_get(v___x_1639_, 4);
lean_inc_ref(v_traceState_1640_);
lean_dec(v___x_1639_);
v_traces_1641_ = lean_ctor_get(v_traceState_1640_, 0);
lean_inc_ref(v_traces_1641_);
lean_dec_ref(v_traceState_1640_);
v___x_1642_ = lean_st_ref_take(v___y_1637_);
v_traceState_1643_ = lean_ctor_get(v___x_1642_, 4);
v_env_1644_ = lean_ctor_get(v___x_1642_, 0);
v_nextMacroScope_1645_ = lean_ctor_get(v___x_1642_, 1);
v_ngen_1646_ = lean_ctor_get(v___x_1642_, 2);
v_auxDeclNGen_1647_ = lean_ctor_get(v___x_1642_, 3);
v_cache_1648_ = lean_ctor_get(v___x_1642_, 5);
v_messages_1649_ = lean_ctor_get(v___x_1642_, 6);
v_infoState_1650_ = lean_ctor_get(v___x_1642_, 7);
v_snapshotTasks_1651_ = lean_ctor_get(v___x_1642_, 8);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1653_ = v___x_1642_;
v_isShared_1654_ = v_isSharedCheck_1670_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_snapshotTasks_1651_);
lean_inc(v_infoState_1650_);
lean_inc(v_messages_1649_);
lean_inc(v_cache_1648_);
lean_inc(v_traceState_1643_);
lean_inc(v_auxDeclNGen_1647_);
lean_inc(v_ngen_1646_);
lean_inc(v_nextMacroScope_1645_);
lean_inc(v_env_1644_);
lean_dec(v___x_1642_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1670_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
uint64_t v_tid_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1668_; 
v_tid_1655_ = lean_ctor_get_uint64(v_traceState_1643_, sizeof(void*)*1);
v_isSharedCheck_1668_ = !lean_is_exclusive(v_traceState_1643_);
if (v_isSharedCheck_1668_ == 0)
{
lean_object* v_unused_1669_; 
v_unused_1669_ = lean_ctor_get(v_traceState_1643_, 0);
lean_dec(v_unused_1669_);
v___x_1657_ = v_traceState_1643_;
v_isShared_1658_ = v_isSharedCheck_1668_;
goto v_resetjp_1656_;
}
else
{
lean_dec(v_traceState_1643_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1668_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1659_; lean_object* v___x_1661_; 
v___x_1659_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1___redArg___closed__1);
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 0, v___x_1659_);
v___x_1661_ = v___x_1657_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1659_);
lean_ctor_set_uint64(v_reuseFailAlloc_1667_, sizeof(void*)*1, v_tid_1655_);
v___x_1661_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
lean_object* v___x_1663_; 
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 4, v___x_1661_);
v___x_1663_ = v___x_1653_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_env_1644_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v_nextMacroScope_1645_);
lean_ctor_set(v_reuseFailAlloc_1666_, 2, v_ngen_1646_);
lean_ctor_set(v_reuseFailAlloc_1666_, 3, v_auxDeclNGen_1647_);
lean_ctor_set(v_reuseFailAlloc_1666_, 4, v___x_1661_);
lean_ctor_set(v_reuseFailAlloc_1666_, 5, v_cache_1648_);
lean_ctor_set(v_reuseFailAlloc_1666_, 6, v_messages_1649_);
lean_ctor_set(v_reuseFailAlloc_1666_, 7, v_infoState_1650_);
lean_ctor_set(v_reuseFailAlloc_1666_, 8, v_snapshotTasks_1651_);
v___x_1663_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1664_ = lean_st_ref_set(v___y_1637_, v___x_1663_);
v___x_1665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1665_, 0, v_traces_1641_);
return v___x_1665_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1___redArg___boxed(lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1___redArg(v___y_1671_);
lean_dec(v___y_1671_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1___redArg(v___y_1677_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1___boxed(lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
return v_res_1685_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(lean_object* v_opts_1686_, lean_object* v_opt_1687_){
_start:
{
lean_object* v_name_1688_; lean_object* v_defValue_1689_; lean_object* v_map_1690_; lean_object* v___x_1691_; 
v_name_1688_ = lean_ctor_get(v_opt_1687_, 0);
v_defValue_1689_ = lean_ctor_get(v_opt_1687_, 1);
v_map_1690_ = lean_ctor_get(v_opts_1686_, 0);
v___x_1691_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1690_, v_name_1688_);
if (lean_obj_tag(v___x_1691_) == 0)
{
uint8_t v___x_1692_; 
v___x_1692_ = lean_unbox(v_defValue_1689_);
return v___x_1692_;
}
else
{
lean_object* v_val_1693_; 
v_val_1693_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_val_1693_);
lean_dec_ref(v___x_1691_);
if (lean_obj_tag(v_val_1693_) == 1)
{
uint8_t v_v_1694_; 
v_v_1694_ = lean_ctor_get_uint8(v_val_1693_, 0);
lean_dec_ref(v_val_1693_);
return v_v_1694_;
}
else
{
uint8_t v___x_1695_; 
lean_dec(v_val_1693_);
v___x_1695_ = lean_unbox(v_defValue_1689_);
return v___x_1695_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___boxed(lean_object* v_opts_1696_, lean_object* v_opt_1697_){
_start:
{
uint8_t v_res_1698_; lean_object* v_r_1699_; 
v_res_1698_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v_opts_1696_, v_opt_1697_);
lean_dec_ref(v_opt_1697_);
lean_dec_ref(v_opts_1696_);
v_r_1699_ = lean_box(v_res_1698_);
return v_r_1699_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1701_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__0));
v___x_1702_ = l_Lean_stringToMessageData(v___x_1701_);
return v___x_1702_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__2));
v___x_1705_ = l_Lean_stringToMessageData(v___x_1704_);
return v___x_1705_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__5));
v___x_1710_ = l_Lean_MessageData_ofFormat(v___x_1709_);
return v___x_1710_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1714_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__8));
v___x_1715_ = l_Lean_MessageData_ofFormat(v___x_1714_);
return v___x_1715_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12(void){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__11));
v___x_1720_ = l_Lean_MessageData_ofFormat(v___x_1719_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0(lean_object* v_fst_1721_, uint8_t v_snd_1722_, lean_object* v_x_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___y_1733_; 
v___x_1729_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1);
v___x_1730_ = l_Lean_MessageData_ofName(v_fst_1721_);
v___x_1731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1729_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
switch(v_snd_1722_)
{
case 0:
{
lean_object* v___x_1738_; 
v___x_1738_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6);
v___y_1733_ = v___x_1738_;
goto v___jp_1732_;
}
case 1:
{
lean_object* v___x_1739_; 
v___x_1739_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9);
v___y_1733_ = v___x_1739_;
goto v___jp_1732_;
}
default: 
{
lean_object* v___x_1740_; 
v___x_1740_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12);
v___y_1733_ = v___x_1740_;
goto v___jp_1732_;
}
}
v___jp_1732_:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1731_);
lean_ctor_set(v___x_1734_, 1, v___y_1733_);
v___x_1735_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3);
v___x_1736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1734_);
lean_ctor_set(v___x_1736_, 1, v___x_1735_);
v___x_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1736_);
return v___x_1737_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___boxed(lean_object* v_fst_1741_, lean_object* v_snd_1742_, lean_object* v_x_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
uint8_t v_snd_11294__boxed_1749_; lean_object* v_res_1750_; 
v_snd_11294__boxed_1749_ = lean_unbox(v_snd_1742_);
v_res_1750_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0(v_fst_1741_, v_snd_11294__boxed_1749_, v_x_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec_ref(v_x_1743_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__4_spec__5(size_t v_sz_1751_, size_t v_i_1752_, lean_object* v_bs_1753_){
_start:
{
uint8_t v___x_1754_; 
v___x_1754_ = lean_usize_dec_lt(v_i_1752_, v_sz_1751_);
if (v___x_1754_ == 0)
{
return v_bs_1753_;
}
else
{
lean_object* v_v_1755_; lean_object* v_msg_1756_; lean_object* v___x_1757_; lean_object* v_bs_x27_1758_; size_t v___x_1759_; size_t v___x_1760_; lean_object* v___x_1761_; 
v_v_1755_ = lean_array_uget_borrowed(v_bs_1753_, v_i_1752_);
v_msg_1756_ = lean_ctor_get(v_v_1755_, 1);
lean_inc_ref(v_msg_1756_);
v___x_1757_ = lean_unsigned_to_nat(0u);
v_bs_x27_1758_ = lean_array_uset(v_bs_1753_, v_i_1752_, v___x_1757_);
v___x_1759_ = ((size_t)1ULL);
v___x_1760_ = lean_usize_add(v_i_1752_, v___x_1759_);
v___x_1761_ = lean_array_uset(v_bs_x27_1758_, v_i_1752_, v_msg_1756_);
v_i_1752_ = v___x_1760_;
v_bs_1753_ = v___x_1761_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__4_spec__5___boxed(lean_object* v_sz_1763_, lean_object* v_i_1764_, lean_object* v_bs_1765_){
_start:
{
size_t v_sz_boxed_1766_; size_t v_i_boxed_1767_; lean_object* v_res_1768_; 
v_sz_boxed_1766_ = lean_unbox_usize(v_sz_1763_);
lean_dec(v_sz_1763_);
v_i_boxed_1767_ = lean_unbox_usize(v_i_1764_);
lean_dec(v_i_1764_);
v_res_1768_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__4_spec__5(v_sz_boxed_1766_, v_i_boxed_1767_, v_bs_1765_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__4(lean_object* v_oldTraces_1769_, lean_object* v_data_1770_, lean_object* v_ref_1771_, lean_object* v_msg_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v_fileName_1778_; lean_object* v_fileMap_1779_; lean_object* v_options_1780_; lean_object* v_currRecDepth_1781_; lean_object* v_maxRecDepth_1782_; lean_object* v_ref_1783_; lean_object* v_currNamespace_1784_; lean_object* v_openDecls_1785_; lean_object* v_initHeartbeats_1786_; lean_object* v_maxHeartbeats_1787_; lean_object* v_quotContext_1788_; lean_object* v_currMacroScope_1789_; uint8_t v_diag_1790_; lean_object* v_cancelTk_x3f_1791_; uint8_t v_suppressElabErrors_1792_; lean_object* v_inheritedTraceOptions_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1848_; 
v_fileName_1778_ = lean_ctor_get(v___y_1775_, 0);
v_fileMap_1779_ = lean_ctor_get(v___y_1775_, 1);
v_options_1780_ = lean_ctor_get(v___y_1775_, 2);
v_currRecDepth_1781_ = lean_ctor_get(v___y_1775_, 3);
v_maxRecDepth_1782_ = lean_ctor_get(v___y_1775_, 4);
v_ref_1783_ = lean_ctor_get(v___y_1775_, 5);
v_currNamespace_1784_ = lean_ctor_get(v___y_1775_, 6);
v_openDecls_1785_ = lean_ctor_get(v___y_1775_, 7);
v_initHeartbeats_1786_ = lean_ctor_get(v___y_1775_, 8);
v_maxHeartbeats_1787_ = lean_ctor_get(v___y_1775_, 9);
v_quotContext_1788_ = lean_ctor_get(v___y_1775_, 10);
v_currMacroScope_1789_ = lean_ctor_get(v___y_1775_, 11);
v_diag_1790_ = lean_ctor_get_uint8(v___y_1775_, sizeof(void*)*14);
v_cancelTk_x3f_1791_ = lean_ctor_get(v___y_1775_, 12);
v_suppressElabErrors_1792_ = lean_ctor_get_uint8(v___y_1775_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1793_ = lean_ctor_get(v___y_1775_, 13);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___y_1775_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1795_ = v___y_1775_;
v_isShared_1796_ = v_isSharedCheck_1848_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_inheritedTraceOptions_1793_);
lean_inc(v_cancelTk_x3f_1791_);
lean_inc(v_currMacroScope_1789_);
lean_inc(v_quotContext_1788_);
lean_inc(v_maxHeartbeats_1787_);
lean_inc(v_initHeartbeats_1786_);
lean_inc(v_openDecls_1785_);
lean_inc(v_currNamespace_1784_);
lean_inc(v_ref_1783_);
lean_inc(v_maxRecDepth_1782_);
lean_inc(v_currRecDepth_1781_);
lean_inc(v_options_1780_);
lean_inc(v_fileMap_1779_);
lean_inc(v_fileName_1778_);
lean_dec(v___y_1775_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1848_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1797_; lean_object* v_traceState_1798_; lean_object* v_traces_1799_; lean_object* v_ref_1800_; lean_object* v___x_1802_; 
v___x_1797_ = lean_st_ref_get(v___y_1776_);
v_traceState_1798_ = lean_ctor_get(v___x_1797_, 4);
lean_inc_ref(v_traceState_1798_);
lean_dec(v___x_1797_);
v_traces_1799_ = lean_ctor_get(v_traceState_1798_, 0);
lean_inc_ref(v_traces_1799_);
lean_dec_ref(v_traceState_1798_);
v_ref_1800_ = l_Lean_replaceRef(v_ref_1771_, v_ref_1783_);
lean_dec(v_ref_1783_);
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 5, v_ref_1800_);
v___x_1802_ = v___x_1795_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_fileName_1778_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v_fileMap_1779_);
lean_ctor_set(v_reuseFailAlloc_1847_, 2, v_options_1780_);
lean_ctor_set(v_reuseFailAlloc_1847_, 3, v_currRecDepth_1781_);
lean_ctor_set(v_reuseFailAlloc_1847_, 4, v_maxRecDepth_1782_);
lean_ctor_set(v_reuseFailAlloc_1847_, 5, v_ref_1800_);
lean_ctor_set(v_reuseFailAlloc_1847_, 6, v_currNamespace_1784_);
lean_ctor_set(v_reuseFailAlloc_1847_, 7, v_openDecls_1785_);
lean_ctor_set(v_reuseFailAlloc_1847_, 8, v_initHeartbeats_1786_);
lean_ctor_set(v_reuseFailAlloc_1847_, 9, v_maxHeartbeats_1787_);
lean_ctor_set(v_reuseFailAlloc_1847_, 10, v_quotContext_1788_);
lean_ctor_set(v_reuseFailAlloc_1847_, 11, v_currMacroScope_1789_);
lean_ctor_set(v_reuseFailAlloc_1847_, 12, v_cancelTk_x3f_1791_);
lean_ctor_set(v_reuseFailAlloc_1847_, 13, v_inheritedTraceOptions_1793_);
lean_ctor_set_uint8(v_reuseFailAlloc_1847_, sizeof(void*)*14, v_diag_1790_);
lean_ctor_set_uint8(v_reuseFailAlloc_1847_, sizeof(void*)*14 + 1, v_suppressElabErrors_1792_);
v___x_1802_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
lean_object* v___x_1803_; size_t v_sz_1804_; size_t v___x_1805_; lean_object* v___x_1806_; lean_object* v_msg_1807_; lean_object* v___x_1808_; lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1846_; 
v___x_1803_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1799_);
lean_dec_ref(v_traces_1799_);
v_sz_1804_ = lean_array_size(v___x_1803_);
v___x_1805_ = ((size_t)0ULL);
v___x_1806_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__4_spec__5(v_sz_1804_, v___x_1805_, v___x_1803_);
v_msg_1807_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1807_, 0, v_data_1770_);
lean_ctor_set(v_msg_1807_, 1, v_msg_1772_);
lean_ctor_set(v_msg_1807_, 2, v___x_1806_);
v___x_1808_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(v_msg_1807_, v___y_1773_, v___y_1774_, v___x_1802_, v___y_1776_);
lean_dec_ref(v___x_1802_);
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1811_ = v___x_1808_;
v_isShared_1812_ = v_isSharedCheck_1846_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1808_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1846_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1813_; lean_object* v_traceState_1814_; lean_object* v_env_1815_; lean_object* v_nextMacroScope_1816_; lean_object* v_ngen_1817_; lean_object* v_auxDeclNGen_1818_; lean_object* v_cache_1819_; lean_object* v_messages_1820_; lean_object* v_infoState_1821_; lean_object* v_snapshotTasks_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1845_; 
v___x_1813_ = lean_st_ref_take(v___y_1776_);
v_traceState_1814_ = lean_ctor_get(v___x_1813_, 4);
v_env_1815_ = lean_ctor_get(v___x_1813_, 0);
v_nextMacroScope_1816_ = lean_ctor_get(v___x_1813_, 1);
v_ngen_1817_ = lean_ctor_get(v___x_1813_, 2);
v_auxDeclNGen_1818_ = lean_ctor_get(v___x_1813_, 3);
v_cache_1819_ = lean_ctor_get(v___x_1813_, 5);
v_messages_1820_ = lean_ctor_get(v___x_1813_, 6);
v_infoState_1821_ = lean_ctor_get(v___x_1813_, 7);
v_snapshotTasks_1822_ = lean_ctor_get(v___x_1813_, 8);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1824_ = v___x_1813_;
v_isShared_1825_ = v_isSharedCheck_1845_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_snapshotTasks_1822_);
lean_inc(v_infoState_1821_);
lean_inc(v_messages_1820_);
lean_inc(v_cache_1819_);
lean_inc(v_traceState_1814_);
lean_inc(v_auxDeclNGen_1818_);
lean_inc(v_ngen_1817_);
lean_inc(v_nextMacroScope_1816_);
lean_inc(v_env_1815_);
lean_dec(v___x_1813_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1845_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
uint64_t v_tid_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1843_; 
v_tid_1826_ = lean_ctor_get_uint64(v_traceState_1814_, sizeof(void*)*1);
v_isSharedCheck_1843_ = !lean_is_exclusive(v_traceState_1814_);
if (v_isSharedCheck_1843_ == 0)
{
lean_object* v_unused_1844_; 
v_unused_1844_ = lean_ctor_get(v_traceState_1814_, 0);
lean_dec(v_unused_1844_);
v___x_1828_ = v_traceState_1814_;
v_isShared_1829_ = v_isSharedCheck_1843_;
goto v_resetjp_1827_;
}
else
{
lean_dec(v_traceState_1814_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1843_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1833_; 
v___x_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1830_, 0, v_ref_1771_);
lean_ctor_set(v___x_1830_, 1, v_a_1809_);
v___x_1831_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1769_, v___x_1830_);
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 0, v___x_1831_);
v___x_1833_ = v___x_1828_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1831_);
lean_ctor_set_uint64(v_reuseFailAlloc_1842_, sizeof(void*)*1, v_tid_1826_);
v___x_1833_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
lean_object* v___x_1835_; 
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 4, v___x_1833_);
v___x_1835_ = v___x_1824_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_env_1815_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_nextMacroScope_1816_);
lean_ctor_set(v_reuseFailAlloc_1841_, 2, v_ngen_1817_);
lean_ctor_set(v_reuseFailAlloc_1841_, 3, v_auxDeclNGen_1818_);
lean_ctor_set(v_reuseFailAlloc_1841_, 4, v___x_1833_);
lean_ctor_set(v_reuseFailAlloc_1841_, 5, v_cache_1819_);
lean_ctor_set(v_reuseFailAlloc_1841_, 6, v_messages_1820_);
lean_ctor_set(v_reuseFailAlloc_1841_, 7, v_infoState_1821_);
lean_ctor_set(v_reuseFailAlloc_1841_, 8, v_snapshotTasks_1822_);
v___x_1835_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1839_; 
v___x_1836_ = lean_st_ref_set(v___y_1776_, v___x_1835_);
v___x_1837_ = lean_box(0);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 0, v___x_1837_);
v___x_1839_ = v___x_1811_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1837_);
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__4___boxed(lean_object* v_oldTraces_1849_, lean_object* v_data_1850_, lean_object* v_ref_1851_, lean_object* v_msg_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__4(v_oldTraces_1849_, v_data_1850_, v_ref_1851_, v_msg_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
lean_dec(v___y_1856_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
return v_res_1858_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__3(lean_object* v_e_1859_){
_start:
{
if (lean_obj_tag(v_e_1859_) == 0)
{
uint8_t v___x_1860_; 
v___x_1860_ = 2;
return v___x_1860_;
}
else
{
uint8_t v___x_1861_; 
v___x_1861_ = 0;
return v___x_1861_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__3___boxed(lean_object* v_e_1862_){
_start:
{
uint8_t v_res_1863_; lean_object* v_r_1864_; 
v_res_1863_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__3(v_e_1862_);
lean_dec_ref(v_e_1862_);
v_r_1864_ = lean_box(v_res_1863_);
return v_r_1864_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__5___redArg(lean_object* v_x_1865_){
_start:
{
if (lean_obj_tag(v_x_1865_) == 0)
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
v_a_1867_ = lean_ctor_get(v_x_1865_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v_x_1865_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v_x_1865_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v_x_1865_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
lean_ctor_set_tag(v___x_1869_, 1);
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1867_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
v_a_1875_ = lean_ctor_get(v_x_1865_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v_x_1865_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v_x_1865_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v_x_1865_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1878_ == 0)
{
lean_ctor_set_tag(v___x_1877_, 0);
v___x_1880_ = v___x_1877_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1875_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__5___redArg___boxed(lean_object* v_x_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__5___redArg(v_x_1883_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__6(lean_object* v_opts_1886_, lean_object* v_opt_1887_){
_start:
{
lean_object* v_name_1888_; lean_object* v_defValue_1889_; lean_object* v_map_1890_; lean_object* v___x_1891_; 
v_name_1888_ = lean_ctor_get(v_opt_1887_, 0);
v_defValue_1889_ = lean_ctor_get(v_opt_1887_, 1);
v_map_1890_ = lean_ctor_get(v_opts_1886_, 0);
v___x_1891_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1890_, v_name_1888_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_inc(v_defValue_1889_);
return v_defValue_1889_;
}
else
{
lean_object* v_val_1892_; 
v_val_1892_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_val_1892_);
lean_dec_ref(v___x_1891_);
if (lean_obj_tag(v_val_1892_) == 3)
{
lean_object* v_v_1893_; 
v_v_1893_ = lean_ctor_get(v_val_1892_, 0);
lean_inc(v_v_1893_);
lean_dec_ref(v_val_1892_);
return v_v_1893_;
}
else
{
lean_dec(v_val_1892_);
lean_inc(v_defValue_1889_);
return v_defValue_1889_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__6___boxed(lean_object* v_opts_1894_, lean_object* v_opt_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__6(v_opts_1894_, v_opt_1895_);
lean_dec_ref(v_opt_1895_);
lean_dec_ref(v_opts_1894_);
return v_res_1896_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1897_; double v___x_1898_; 
v___x_1897_ = lean_unsigned_to_nat(0u);
v___x_1898_ = lean_float_of_nat(v___x_1897_);
return v___x_1898_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1900_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3___closed__1));
v___x_1901_ = l_Lean_stringToMessageData(v___x_1900_);
return v___x_1901_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1902_; double v___x_1903_; 
v___x_1902_ = lean_unsigned_to_nat(1000u);
v___x_1903_ = lean_float_of_nat(v___x_1902_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3(lean_object* v_cls_1904_, uint8_t v_collapsed_1905_, lean_object* v_tag_1906_, lean_object* v_opts_1907_, uint8_t v_clsEnabled_1908_, lean_object* v_oldTraces_1909_, lean_object* v_msg_1910_, lean_object* v_resStartStop_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v_fst_1917_; lean_object* v_snd_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_2016_; 
v_fst_1917_ = lean_ctor_get(v_resStartStop_1911_, 0);
v_snd_1918_ = lean_ctor_get(v_resStartStop_1911_, 1);
v_isSharedCheck_2016_ = !lean_is_exclusive(v_resStartStop_1911_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_1920_ = v_resStartStop_1911_;
v_isShared_1921_ = v_isSharedCheck_2016_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_snd_1918_);
lean_inc(v_fst_1917_);
lean_dec(v_resStartStop_1911_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_2016_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v_data_1925_; lean_object* v_fst_1936_; lean_object* v_snd_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_2015_; 
v_fst_1936_ = lean_ctor_get(v_snd_1918_, 0);
v_snd_1937_ = lean_ctor_get(v_snd_1918_, 1);
v_isSharedCheck_2015_ = !lean_is_exclusive(v_snd_1918_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_1939_ = v_snd_1918_;
v_isShared_1940_ = v_isSharedCheck_2015_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_snd_1937_);
lean_inc(v_fst_1936_);
lean_dec(v_snd_1918_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_2015_;
goto v_resetjp_1938_;
}
v___jp_1922_:
{
lean_object* v___x_1926_; 
v___x_1926_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__4(v_oldTraces_1909_, v_data_1925_, v___y_1923_, v___y_1924_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
lean_dec(v___y_1915_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v___x_1927_; 
lean_dec_ref(v___x_1926_);
v___x_1927_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__5___redArg(v_fst_1917_);
return v___x_1927_;
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
lean_dec(v_fst_1917_);
v_a_1928_ = lean_ctor_get(v___x_1926_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1926_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1926_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
v_resetjp_1938_:
{
lean_object* v___x_1941_; uint8_t v___x_1942_; lean_object* v___y_1944_; lean_object* v_a_1945_; uint8_t v___y_1969_; double v___y_2000_; 
v___x_1941_ = l_Lean_trace_profiler;
v___x_1942_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v_opts_1907_, v___x_1941_);
if (v___x_1942_ == 0)
{
v___y_1969_ = v___x_1942_;
goto v___jp_1968_;
}
else
{
lean_object* v___x_2005_; uint8_t v___x_2006_; 
v___x_2005_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2006_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v_opts_1907_, v___x_2005_);
if (v___x_2006_ == 0)
{
lean_object* v___x_2007_; lean_object* v___x_2008_; double v___x_2009_; double v___x_2010_; double v___x_2011_; 
v___x_2007_ = l_Lean_trace_profiler_threshold;
v___x_2008_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__6(v_opts_1907_, v___x_2007_);
v___x_2009_ = lean_float_of_nat(v___x_2008_);
v___x_2010_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3___closed__3);
v___x_2011_ = lean_float_div(v___x_2009_, v___x_2010_);
v___y_2000_ = v___x_2011_;
goto v___jp_1999_;
}
else
{
lean_object* v___x_2012_; lean_object* v___x_2013_; double v___x_2014_; 
v___x_2012_ = l_Lean_trace_profiler_threshold;
v___x_2013_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__6(v_opts_1907_, v___x_2012_);
v___x_2014_ = lean_float_of_nat(v___x_2013_);
v___y_2000_ = v___x_2014_;
goto v___jp_1999_;
}
}
v___jp_1943_:
{
uint8_t v_result_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1951_; 
v_result_1946_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__3(v_fst_1917_);
v___x_1947_ = l_Lean_TraceResult_toEmoji(v_result_1946_);
v___x_1948_ = l_Lean_stringToMessageData(v___x_1947_);
v___x_1949_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3);
if (v_isShared_1940_ == 0)
{
lean_ctor_set_tag(v___x_1939_, 7);
lean_ctor_set(v___x_1939_, 1, v___x_1949_);
lean_ctor_set(v___x_1939_, 0, v___x_1948_);
v___x_1951_ = v___x_1939_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v___x_1948_);
lean_ctor_set(v_reuseFailAlloc_1962_, 1, v___x_1949_);
v___x_1951_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
lean_object* v_m_1953_; 
if (v_isShared_1921_ == 0)
{
lean_ctor_set_tag(v___x_1920_, 7);
lean_ctor_set(v___x_1920_, 1, v_a_1945_);
lean_ctor_set(v___x_1920_, 0, v___x_1951_);
v_m_1953_ = v___x_1920_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1951_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v_a_1945_);
v_m_1953_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; double v___x_1956_; lean_object* v_data_1957_; 
v___x_1954_ = lean_box(v_result_1946_);
v___x_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1954_);
v___x_1956_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3___closed__0);
lean_inc_ref(v_tag_1906_);
lean_inc_ref(v___x_1955_);
lean_inc(v_cls_1904_);
v_data_1957_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1957_, 0, v_cls_1904_);
lean_ctor_set(v_data_1957_, 1, v___x_1955_);
lean_ctor_set(v_data_1957_, 2, v_tag_1906_);
lean_ctor_set_float(v_data_1957_, sizeof(void*)*3, v___x_1956_);
lean_ctor_set_float(v_data_1957_, sizeof(void*)*3 + 8, v___x_1956_);
lean_ctor_set_uint8(v_data_1957_, sizeof(void*)*3 + 16, v_collapsed_1905_);
if (v___x_1942_ == 0)
{
lean_dec_ref(v___x_1955_);
lean_dec(v_snd_1937_);
lean_dec(v_fst_1936_);
lean_dec_ref(v_tag_1906_);
lean_dec(v_cls_1904_);
v___y_1923_ = v___y_1944_;
v___y_1924_ = v_m_1953_;
v_data_1925_ = v_data_1957_;
goto v___jp_1922_;
}
else
{
lean_object* v_data_1958_; double v___x_1959_; double v___x_1960_; 
lean_dec_ref(v_data_1957_);
v_data_1958_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1958_, 0, v_cls_1904_);
lean_ctor_set(v_data_1958_, 1, v___x_1955_);
lean_ctor_set(v_data_1958_, 2, v_tag_1906_);
v___x_1959_ = lean_unbox_float(v_fst_1936_);
lean_dec(v_fst_1936_);
lean_ctor_set_float(v_data_1958_, sizeof(void*)*3, v___x_1959_);
v___x_1960_ = lean_unbox_float(v_snd_1937_);
lean_dec(v_snd_1937_);
lean_ctor_set_float(v_data_1958_, sizeof(void*)*3 + 8, v___x_1960_);
lean_ctor_set_uint8(v_data_1958_, sizeof(void*)*3 + 16, v_collapsed_1905_);
v___y_1923_ = v___y_1944_;
v___y_1924_ = v_m_1953_;
v_data_1925_ = v_data_1958_;
goto v___jp_1922_;
}
}
}
}
v___jp_1963_:
{
lean_object* v_ref_1964_; lean_object* v___x_1965_; 
v_ref_1964_ = lean_ctor_get(v___y_1914_, 5);
lean_inc(v___y_1915_);
lean_inc_ref(v___y_1914_);
lean_inc(v___y_1913_);
lean_inc_ref(v___y_1912_);
lean_inc(v_fst_1917_);
v___x_1965_ = lean_apply_6(v_msg_1910_, v_fst_1917_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, lean_box(0));
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_a_1966_; 
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_a_1966_);
lean_dec_ref(v___x_1965_);
lean_inc(v_ref_1964_);
v___y_1944_ = v_ref_1964_;
v_a_1945_ = v_a_1966_;
goto v___jp_1943_;
}
else
{
lean_object* v___x_1967_; 
lean_dec_ref(v___x_1965_);
v___x_1967_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3___closed__2);
lean_inc(v_ref_1964_);
v___y_1944_ = v_ref_1964_;
v_a_1945_ = v___x_1967_;
goto v___jp_1943_;
}
}
v___jp_1968_:
{
if (v_clsEnabled_1908_ == 0)
{
if (v___y_1969_ == 0)
{
lean_object* v___x_1970_; lean_object* v_traceState_1971_; lean_object* v_env_1972_; lean_object* v_nextMacroScope_1973_; lean_object* v_ngen_1974_; lean_object* v_auxDeclNGen_1975_; lean_object* v_cache_1976_; lean_object* v_messages_1977_; lean_object* v_infoState_1978_; lean_object* v_snapshotTasks_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1998_; 
lean_del_object(v___x_1939_);
lean_dec(v_snd_1937_);
lean_dec(v_fst_1936_);
lean_del_object(v___x_1920_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec_ref(v_msg_1910_);
lean_dec_ref(v_tag_1906_);
lean_dec(v_cls_1904_);
v___x_1970_ = lean_st_ref_take(v___y_1915_);
v_traceState_1971_ = lean_ctor_get(v___x_1970_, 4);
v_env_1972_ = lean_ctor_get(v___x_1970_, 0);
v_nextMacroScope_1973_ = lean_ctor_get(v___x_1970_, 1);
v_ngen_1974_ = lean_ctor_get(v___x_1970_, 2);
v_auxDeclNGen_1975_ = lean_ctor_get(v___x_1970_, 3);
v_cache_1976_ = lean_ctor_get(v___x_1970_, 5);
v_messages_1977_ = lean_ctor_get(v___x_1970_, 6);
v_infoState_1978_ = lean_ctor_get(v___x_1970_, 7);
v_snapshotTasks_1979_ = lean_ctor_get(v___x_1970_, 8);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1981_ = v___x_1970_;
v_isShared_1982_ = v_isSharedCheck_1998_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_snapshotTasks_1979_);
lean_inc(v_infoState_1978_);
lean_inc(v_messages_1977_);
lean_inc(v_cache_1976_);
lean_inc(v_traceState_1971_);
lean_inc(v_auxDeclNGen_1975_);
lean_inc(v_ngen_1974_);
lean_inc(v_nextMacroScope_1973_);
lean_inc(v_env_1972_);
lean_dec(v___x_1970_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1998_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
uint64_t v_tid_1983_; lean_object* v_traces_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1997_; 
v_tid_1983_ = lean_ctor_get_uint64(v_traceState_1971_, sizeof(void*)*1);
v_traces_1984_ = lean_ctor_get(v_traceState_1971_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v_traceState_1971_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1986_ = v_traceState_1971_;
v_isShared_1987_ = v_isSharedCheck_1997_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_traces_1984_);
lean_dec(v_traceState_1971_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1997_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1988_; lean_object* v___x_1990_; 
v___x_1988_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1909_, v_traces_1984_);
lean_dec_ref(v_traces_1984_);
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 0, v___x_1988_);
v___x_1990_ = v___x_1986_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1988_);
lean_ctor_set_uint64(v_reuseFailAlloc_1996_, sizeof(void*)*1, v_tid_1983_);
v___x_1990_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_object* v___x_1992_; 
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 4, v___x_1990_);
v___x_1992_ = v___x_1981_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_env_1972_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v_nextMacroScope_1973_);
lean_ctor_set(v_reuseFailAlloc_1995_, 2, v_ngen_1974_);
lean_ctor_set(v_reuseFailAlloc_1995_, 3, v_auxDeclNGen_1975_);
lean_ctor_set(v_reuseFailAlloc_1995_, 4, v___x_1990_);
lean_ctor_set(v_reuseFailAlloc_1995_, 5, v_cache_1976_);
lean_ctor_set(v_reuseFailAlloc_1995_, 6, v_messages_1977_);
lean_ctor_set(v_reuseFailAlloc_1995_, 7, v_infoState_1978_);
lean_ctor_set(v_reuseFailAlloc_1995_, 8, v_snapshotTasks_1979_);
v___x_1992_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1993_ = lean_st_ref_set(v___y_1915_, v___x_1992_);
lean_dec(v___y_1915_);
v___x_1994_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__5___redArg(v_fst_1917_);
return v___x_1994_;
}
}
}
}
}
else
{
goto v___jp_1963_;
}
}
else
{
goto v___jp_1963_;
}
}
v___jp_1999_:
{
double v___x_2001_; double v___x_2002_; double v___x_2003_; uint8_t v___x_2004_; 
v___x_2001_ = lean_unbox_float(v_snd_1937_);
v___x_2002_ = lean_unbox_float(v_fst_1936_);
v___x_2003_ = lean_float_sub(v___x_2001_, v___x_2002_);
v___x_2004_ = lean_float_decLt(v___y_2000_, v___x_2003_);
v___y_1969_ = v___x_2004_;
goto v___jp_1968_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3___boxed(lean_object* v_cls_2017_, lean_object* v_collapsed_2018_, lean_object* v_tag_2019_, lean_object* v_opts_2020_, lean_object* v_clsEnabled_2021_, lean_object* v_oldTraces_2022_, lean_object* v_msg_2023_, lean_object* v_resStartStop_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
uint8_t v_collapsed_boxed_2030_; uint8_t v_clsEnabled_boxed_2031_; lean_object* v_res_2032_; 
v_collapsed_boxed_2030_ = lean_unbox(v_collapsed_2018_);
v_clsEnabled_boxed_2031_ = lean_unbox(v_clsEnabled_2021_);
v_res_2032_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3(v_cls_2017_, v_collapsed_boxed_2030_, v_tag_2019_, v_opts_2020_, v_clsEnabled_boxed_2031_, v_oldTraces_2022_, v_msg_2023_, v_resStartStop_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
lean_dec_ref(v_opts_2020_);
return v_res_2032_;
}
}
static double _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__0(void){
_start:
{
lean_object* v___x_2033_; double v___x_2034_; 
v___x_2033_ = lean_unsigned_to_nat(1000000000u);
v___x_2034_ = lean_float_of_nat(v___x_2033_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(lean_object* v_cfg_2035_, lean_object* v_act_2036_, lean_object* v_allowFailure_2037_, lean_object* v_cand_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_){
_start:
{
lean_object* v_fst_2044_; lean_object* v_snd_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2339_; 
v_fst_2044_ = lean_ctor_get(v_cand_2038_, 0);
v_snd_2045_ = lean_ctor_get(v_cand_2038_, 1);
v_isSharedCheck_2339_ = !lean_is_exclusive(v_cand_2038_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2047_ = v_cand_2038_;
v_isShared_2048_ = v_isSharedCheck_2339_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_snd_2045_);
lean_inc(v_fst_2044_);
lean_dec(v_cand_2038_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2339_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v_options_2049_; uint8_t v_hasTrace_2050_; 
v_options_2049_ = lean_ctor_get(v_a_2041_, 2);
v_hasTrace_2050_ = lean_ctor_get_uint8(v_options_2049_, sizeof(void*)*1);
if (v_hasTrace_2050_ == 0)
{
lean_object* v_fst_2051_; lean_object* v_snd_2052_; lean_object* v_fst_2053_; lean_object* v_snd_2054_; lean_object* v___x_2055_; lean_object* v_cache_2056_; lean_object* v_zetaDeltaFVarIds_2057_; lean_object* v_postponed_2058_; lean_object* v_diag_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2107_; 
lean_del_object(v___x_2047_);
v_fst_2051_ = lean_ctor_get(v_fst_2044_, 0);
lean_inc(v_fst_2051_);
v_snd_2052_ = lean_ctor_get(v_fst_2044_, 1);
lean_inc(v_snd_2052_);
lean_dec(v_fst_2044_);
v_fst_2053_ = lean_ctor_get(v_snd_2045_, 0);
lean_inc(v_fst_2053_);
v_snd_2054_ = lean_ctor_get(v_snd_2045_, 1);
lean_inc(v_snd_2054_);
lean_dec(v_snd_2045_);
v___x_2055_ = lean_st_ref_take(v_a_2040_);
v_cache_2056_ = lean_ctor_get(v___x_2055_, 1);
v_zetaDeltaFVarIds_2057_ = lean_ctor_get(v___x_2055_, 2);
v_postponed_2058_ = lean_ctor_get(v___x_2055_, 3);
v_diag_2059_ = lean_ctor_get(v___x_2055_, 4);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2107_ == 0)
{
lean_object* v_unused_2108_; 
v_unused_2108_ = lean_ctor_get(v___x_2055_, 0);
lean_dec(v_unused_2108_);
v___x_2061_ = v___x_2055_;
v_isShared_2062_ = v_isSharedCheck_2107_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_diag_2059_);
lean_inc(v_postponed_2058_);
lean_inc(v_zetaDeltaFVarIds_2057_);
lean_inc(v_cache_2056_);
lean_dec(v___x_2055_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2107_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 0, v_snd_2052_);
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_snd_2052_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v_cache_2056_);
lean_ctor_set(v_reuseFailAlloc_2106_, 2, v_zetaDeltaFVarIds_2057_);
lean_ctor_set(v_reuseFailAlloc_2106_, 3, v_postponed_2058_);
lean_ctor_set(v_reuseFailAlloc_2106_, 4, v_diag_2059_);
v___x_2064_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
lean_object* v___x_2065_; uint8_t v___x_2066_; lean_object* v___x_2067_; 
v___x_2065_ = lean_st_ref_set(v_a_2040_, v___x_2064_);
v___x_2066_ = lean_unbox(v_snd_2054_);
lean_dec(v_snd_2054_);
lean_inc(v_a_2042_);
lean_inc_ref(v_a_2041_);
lean_inc(v_a_2040_);
lean_inc_ref(v_a_2039_);
v___x_2067_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_2053_, v___x_2066_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_a_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc(v_a_2068_);
lean_dec_ref(v___x_2067_);
v___x_2069_ = lean_box(0);
lean_inc(v_a_2042_);
lean_inc_ref(v_a_2041_);
lean_inc(v_a_2040_);
lean_inc_ref(v_a_2039_);
lean_inc(v_fst_2051_);
v___x_2070_ = l_Lean_MVarId_apply(v_fst_2051_, v_a_2068_, v_cfg_2035_, v___x_2069_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2071_; lean_object* v___x_2072_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_a_2071_);
lean_dec_ref(v___x_2070_);
lean_inc(v_a_2042_);
lean_inc_ref(v_a_2041_);
lean_inc(v_a_2040_);
lean_inc_ref(v_a_2039_);
lean_inc(v_a_2071_);
v___x_2072_ = lean_apply_6(v_act_2036_, v_a_2071_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, lean_box(0));
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_dec(v_a_2071_);
lean_dec(v_fst_2051_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
lean_dec(v_a_2040_);
lean_dec_ref(v_a_2039_);
lean_dec_ref(v_allowFailure_2037_);
return v___x_2072_;
}
else
{
lean_object* v_a_2073_; uint8_t v___y_2075_; uint8_t v___x_2096_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_a_2073_);
v___x_2096_ = l_Lean_Exception_isInterrupt(v_a_2073_);
if (v___x_2096_ == 0)
{
uint8_t v___x_2097_; 
v___x_2097_ = l_Lean_Exception_isRuntime(v_a_2073_);
v___y_2075_ = v___x_2097_;
goto v___jp_2074_;
}
else
{
lean_dec(v_a_2073_);
v___y_2075_ = v___x_2096_;
goto v___jp_2074_;
}
v___jp_2074_:
{
if (v___y_2075_ == 0)
{
lean_object* v___x_2076_; 
lean_dec_ref(v___x_2072_);
lean_inc(v_a_2042_);
lean_inc_ref(v_a_2041_);
lean_inc(v_a_2040_);
lean_inc_ref(v_a_2039_);
v___x_2076_ = lean_apply_6(v_allowFailure_2037_, v_fst_2051_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, lean_box(0));
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2087_; 
v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2079_ = v___x_2076_;
v_isShared_2080_ = v_isSharedCheck_2087_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2076_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2087_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
uint8_t v___x_2081_; 
v___x_2081_ = lean_unbox(v_a_2077_);
lean_dec(v_a_2077_);
if (v___x_2081_ == 0)
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
lean_del_object(v___x_2079_);
lean_dec(v_a_2071_);
v___x_2082_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1);
v___x_2083_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2082_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
lean_dec(v_a_2040_);
lean_dec_ref(v_a_2039_);
return v___x_2083_;
}
else
{
lean_object* v___x_2085_; 
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
lean_dec(v_a_2040_);
lean_dec_ref(v_a_2039_);
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 0, v_a_2071_);
v___x_2085_ = v___x_2079_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2071_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
else
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
lean_dec(v_a_2071_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
lean_dec(v_a_2040_);
lean_dec_ref(v_a_2039_);
v_a_2088_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2090_ = v___x_2076_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2076_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2093_; 
if (v_isShared_2091_ == 0)
{
v___x_2093_ = v___x_2090_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_a_2088_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
else
{
lean_dec(v_a_2071_);
lean_dec(v_fst_2051_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
lean_dec(v_a_2040_);
lean_dec_ref(v_a_2039_);
lean_dec_ref(v_allowFailure_2037_);
return v___x_2072_;
}
}
}
}
else
{
lean_dec(v_fst_2051_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
lean_dec(v_a_2040_);
lean_dec_ref(v_a_2039_);
lean_dec_ref(v_allowFailure_2037_);
lean_dec_ref(v_act_2036_);
return v___x_2070_;
}
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2105_; 
lean_dec(v_fst_2051_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
lean_dec(v_a_2040_);
lean_dec_ref(v_a_2039_);
lean_dec_ref(v_allowFailure_2037_);
lean_dec_ref(v_act_2036_);
lean_dec_ref(v_cfg_2035_);
v_a_2098_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2100_ = v___x_2067_;
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2067_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
}
}
else
{
lean_object* v_fst_2109_; lean_object* v_snd_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2338_; 
v_fst_2109_ = lean_ctor_get(v_fst_2044_, 0);
v_snd_2110_ = lean_ctor_get(v_fst_2044_, 1);
v_isSharedCheck_2338_ = !lean_is_exclusive(v_fst_2044_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2112_ = v_fst_2044_;
v_isShared_2113_ = v_isSharedCheck_2338_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_snd_2110_);
lean_inc(v_fst_2109_);
lean_dec(v_fst_2044_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2338_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v_fst_2114_; lean_object* v_snd_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2337_; 
v_fst_2114_ = lean_ctor_get(v_snd_2045_, 0);
v_snd_2115_ = lean_ctor_get(v_snd_2045_, 1);
v_isSharedCheck_2337_ = !lean_is_exclusive(v_snd_2045_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2117_ = v_snd_2045_;
v_isShared_2118_ = v_isSharedCheck_2337_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_snd_2115_);
lean_inc(v_fst_2114_);
lean_dec(v_snd_2045_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2337_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2336_; 
v___x_2119_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_2120_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v___x_2119_, v_a_2041_);
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2123_ = v___x_2120_;
v_isShared_2124_ = v_isSharedCheck_2336_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2120_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2336_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___f_2125_; lean_object* v___x_2126_; lean_object* v___y_2128_; lean_object* v___y_2129_; lean_object* v_a_2130_; lean_object* v___y_2148_; lean_object* v___y_2149_; lean_object* v_a_2150_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v_a_2157_; lean_object* v___y_2160_; lean_object* v___y_2161_; lean_object* v___y_2162_; lean_object* v___y_2166_; lean_object* v___y_2167_; lean_object* v___y_2168_; lean_object* v___y_2169_; uint8_t v___y_2170_; lean_object* v___y_2178_; lean_object* v___y_2179_; lean_object* v_a_2180_; lean_object* v___y_2193_; lean_object* v___y_2194_; lean_object* v_a_2195_; lean_object* v___y_2198_; lean_object* v___y_2199_; lean_object* v_a_2200_; lean_object* v___y_2203_; lean_object* v___y_2204_; lean_object* v___y_2205_; lean_object* v___y_2209_; lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v___y_2212_; uint8_t v___y_2213_; uint8_t v___x_2279_; 
lean_inc(v_snd_2115_);
lean_inc(v_fst_2114_);
v___f_2125_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2125_, 0, v_fst_2114_);
lean_closure_set(v___f_2125_, 1, v_snd_2115_);
v___x_2126_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__4));
v___x_2279_ = lean_unbox(v_a_2121_);
if (v___x_2279_ == 0)
{
lean_object* v___x_2280_; uint8_t v___x_2281_; 
v___x_2280_ = l_Lean_trace_profiler;
v___x_2281_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v_options_2049_, v___x_2280_);
if (v___x_2281_ == 0)
{
lean_object* v___x_2282_; lean_object* v_cache_2283_; lean_object* v_zetaDeltaFVarIds_2284_; lean_object* v_postponed_2285_; lean_object* v_diag_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2334_; 
lean_dec_ref(v___f_2125_);
lean_del_object(v___x_2123_);
lean_dec(v_a_2121_);
lean_del_object(v___x_2117_);
lean_del_object(v___x_2112_);
lean_del_object(v___x_2047_);
v___x_2282_ = lean_st_ref_take(v_a_2040_);
v_cache_2283_ = lean_ctor_get(v___x_2282_, 1);
v_zetaDeltaFVarIds_2284_ = lean_ctor_get(v___x_2282_, 2);
v_postponed_2285_ = lean_ctor_get(v___x_2282_, 3);
v_diag_2286_ = lean_ctor_get(v___x_2282_, 4);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2334_ == 0)
{
lean_object* v_unused_2335_; 
v_unused_2335_ = lean_ctor_get(v___x_2282_, 0);
lean_dec(v_unused_2335_);
v___x_2288_ = v___x_2282_;
v_isShared_2289_ = v_isSharedCheck_2334_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_diag_2286_);
lean_inc(v_postponed_2285_);
lean_inc(v_zetaDeltaFVarIds_2284_);
lean_inc(v_cache_2283_);
lean_dec(v___x_2282_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2334_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 0, v_snd_2110_);
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_snd_2110_);
lean_ctor_set(v_reuseFailAlloc_2333_, 1, v_cache_2283_);
lean_ctor_set(v_reuseFailAlloc_2333_, 2, v_zetaDeltaFVarIds_2284_);
lean_ctor_set(v_reuseFailAlloc_2333_, 3, v_postponed_2285_);
lean_ctor_set(v_reuseFailAlloc_2333_, 4, v_diag_2286_);
v___x_2291_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
lean_object* v___x_2292_; uint8_t v___x_2293_; lean_object* v___x_2294_; 
v___x_2292_ = lean_st_ref_set(v_a_2040_, v___x_2291_);
v___x_2293_ = lean_unbox(v_snd_2115_);
lean_dec(v_snd_2115_);
lean_inc(v_a_2042_);
lean_inc_ref(v_a_2041_);
lean_inc(v_a_2040_);
lean_inc_ref(v_a_2039_);
v___x_2294_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_2114_, v___x_2293_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2295_);
lean_dec_ref(v___x_2294_);
v___x_2296_ = lean_box(0);
lean_inc(v_a_2042_);
lean_inc_ref(v_a_2041_);
lean_inc(v_a_2040_);
lean_inc_ref(v_a_2039_);
lean_inc(v_fst_2109_);
v___x_2297_ = l_Lean_MVarId_apply(v_fst_2109_, v_a_2295_, v_cfg_2035_, v___x_2296_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; lean_object* v___x_2299_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_a_2298_);
lean_dec_ref(v___x_2297_);
lean_inc(v_a_2042_);
lean_inc_ref(v_a_2041_);
lean_inc(v_a_2040_);
lean_inc_ref(v_a_2039_);
lean_inc(v_a_2298_);
v___x_2299_ = lean_apply_6(v_act_2036_, v_a_2298_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, lean_box(0));
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_dec(v_a_2298_);
lean_dec(v_fst_2109_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
lean_dec(v_a_2040_);
lean_dec_ref(v_a_2039_);
lean_dec_ref(v_allowFailure_2037_);
return v___x_2299_;
}
else
{
lean_object* v_a_2300_; uint8_t v___y_2302_; uint8_t v___x_2323_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2300_);
v___x_2323_ = l_Lean_Exception_isInterrupt(v_a_2300_);
if (v___x_2323_ == 0)
{
uint8_t v___x_2324_; 
v___x_2324_ = l_Lean_Exception_isRuntime(v_a_2300_);
v___y_2302_ = v___x_2324_;
goto v___jp_2301_;
}
else
{
lean_dec(v_a_2300_);
v___y_2302_ = v___x_2323_;
goto v___jp_2301_;
}
v___jp_2301_:
{
if (v___y_2302_ == 0)
{
lean_object* v___x_2303_; 
lean_dec_ref(v___x_2299_);
lean_inc(v_a_2042_);
lean_inc_ref(v_a_2041_);
lean_inc(v_a_2040_);
lean_inc_ref(v_a_2039_);
v___x_2303_ = lean_apply_6(v_allowFailure_2037_, v_fst_2109_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, lean_box(0));
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2314_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2306_ = v___x_2303_;
v_isShared_2307_ = v_isSharedCheck_2314_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2303_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2314_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
uint8_t v___x_2308_; 
v___x_2308_ = lean_unbox(v_a_2304_);
lean_dec(v_a_2304_);
if (v___x_2308_ == 0)
{
lean_object* v___x_2309_; lean_object* v___x_2310_; 
lean_del_object(v___x_2306_);
lean_dec(v_a_2298_);
v___x_2309_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1);
v___x_2310_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2309_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
lean_dec(v_a_2040_);
lean_dec_ref(v_a_2039_);
return v___x_2310_;
}
else
{
lean_object* v___x_2312_; 
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
lean_dec(v_a_2040_);
lean_dec_ref(v_a_2039_);
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 0, v_a_2298_);
v___x_2312_ = v___x_2306_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2298_);
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
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
lean_dec(v_a_2298_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
lean_dec(v_a_2040_);
lean_dec_ref(v_a_2039_);
v_a_2315_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___x_2303_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2303_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
else
{
lean_dec(v_a_2298_);
lean_dec(v_fst_2109_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
lean_dec(v_a_2040_);
lean_dec_ref(v_a_2039_);
lean_dec_ref(v_allowFailure_2037_);
return v___x_2299_;
}
}
}
}
else
{
lean_dec(v_fst_2109_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
lean_dec(v_a_2040_);
lean_dec_ref(v_a_2039_);
lean_dec_ref(v_allowFailure_2037_);
lean_dec_ref(v_act_2036_);
return v___x_2297_;
}
}
else
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2332_; 
lean_dec(v_fst_2109_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
lean_dec(v_a_2040_);
lean_dec_ref(v_a_2039_);
lean_dec_ref(v_allowFailure_2037_);
lean_dec_ref(v_act_2036_);
lean_dec_ref(v_cfg_2035_);
v_a_2325_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2327_ = v___x_2294_;
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2294_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2330_; 
if (v_isShared_2328_ == 0)
{
v___x_2330_ = v___x_2327_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_a_2325_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
}
}
else
{
lean_inc_ref(v_options_2049_);
goto v___jp_2220_;
}
}
else
{
lean_inc_ref(v_options_2049_);
goto v___jp_2220_;
}
v___jp_2127_:
{
lean_object* v___x_2131_; double v___x_2132_; double v___x_2133_; double v___x_2134_; double v___x_2135_; double v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2140_; 
v___x_2131_ = lean_io_mono_nanos_now();
v___x_2132_ = lean_float_of_nat(v___y_2128_);
v___x_2133_ = lean_float_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__0, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__0_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__0);
v___x_2134_ = lean_float_div(v___x_2132_, v___x_2133_);
v___x_2135_ = lean_float_of_nat(v___x_2131_);
v___x_2136_ = lean_float_div(v___x_2135_, v___x_2133_);
v___x_2137_ = lean_box_float(v___x_2134_);
v___x_2138_ = lean_box_float(v___x_2136_);
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 1, v___x_2138_);
lean_ctor_set(v___x_2117_, 0, v___x_2137_);
v___x_2140_ = v___x_2117_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2137_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v___x_2138_);
v___x_2140_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
lean_object* v___x_2142_; 
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 1, v___x_2140_);
lean_ctor_set(v___x_2112_, 0, v_a_2130_);
v___x_2142_ = v___x_2112_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2130_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v___x_2140_);
v___x_2142_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
uint8_t v___x_2143_; lean_object* v___x_2144_; 
v___x_2143_ = lean_unbox(v_a_2121_);
lean_dec(v_a_2121_);
v___x_2144_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3(v___x_2119_, v_hasTrace_2050_, v___x_2126_, v_options_2049_, v___x_2143_, v___y_2129_, v___f_2125_, v___x_2142_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
lean_dec_ref(v_options_2049_);
return v___x_2144_;
}
}
}
v___jp_2147_:
{
lean_object* v___x_2152_; 
if (v_isShared_2124_ == 0)
{
lean_ctor_set_tag(v___x_2123_, 1);
lean_ctor_set(v___x_2123_, 0, v_a_2150_);
v___x_2152_ = v___x_2123_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_a_2150_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
v___y_2128_ = v___y_2148_;
v___y_2129_ = v___y_2149_;
v_a_2130_ = v___x_2152_;
goto v___jp_2127_;
}
}
v___jp_2154_:
{
lean_object* v___x_2158_; 
v___x_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2158_, 0, v_a_2157_);
v___y_2128_ = v___y_2155_;
v___y_2129_ = v___y_2156_;
v_a_2130_ = v___x_2158_;
goto v___jp_2127_;
}
v___jp_2159_:
{
if (lean_obj_tag(v___y_2162_) == 0)
{
lean_object* v_a_2163_; 
v_a_2163_ = lean_ctor_get(v___y_2162_, 0);
lean_inc(v_a_2163_);
lean_dec_ref(v___y_2162_);
v___y_2148_ = v___y_2160_;
v___y_2149_ = v___y_2161_;
v_a_2150_ = v_a_2163_;
goto v___jp_2147_;
}
else
{
lean_object* v_a_2164_; 
lean_del_object(v___x_2123_);
v_a_2164_ = lean_ctor_get(v___y_2162_, 0);
lean_inc(v_a_2164_);
lean_dec_ref(v___y_2162_);
v___y_2155_ = v___y_2160_;
v___y_2156_ = v___y_2161_;
v_a_2157_ = v_a_2164_;
goto v___jp_2154_;
}
}
v___jp_2165_:
{
if (v___y_2170_ == 0)
{
lean_object* v___x_2171_; 
lean_dec_ref(v___y_2168_);
lean_inc(v_a_2042_);
lean_inc_ref(v_a_2041_);
lean_inc(v_a_2040_);
lean_inc_ref(v_a_2039_);
v___x_2171_ = lean_apply_6(v_allowFailure_2037_, v_fst_2109_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, lean_box(0));
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; uint8_t v___x_2173_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_a_2172_);
lean_dec_ref(v___x_2171_);
v___x_2173_ = lean_unbox(v_a_2172_);
lean_dec(v_a_2172_);
if (v___x_2173_ == 0)
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
lean_dec(v___y_2166_);
v___x_2174_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1);
v___x_2175_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2174_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
v___y_2160_ = v___y_2167_;
v___y_2161_ = v___y_2169_;
v___y_2162_ = v___x_2175_;
goto v___jp_2159_;
}
else
{
v___y_2148_ = v___y_2167_;
v___y_2149_ = v___y_2169_;
v_a_2150_ = v___y_2166_;
goto v___jp_2147_;
}
}
else
{
lean_object* v_a_2176_; 
lean_dec(v___y_2166_);
lean_del_object(v___x_2123_);
v_a_2176_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_a_2176_);
lean_dec_ref(v___x_2171_);
v___y_2155_ = v___y_2167_;
v___y_2156_ = v___y_2169_;
v_a_2157_ = v_a_2176_;
goto v___jp_2154_;
}
}
else
{
lean_dec(v___y_2166_);
lean_del_object(v___x_2123_);
lean_dec(v_fst_2109_);
lean_dec_ref(v_allowFailure_2037_);
v___y_2155_ = v___y_2167_;
v___y_2156_ = v___y_2169_;
v_a_2157_ = v___y_2168_;
goto v___jp_2154_;
}
}
v___jp_2177_:
{
lean_object* v___x_2181_; double v___x_2182_; double v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2187_; 
v___x_2181_ = lean_io_get_num_heartbeats();
v___x_2182_ = lean_float_of_nat(v___y_2178_);
v___x_2183_ = lean_float_of_nat(v___x_2181_);
v___x_2184_ = lean_box_float(v___x_2182_);
v___x_2185_ = lean_box_float(v___x_2183_);
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 1, v___x_2185_);
lean_ctor_set(v___x_2047_, 0, v___x_2184_);
v___x_2187_ = v___x_2047_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2184_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v___x_2185_);
v___x_2187_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
lean_object* v___x_2188_; uint8_t v___x_2189_; lean_object* v___x_2190_; 
v___x_2188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2188_, 0, v_a_2180_);
lean_ctor_set(v___x_2188_, 1, v___x_2187_);
v___x_2189_ = lean_unbox(v_a_2121_);
lean_dec(v_a_2121_);
v___x_2190_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3(v___x_2119_, v_hasTrace_2050_, v___x_2126_, v_options_2049_, v___x_2189_, v___y_2179_, v___f_2125_, v___x_2188_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
lean_dec_ref(v_options_2049_);
return v___x_2190_;
}
}
v___jp_2192_:
{
lean_object* v___x_2196_; 
v___x_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2196_, 0, v_a_2195_);
v___y_2178_ = v___y_2193_;
v___y_2179_ = v___y_2194_;
v_a_2180_ = v___x_2196_;
goto v___jp_2177_;
}
v___jp_2197_:
{
lean_object* v___x_2201_; 
v___x_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2201_, 0, v_a_2200_);
v___y_2178_ = v___y_2198_;
v___y_2179_ = v___y_2199_;
v_a_2180_ = v___x_2201_;
goto v___jp_2177_;
}
v___jp_2202_:
{
if (lean_obj_tag(v___y_2205_) == 0)
{
lean_object* v_a_2206_; 
v_a_2206_ = lean_ctor_get(v___y_2205_, 0);
lean_inc(v_a_2206_);
lean_dec_ref(v___y_2205_);
v___y_2193_ = v___y_2203_;
v___y_2194_ = v___y_2204_;
v_a_2195_ = v_a_2206_;
goto v___jp_2192_;
}
else
{
lean_object* v_a_2207_; 
v_a_2207_ = lean_ctor_get(v___y_2205_, 0);
lean_inc(v_a_2207_);
lean_dec_ref(v___y_2205_);
v___y_2198_ = v___y_2203_;
v___y_2199_ = v___y_2204_;
v_a_2200_ = v_a_2207_;
goto v___jp_2197_;
}
}
v___jp_2208_:
{
if (v___y_2213_ == 0)
{
lean_object* v___x_2214_; 
lean_dec_ref(v___y_2209_);
lean_inc(v_a_2042_);
lean_inc_ref(v_a_2041_);
lean_inc(v_a_2040_);
lean_inc_ref(v_a_2039_);
v___x_2214_ = lean_apply_6(v_allowFailure_2037_, v_fst_2109_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, lean_box(0));
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_object* v_a_2215_; uint8_t v___x_2216_; 
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2215_);
lean_dec_ref(v___x_2214_);
v___x_2216_ = lean_unbox(v_a_2215_);
lean_dec(v_a_2215_);
if (v___x_2216_ == 0)
{
lean_object* v___x_2217_; lean_object* v___x_2218_; 
lean_dec(v___y_2211_);
v___x_2217_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__0___closed__1);
v___x_2218_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2217_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
v___y_2203_ = v___y_2210_;
v___y_2204_ = v___y_2212_;
v___y_2205_ = v___x_2218_;
goto v___jp_2202_;
}
else
{
v___y_2193_ = v___y_2210_;
v___y_2194_ = v___y_2212_;
v_a_2195_ = v___y_2211_;
goto v___jp_2192_;
}
}
else
{
lean_object* v_a_2219_; 
lean_dec(v___y_2211_);
v_a_2219_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2219_);
lean_dec_ref(v___x_2214_);
v___y_2198_ = v___y_2210_;
v___y_2199_ = v___y_2212_;
v_a_2200_ = v_a_2219_;
goto v___jp_2197_;
}
}
else
{
lean_dec(v___y_2211_);
lean_dec(v_fst_2109_);
lean_dec_ref(v_allowFailure_2037_);
v___y_2198_ = v___y_2210_;
v___y_2199_ = v___y_2212_;
v_a_2200_ = v___y_2209_;
goto v___jp_2197_;
}
}
v___jp_2220_:
{
lean_object* v___x_2221_; lean_object* v_a_2222_; lean_object* v___x_2223_; uint8_t v___x_2224_; 
v___x_2221_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1___redArg(v_a_2042_);
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_a_2222_);
lean_dec_ref(v___x_2221_);
v___x_2223_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2224_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v_options_2049_, v___x_2223_);
if (v___x_2224_ == 0)
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v_cache_2227_; lean_object* v_zetaDeltaFVarIds_2228_; lean_object* v_postponed_2229_; lean_object* v_diag_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2250_; 
lean_del_object(v___x_2047_);
v___x_2225_ = lean_io_mono_nanos_now();
v___x_2226_ = lean_st_ref_take(v_a_2040_);
v_cache_2227_ = lean_ctor_get(v___x_2226_, 1);
v_zetaDeltaFVarIds_2228_ = lean_ctor_get(v___x_2226_, 2);
v_postponed_2229_ = lean_ctor_get(v___x_2226_, 3);
v_diag_2230_ = lean_ctor_get(v___x_2226_, 4);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2250_ == 0)
{
lean_object* v_unused_2251_; 
v_unused_2251_ = lean_ctor_get(v___x_2226_, 0);
lean_dec(v_unused_2251_);
v___x_2232_ = v___x_2226_;
v_isShared_2233_ = v_isSharedCheck_2250_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_diag_2230_);
lean_inc(v_postponed_2229_);
lean_inc(v_zetaDeltaFVarIds_2228_);
lean_inc(v_cache_2227_);
lean_dec(v___x_2226_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2250_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 0, v_snd_2110_);
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_snd_2110_);
lean_ctor_set(v_reuseFailAlloc_2249_, 1, v_cache_2227_);
lean_ctor_set(v_reuseFailAlloc_2249_, 2, v_zetaDeltaFVarIds_2228_);
lean_ctor_set(v_reuseFailAlloc_2249_, 3, v_postponed_2229_);
lean_ctor_set(v_reuseFailAlloc_2249_, 4, v_diag_2230_);
v___x_2235_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
lean_object* v___x_2236_; uint8_t v___x_2237_; lean_object* v___x_2238_; 
v___x_2236_ = lean_st_ref_set(v_a_2040_, v___x_2235_);
v___x_2237_ = lean_unbox(v_snd_2115_);
lean_dec(v_snd_2115_);
lean_inc(v_a_2042_);
lean_inc_ref(v_a_2041_);
lean_inc(v_a_2040_);
lean_inc_ref(v_a_2039_);
v___x_2238_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_2114_, v___x_2237_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_a_2239_);
lean_dec_ref(v___x_2238_);
v___x_2240_ = lean_box(0);
lean_inc(v_a_2042_);
lean_inc_ref(v_a_2041_);
lean_inc(v_a_2040_);
lean_inc_ref(v_a_2039_);
lean_inc(v_fst_2109_);
v___x_2241_ = l_Lean_MVarId_apply(v_fst_2109_, v_a_2239_, v_cfg_2035_, v___x_2240_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_a_2242_; lean_object* v___x_2243_; 
v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
lean_inc(v_a_2242_);
lean_dec_ref(v___x_2241_);
lean_inc(v_a_2042_);
lean_inc_ref(v_a_2041_);
lean_inc(v_a_2040_);
lean_inc_ref(v_a_2039_);
lean_inc(v_a_2242_);
v___x_2243_ = lean_apply_6(v_act_2036_, v_a_2242_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, lean_box(0));
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_object* v_a_2244_; 
lean_dec(v_a_2242_);
lean_dec(v_fst_2109_);
lean_dec_ref(v_allowFailure_2037_);
v_a_2244_ = lean_ctor_get(v___x_2243_, 0);
lean_inc(v_a_2244_);
lean_dec_ref(v___x_2243_);
v___y_2148_ = v___x_2225_;
v___y_2149_ = v_a_2222_;
v_a_2150_ = v_a_2244_;
goto v___jp_2147_;
}
else
{
lean_object* v_a_2245_; uint8_t v___x_2246_; 
v_a_2245_ = lean_ctor_get(v___x_2243_, 0);
lean_inc(v_a_2245_);
lean_dec_ref(v___x_2243_);
v___x_2246_ = l_Lean_Exception_isInterrupt(v_a_2245_);
if (v___x_2246_ == 0)
{
uint8_t v___x_2247_; 
lean_inc(v_a_2245_);
v___x_2247_ = l_Lean_Exception_isRuntime(v_a_2245_);
v___y_2166_ = v_a_2242_;
v___y_2167_ = v___x_2225_;
v___y_2168_ = v_a_2245_;
v___y_2169_ = v_a_2222_;
v___y_2170_ = v___x_2247_;
goto v___jp_2165_;
}
else
{
v___y_2166_ = v_a_2242_;
v___y_2167_ = v___x_2225_;
v___y_2168_ = v_a_2245_;
v___y_2169_ = v_a_2222_;
v___y_2170_ = v___x_2246_;
goto v___jp_2165_;
}
}
}
else
{
lean_dec(v_fst_2109_);
lean_dec_ref(v_allowFailure_2037_);
lean_dec_ref(v_act_2036_);
v___y_2160_ = v___x_2225_;
v___y_2161_ = v_a_2222_;
v___y_2162_ = v___x_2241_;
goto v___jp_2159_;
}
}
else
{
lean_object* v_a_2248_; 
lean_del_object(v___x_2123_);
lean_dec(v_fst_2109_);
lean_dec_ref(v_allowFailure_2037_);
lean_dec_ref(v_act_2036_);
lean_dec_ref(v_cfg_2035_);
v_a_2248_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_a_2248_);
lean_dec_ref(v___x_2238_);
v___y_2155_ = v___x_2225_;
v___y_2156_ = v_a_2222_;
v_a_2157_ = v_a_2248_;
goto v___jp_2154_;
}
}
}
}
else
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v_cache_2254_; lean_object* v_zetaDeltaFVarIds_2255_; lean_object* v_postponed_2256_; lean_object* v_diag_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2277_; 
lean_del_object(v___x_2123_);
lean_del_object(v___x_2117_);
lean_del_object(v___x_2112_);
v___x_2252_ = lean_io_get_num_heartbeats();
v___x_2253_ = lean_st_ref_take(v_a_2040_);
v_cache_2254_ = lean_ctor_get(v___x_2253_, 1);
v_zetaDeltaFVarIds_2255_ = lean_ctor_get(v___x_2253_, 2);
v_postponed_2256_ = lean_ctor_get(v___x_2253_, 3);
v_diag_2257_ = lean_ctor_get(v___x_2253_, 4);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2277_ == 0)
{
lean_object* v_unused_2278_; 
v_unused_2278_ = lean_ctor_get(v___x_2253_, 0);
lean_dec(v_unused_2278_);
v___x_2259_ = v___x_2253_;
v_isShared_2260_ = v_isSharedCheck_2277_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_diag_2257_);
lean_inc(v_postponed_2256_);
lean_inc(v_zetaDeltaFVarIds_2255_);
lean_inc(v_cache_2254_);
lean_dec(v___x_2253_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2277_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 0, v_snd_2110_);
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_snd_2110_);
lean_ctor_set(v_reuseFailAlloc_2276_, 1, v_cache_2254_);
lean_ctor_set(v_reuseFailAlloc_2276_, 2, v_zetaDeltaFVarIds_2255_);
lean_ctor_set(v_reuseFailAlloc_2276_, 3, v_postponed_2256_);
lean_ctor_set(v_reuseFailAlloc_2276_, 4, v_diag_2257_);
v___x_2262_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
lean_object* v___x_2263_; uint8_t v___x_2264_; lean_object* v___x_2265_; 
v___x_2263_ = lean_st_ref_set(v_a_2040_, v___x_2262_);
v___x_2264_ = lean_unbox(v_snd_2115_);
lean_dec(v_snd_2115_);
lean_inc(v_a_2042_);
lean_inc_ref(v_a_2041_);
lean_inc(v_a_2040_);
lean_inc_ref(v_a_2039_);
v___x_2265_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_2114_, v___x_2264_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_a_2266_);
lean_dec_ref(v___x_2265_);
v___x_2267_ = lean_box(0);
lean_inc(v_a_2042_);
lean_inc_ref(v_a_2041_);
lean_inc(v_a_2040_);
lean_inc_ref(v_a_2039_);
lean_inc(v_fst_2109_);
v___x_2268_ = l_Lean_MVarId_apply(v_fst_2109_, v_a_2266_, v_cfg_2035_, v___x_2267_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v_a_2269_; lean_object* v___x_2270_; 
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_a_2269_);
lean_dec_ref(v___x_2268_);
lean_inc(v_a_2042_);
lean_inc_ref(v_a_2041_);
lean_inc(v_a_2040_);
lean_inc_ref(v_a_2039_);
lean_inc(v_a_2269_);
v___x_2270_ = lean_apply_6(v_act_2036_, v_a_2269_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, lean_box(0));
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v_a_2271_; 
lean_dec(v_a_2269_);
lean_dec(v_fst_2109_);
lean_dec_ref(v_allowFailure_2037_);
v_a_2271_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_a_2271_);
lean_dec_ref(v___x_2270_);
v___y_2193_ = v___x_2252_;
v___y_2194_ = v_a_2222_;
v_a_2195_ = v_a_2271_;
goto v___jp_2192_;
}
else
{
lean_object* v_a_2272_; uint8_t v___x_2273_; 
v_a_2272_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_a_2272_);
lean_dec_ref(v___x_2270_);
v___x_2273_ = l_Lean_Exception_isInterrupt(v_a_2272_);
if (v___x_2273_ == 0)
{
uint8_t v___x_2274_; 
lean_inc(v_a_2272_);
v___x_2274_ = l_Lean_Exception_isRuntime(v_a_2272_);
v___y_2209_ = v_a_2272_;
v___y_2210_ = v___x_2252_;
v___y_2211_ = v_a_2269_;
v___y_2212_ = v_a_2222_;
v___y_2213_ = v___x_2274_;
goto v___jp_2208_;
}
else
{
v___y_2209_ = v_a_2272_;
v___y_2210_ = v___x_2252_;
v___y_2211_ = v_a_2269_;
v___y_2212_ = v_a_2222_;
v___y_2213_ = v___x_2273_;
goto v___jp_2208_;
}
}
}
else
{
lean_dec(v_fst_2109_);
lean_dec_ref(v_allowFailure_2037_);
lean_dec_ref(v_act_2036_);
v___y_2203_ = v___x_2252_;
v___y_2204_ = v_a_2222_;
v___y_2205_ = v___x_2268_;
goto v___jp_2202_;
}
}
else
{
lean_object* v_a_2275_; 
lean_dec(v_fst_2109_);
lean_dec_ref(v_allowFailure_2037_);
lean_dec_ref(v_act_2036_);
lean_dec_ref(v_cfg_2035_);
v_a_2275_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_a_2275_);
lean_dec_ref(v___x_2265_);
v___y_2198_ = v___x_2252_;
v___y_2199_ = v_a_2222_;
v_a_2200_ = v_a_2275_;
goto v___jp_2197_;
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___boxed(lean_object* v_cfg_2340_, lean_object* v_act_2341_, lean_object* v_allowFailure_2342_, lean_object* v_cand_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(v_cfg_2340_, v_act_2341_, v_allowFailure_2342_, v_cand_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__5(lean_object* v_00_u03b1_2350_, lean_object* v_x_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_){
_start:
{
lean_object* v___x_2357_; 
v___x_2357_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__5___redArg(v_x_2351_);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2358_, lean_object* v_x_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__5(v_00_u03b1_2358_, v_x_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(lean_object* v_act_2368_, lean_object* v_a_2369_, uint8_t v_collectAll_2370_, lean_object* v_as_2371_, size_t v_sz_2372_, size_t v_i_2373_, lean_object* v_b_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
lean_object* v_a_2381_; uint8_t v___x_2385_; 
v___x_2385_ = lean_usize_dec_lt(v_i_2373_, v_sz_2372_);
if (v___x_2385_ == 0)
{
lean_object* v___x_2386_; 
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec_ref(v_act_2368_);
v___x_2386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2386_, 0, v_b_2374_);
return v___x_2386_;
}
else
{
lean_object* v_snd_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2460_; 
v_snd_2387_ = lean_ctor_get(v_b_2374_, 1);
v_isSharedCheck_2460_ = !lean_is_exclusive(v_b_2374_);
if (v_isSharedCheck_2460_ == 0)
{
lean_object* v_unused_2461_; 
v_unused_2461_ = lean_ctor_get(v_b_2374_, 0);
lean_dec(v_unused_2461_);
v___x_2389_ = v_b_2374_;
v_isShared_2390_ = v_isSharedCheck_2460_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_snd_2387_);
lean_dec(v_b_2374_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2460_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2391_; lean_object* v_a_2392_; lean_object* v___x_2393_; 
v___x_2391_ = lean_box(0);
v_a_2392_ = lean_array_uget_borrowed(v_as_2371_, v_i_2373_);
lean_inc_ref(v_act_2368_);
lean_inc(v___y_2378_);
lean_inc_ref(v___y_2377_);
lean_inc(v___y_2376_);
lean_inc_ref(v___y_2375_);
lean_inc(v_a_2392_);
v___x_2393_ = lean_apply_6(v_act_2368_, v_a_2392_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, lean_box(0));
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2423_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2396_ = v___x_2393_;
v_isShared_2397_ = v_isSharedCheck_2423_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2393_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2423_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
uint8_t v___y_2416_; uint8_t v___x_2422_; 
v___x_2422_ = l_List_isEmpty___redArg(v_a_2394_);
if (v___x_2422_ == 0)
{
v___y_2416_ = v___x_2422_;
goto v___jp_2415_;
}
else
{
if (v_collectAll_2370_ == 0)
{
v___y_2416_ = v___x_2422_;
goto v___jp_2415_;
}
else
{
lean_del_object(v___x_2396_);
goto v___jp_2398_;
}
}
v___jp_2398_:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2399_ = lean_st_ref_get(v___y_2376_);
v___x_2400_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2369_, v___y_2376_, v___y_2378_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v_mctx_2401_; lean_object* v___x_2403_; 
lean_dec_ref(v___x_2400_);
v_mctx_2401_ = lean_ctor_get(v___x_2399_, 0);
lean_inc_ref(v_mctx_2401_);
lean_dec(v___x_2399_);
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 1, v_mctx_2401_);
lean_ctor_set(v___x_2389_, 0, v_a_2394_);
v___x_2403_ = v___x_2389_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2394_);
lean_ctor_set(v_reuseFailAlloc_2406_, 1, v_mctx_2401_);
v___x_2403_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2404_ = lean_array_push(v_snd_2387_, v___x_2403_);
v___x_2405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2391_);
lean_ctor_set(v___x_2405_, 1, v___x_2404_);
v_a_2381_ = v___x_2405_;
goto v___jp_2380_;
}
}
else
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2414_; 
lean_dec(v___x_2399_);
lean_dec(v_a_2394_);
lean_del_object(v___x_2389_);
lean_dec(v_snd_2387_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec_ref(v_act_2368_);
v_a_2407_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2409_ = v___x_2400_;
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2400_);
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
v___jp_2415_:
{
if (v___y_2416_ == 0)
{
lean_del_object(v___x_2396_);
goto v___jp_2398_;
}
else
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2420_; 
lean_dec(v_a_2394_);
lean_del_object(v___x_2389_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec_ref(v_act_2368_);
v___x_2417_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0___closed__0));
v___x_2418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2417_);
lean_ctor_set(v___x_2418_, 1, v_snd_2387_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 0, v___x_2418_);
v___x_2420_ = v___x_2396_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v___x_2418_);
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
else
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2459_; 
v_a_2424_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2426_ = v___x_2393_;
v_isShared_2427_ = v_isSharedCheck_2459_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2393_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2459_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
uint8_t v___y_2429_; uint8_t v___x_2457_; 
v___x_2457_ = l_Lean_Exception_isInterrupt(v_a_2424_);
if (v___x_2457_ == 0)
{
uint8_t v___x_2458_; 
lean_inc(v_a_2424_);
v___x_2458_ = l_Lean_Exception_isRuntime(v_a_2424_);
v___y_2429_ = v___x_2458_;
goto v___jp_2428_;
}
else
{
v___y_2429_ = v___x_2457_;
goto v___jp_2428_;
}
v___jp_2428_:
{
if (v___y_2429_ == 0)
{
lean_object* v___x_2430_; 
lean_del_object(v___x_2426_);
v___x_2430_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2369_, v___y_2376_, v___y_2378_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2444_; 
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2444_ == 0)
{
lean_object* v_unused_2445_; 
v_unused_2445_ = lean_ctor_get(v___x_2430_, 0);
lean_dec(v_unused_2445_);
v___x_2432_ = v___x_2430_;
v_isShared_2433_ = v_isSharedCheck_2444_;
goto v_resetjp_2431_;
}
else
{
lean_dec(v___x_2430_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2444_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
uint8_t v___x_2434_; 
v___x_2434_ = l_Lean_Meta_LibrarySearch_isAbortSpeculation(v_a_2424_);
lean_dec(v_a_2424_);
if (v___x_2434_ == 0)
{
lean_object* v___x_2436_; 
lean_del_object(v___x_2432_);
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 0, v___x_2391_);
v___x_2436_ = v___x_2389_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v___x_2391_);
lean_ctor_set(v_reuseFailAlloc_2437_, 1, v_snd_2387_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
v_a_2381_ = v___x_2436_;
goto v___jp_2380_;
}
}
else
{
lean_object* v___x_2439_; 
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec_ref(v_act_2368_);
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 0, v___x_2391_);
v___x_2439_ = v___x_2389_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2391_);
lean_ctor_set(v_reuseFailAlloc_2443_, 1, v_snd_2387_);
v___x_2439_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
lean_object* v___x_2441_; 
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 0, v___x_2439_);
v___x_2441_ = v___x_2432_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v___x_2439_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
}
}
else
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
lean_dec(v_a_2424_);
lean_del_object(v___x_2389_);
lean_dec(v_snd_2387_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec_ref(v_act_2368_);
v_a_2446_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2448_ = v___x_2430_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2430_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2451_; 
if (v_isShared_2449_ == 0)
{
v___x_2451_ = v___x_2448_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_a_2446_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
else
{
lean_object* v___x_2455_; 
lean_del_object(v___x_2389_);
lean_dec(v_snd_2387_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec_ref(v_act_2368_);
if (v_isShared_2427_ == 0)
{
v___x_2455_ = v___x_2426_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_a_2424_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
}
}
}
v___jp_2380_:
{
size_t v___x_2382_; size_t v___x_2383_; 
v___x_2382_ = ((size_t)1ULL);
v___x_2383_ = lean_usize_add(v_i_2373_, v___x_2382_);
v_i_2373_ = v___x_2383_;
v_b_2374_ = v_a_2381_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0___boxed(lean_object* v_act_2462_, lean_object* v_a_2463_, lean_object* v_collectAll_2464_, lean_object* v_as_2465_, lean_object* v_sz_2466_, lean_object* v_i_2467_, lean_object* v_b_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
uint8_t v_collectAll_boxed_2474_; size_t v_sz_boxed_2475_; size_t v_i_boxed_2476_; lean_object* v_res_2477_; 
v_collectAll_boxed_2474_ = lean_unbox(v_collectAll_2464_);
v_sz_boxed_2475_ = lean_unbox_usize(v_sz_2466_);
lean_dec(v_sz_2466_);
v_i_boxed_2476_ = lean_unbox_usize(v_i_2467_);
lean_dec(v_i_2467_);
v_res_2477_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(v_act_2462_, v_a_2463_, v_collectAll_boxed_2474_, v_as_2465_, v_sz_boxed_2475_, v_i_boxed_2476_, v_b_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_);
lean_dec_ref(v_as_2465_);
lean_dec_ref(v_a_2463_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryOnEach(lean_object* v_act_2483_, lean_object* v_candidates_2484_, uint8_t v_collectAll_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_){
_start:
{
lean_object* v___x_2491_; 
v___x_2491_ = l_Lean_Meta_saveState___redArg(v_a_2487_, v_a_2489_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v_a_2492_; lean_object* v___x_2493_; size_t v_sz_2494_; size_t v___x_2495_; lean_object* v___x_2496_; 
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
lean_inc(v_a_2492_);
lean_dec_ref(v___x_2491_);
v___x_2493_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryOnEach___closed__1));
v_sz_2494_ = lean_array_size(v_candidates_2484_);
v___x_2495_ = ((size_t)0ULL);
v___x_2496_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(v_act_2483_, v_a_2492_, v_collectAll_2485_, v_candidates_2484_, v_sz_2494_, v___x_2495_, v___x_2493_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_);
lean_dec(v_a_2492_);
if (lean_obj_tag(v___x_2496_) == 0)
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2511_; 
v_a_2497_ = lean_ctor_get(v___x_2496_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2499_ = v___x_2496_;
v_isShared_2500_ = v_isSharedCheck_2511_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2496_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2511_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v_fst_2501_; 
v_fst_2501_ = lean_ctor_get(v_a_2497_, 0);
if (lean_obj_tag(v_fst_2501_) == 0)
{
lean_object* v_snd_2502_; lean_object* v___x_2503_; lean_object* v___x_2505_; 
v_snd_2502_ = lean_ctor_get(v_a_2497_, 1);
lean_inc(v_snd_2502_);
lean_dec(v_a_2497_);
v___x_2503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2503_, 0, v_snd_2502_);
if (v_isShared_2500_ == 0)
{
lean_ctor_set(v___x_2499_, 0, v___x_2503_);
v___x_2505_ = v___x_2499_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v___x_2503_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
else
{
lean_object* v_val_2507_; lean_object* v___x_2509_; 
lean_inc_ref(v_fst_2501_);
lean_dec(v_a_2497_);
v_val_2507_ = lean_ctor_get(v_fst_2501_, 0);
lean_inc(v_val_2507_);
lean_dec_ref(v_fst_2501_);
if (v_isShared_2500_ == 0)
{
lean_ctor_set(v___x_2499_, 0, v_val_2507_);
v___x_2509_ = v___x_2499_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_val_2507_);
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
else
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2519_; 
v_a_2512_ = lean_ctor_get(v___x_2496_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2514_ = v___x_2496_;
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2496_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2517_; 
if (v_isShared_2515_ == 0)
{
v___x_2517_ = v___x_2514_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_a_2512_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
}
else
{
lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2527_; 
lean_dec(v_a_2489_);
lean_dec_ref(v_a_2488_);
lean_dec(v_a_2487_);
lean_dec_ref(v_a_2486_);
lean_dec_ref(v_act_2483_);
v_a_2520_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2522_ = v___x_2491_;
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2491_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2525_; 
if (v_isShared_2523_ == 0)
{
v___x_2525_ = v___x_2522_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_a_2520_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryOnEach___boxed(lean_object* v_act_2528_, lean_object* v_candidates_2529_, lean_object* v_collectAll_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_){
_start:
{
uint8_t v_collectAll_boxed_2536_; lean_object* v_res_2537_; 
v_collectAll_boxed_2536_ = lean_unbox(v_collectAll_2530_);
v_res_2537_ = l_Lean_Meta_LibrarySearch_tryOnEach(v_act_2528_, v_candidates_2529_, v_collectAll_boxed_2536_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_);
lean_dec_ref(v_candidates_2529_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg(){
_start:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2539_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0, &l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0_once, _init_l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0);
v___x_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2539_);
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg___boxed(lean_object* v___y_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg();
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0(lean_object* v_00_u03b1_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
lean_object* v___x_2549_; 
v___x_2549_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg();
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___boxed(lean_object* v_00_u03b1_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0(v_00_u03b1_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(lean_object* v_category_2557_, lean_object* v_opts_2558_, lean_object* v_act_2559_, lean_object* v_decl_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2566_ = lean_apply_4(v_act_2559_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
v___x_2567_ = l_Lean_profileitIOUnsafe___redArg(v_category_2557_, v_opts_2558_, v___x_2566_, v_decl_2560_);
return v___x_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg___boxed(lean_object* v_category_2568_, lean_object* v_opts_2569_, lean_object* v_act_2570_, lean_object* v_decl_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v_category_2568_, v_opts_2569_, v_act_2570_, v_decl_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
lean_dec_ref(v_opts_2569_);
lean_dec_ref(v_category_2568_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3(lean_object* v_00_u03b1_2578_, lean_object* v_category_2579_, lean_object* v_opts_2580_, lean_object* v_act_2581_, lean_object* v_decl_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
lean_object* v___x_2588_; 
v___x_2588_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v_category_2579_, v_opts_2580_, v_act_2581_, v_decl_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___boxed(lean_object* v_00_u03b1_2589_, lean_object* v_category_2590_, lean_object* v_opts_2591_, lean_object* v_act_2592_, lean_object* v_decl_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
lean_object* v_res_2599_; 
v_res_2599_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3(v_00_u03b1_2589_, v_category_2590_, v_opts_2591_, v_act_2592_, v_decl_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
lean_dec_ref(v_opts_2591_);
lean_dec_ref(v_category_2590_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0(lean_object* v_a_2600_, lean_object* v___x_2601_, lean_object* v_tactic_2602_, lean_object* v_allowFailure_2603_, lean_object* v_cand_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v___x_2610_; 
lean_inc(v___y_2608_);
lean_inc_ref(v___y_2607_);
lean_inc(v___y_2606_);
lean_inc_ref(v___y_2605_);
v___x_2610_ = lean_apply_5(v_a_2600_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, lean_box(0));
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; uint8_t v___x_2612_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_a_2611_);
lean_dec_ref(v___x_2610_);
v___x_2612_ = lean_unbox(v_a_2611_);
lean_dec(v_a_2611_);
if (v___x_2612_ == 0)
{
lean_object* v___x_2613_; 
v___x_2613_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(v___x_2601_, v_tactic_2602_, v_allowFailure_2603_, v_cand_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
return v___x_2613_;
}
else
{
lean_object* v___x_2614_; lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec_ref(v_cand_2604_);
lean_dec_ref(v_allowFailure_2603_);
lean_dec_ref(v_tactic_2602_);
lean_dec_ref(v___x_2601_);
v___x_2614_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg();
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2614_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2614_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2615_);
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
else
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2630_; 
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec_ref(v_cand_2604_);
lean_dec_ref(v_allowFailure_2603_);
lean_dec_ref(v_tactic_2602_);
lean_dec_ref(v___x_2601_);
v_a_2623_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2625_ = v___x_2610_;
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2610_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2628_; 
if (v_isShared_2626_ == 0)
{
v___x_2628_ = v___x_2625_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_a_2623_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed(lean_object* v_a_2631_, lean_object* v___x_2632_, lean_object* v_tactic_2633_, lean_object* v_allowFailure_2634_, lean_object* v_cand_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0(v_a_2631_, v___x_2632_, v_tactic_2633_, v_allowFailure_2634_, v_cand_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
return v_res_2641_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(lean_object* v_as_2642_, size_t v_i_2643_, size_t v_stop_2644_){
_start:
{
uint8_t v___x_2645_; 
v___x_2645_ = lean_usize_dec_eq(v_i_2643_, v_stop_2644_);
if (v___x_2645_ == 0)
{
lean_object* v___x_2646_; lean_object* v_fst_2647_; uint8_t v___x_2648_; 
v___x_2646_ = lean_array_uget_borrowed(v_as_2642_, v_i_2643_);
v_fst_2647_ = lean_ctor_get(v___x_2646_, 0);
v___x_2648_ = l_List_isEmpty___redArg(v_fst_2647_);
if (v___x_2648_ == 0)
{
size_t v___x_2649_; size_t v___x_2650_; 
v___x_2649_ = ((size_t)1ULL);
v___x_2650_ = lean_usize_add(v_i_2643_, v___x_2649_);
v_i_2643_ = v___x_2650_;
goto _start;
}
else
{
return v___x_2648_;
}
}
else
{
uint8_t v___x_2652_; 
v___x_2652_ = 0;
return v___x_2652_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2___boxed(lean_object* v_as_2653_, lean_object* v_i_2654_, lean_object* v_stop_2655_){
_start:
{
size_t v_i_boxed_2656_; size_t v_stop_boxed_2657_; uint8_t v_res_2658_; lean_object* v_r_2659_; 
v_i_boxed_2656_ = lean_unbox_usize(v_i_2654_);
lean_dec(v_i_2654_);
v_stop_boxed_2657_ = lean_unbox_usize(v_stop_2655_);
lean_dec(v_stop_2655_);
v_res_2658_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_as_2653_, v_i_boxed_2656_, v_stop_boxed_2657_);
lean_dec_ref(v_as_2653_);
v_r_2659_ = lean_box(v_res_2658_);
return v_r_2659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(lean_object* v_goal_2660_, lean_object* v___x_2661_, size_t v_sz_2662_, size_t v_i_2663_, lean_object* v_bs_2664_){
_start:
{
uint8_t v___x_2665_; 
v___x_2665_ = lean_usize_dec_lt(v_i_2663_, v_sz_2662_);
if (v___x_2665_ == 0)
{
lean_dec_ref(v___x_2661_);
lean_dec(v_goal_2660_);
return v_bs_2664_;
}
else
{
lean_object* v_v_2666_; lean_object* v___x_2667_; lean_object* v_bs_x27_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; size_t v___x_2671_; size_t v___x_2672_; lean_object* v___x_2673_; 
v_v_2666_ = lean_array_uget(v_bs_2664_, v_i_2663_);
v___x_2667_ = lean_unsigned_to_nat(0u);
v_bs_x27_2668_ = lean_array_uset(v_bs_2664_, v_i_2663_, v___x_2667_);
lean_inc_ref(v___x_2661_);
lean_inc(v_goal_2660_);
v___x_2669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2669_, 0, v_goal_2660_);
lean_ctor_set(v___x_2669_, 1, v___x_2661_);
v___x_2670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2669_);
lean_ctor_set(v___x_2670_, 1, v_v_2666_);
v___x_2671_ = ((size_t)1ULL);
v___x_2672_ = lean_usize_add(v_i_2663_, v___x_2671_);
v___x_2673_ = lean_array_uset(v_bs_x27_2668_, v_i_2663_, v___x_2670_);
v_i_2663_ = v___x_2672_;
v_bs_2664_ = v___x_2673_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1___boxed(lean_object* v_goal_2675_, lean_object* v___x_2676_, lean_object* v_sz_2677_, lean_object* v_i_2678_, lean_object* v_bs_2679_){
_start:
{
size_t v_sz_boxed_2680_; size_t v_i_boxed_2681_; lean_object* v_res_2682_; 
v_sz_boxed_2680_ = lean_unbox_usize(v_sz_2677_);
lean_dec(v_sz_2677_);
v_i_boxed_2681_ = lean_unbox_usize(v_i_2678_);
lean_dec(v_i_2678_);
v_res_2682_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2675_, v___x_2676_, v_sz_boxed_2680_, v_i_boxed_2681_, v_bs_2679_);
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1(lean_object* v_leavePercentHeartbeats_2684_, lean_object* v_goal_2685_, lean_object* v___x_2686_, lean_object* v_tactic_2687_, lean_object* v_allowFailure_2688_, uint8_t v_collectAll_2689_, uint8_t v_includeStar_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_){
_start:
{
lean_object* v___x_2699_; 
v___x_2699_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercentHeartbeats_2684_, v___y_2693_);
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_object* v_a_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
v_a_2700_ = lean_ctor_get(v___x_2699_, 0);
lean_inc(v_a_2700_);
lean_dec_ref(v___x_2699_);
v___x_2701_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___closed__0));
lean_inc(v___y_2694_);
lean_inc_ref(v___y_2693_);
lean_inc(v___y_2692_);
lean_inc_ref(v___y_2691_);
lean_inc(v_goal_2685_);
v___x_2702_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v___x_2701_, v_goal_2685_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_);
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_object* v_a_2703_; lean_object* v___f_2704_; lean_object* v___x_2705_; 
v_a_2703_ = lean_ctor_get(v___x_2702_, 0);
lean_inc(v_a_2703_);
lean_dec_ref(v___x_2702_);
v___f_2704_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2704_, 0, v_a_2700_);
lean_closure_set(v___f_2704_, 1, v___x_2686_);
lean_closure_set(v___f_2704_, 2, v_tactic_2687_);
lean_closure_set(v___f_2704_, 3, v_allowFailure_2688_);
lean_inc(v___y_2694_);
lean_inc_ref(v___y_2693_);
lean_inc(v___y_2692_);
lean_inc_ref(v___y_2691_);
lean_inc_ref(v___f_2704_);
v___x_2705_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2704_, v_a_2703_, v_collectAll_2689_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_);
lean_dec(v_a_2703_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v_a_2706_; 
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_a_2706_);
if (lean_obj_tag(v_a_2706_) == 0)
{
lean_dec_ref(v___x_2705_);
lean_dec_ref(v___f_2704_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v_goal_2685_);
goto v___jp_2696_;
}
else
{
lean_object* v_val_2707_; lean_object* v___x_2756_; lean_object* v___x_2757_; uint8_t v___x_2758_; 
v_val_2707_ = lean_ctor_get(v_a_2706_, 0);
v___x_2756_ = lean_unsigned_to_nat(0u);
v___x_2757_ = lean_array_get_size(v_val_2707_);
v___x_2758_ = lean_nat_dec_lt(v___x_2756_, v___x_2757_);
if (v___x_2758_ == 0)
{
goto v___jp_2752_;
}
else
{
if (v___x_2758_ == 0)
{
goto v___jp_2752_;
}
else
{
size_t v___x_2759_; size_t v___x_2760_; uint8_t v___x_2761_; 
v___x_2759_ = ((size_t)0ULL);
v___x_2760_ = lean_usize_of_nat(v___x_2757_);
v___x_2761_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_val_2707_, v___x_2759_, v___x_2760_);
if (v___x_2761_ == 0)
{
goto v___jp_2752_;
}
else
{
lean_dec_ref(v_a_2706_);
lean_dec_ref(v___f_2704_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v_goal_2685_);
return v___x_2705_;
}
}
}
v___jp_2708_:
{
if (v_includeStar_2690_ == 0)
{
lean_dec_ref(v_a_2706_);
lean_dec_ref(v___f_2704_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v_goal_2685_);
return v___x_2705_;
}
else
{
lean_object* v___x_2709_; 
lean_dec_ref(v___x_2705_);
lean_inc(v___y_2694_);
lean_inc_ref(v___y_2693_);
lean_inc(v___y_2692_);
lean_inc_ref(v___y_2691_);
v___x_2709_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2743_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2712_ = v___x_2709_;
v_isShared_2713_ = v_isSharedCheck_2743_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2709_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2743_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; uint8_t v___x_2716_; 
v___x_2714_ = lean_array_get_size(v_a_2710_);
v___x_2715_ = lean_unsigned_to_nat(0u);
v___x_2716_ = lean_nat_dec_eq(v___x_2714_, v___x_2715_);
if (v___x_2716_ == 0)
{
lean_object* v___x_2717_; lean_object* v_mctx_2718_; size_t v_sz_2719_; size_t v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
lean_inc(v_val_2707_);
lean_del_object(v___x_2712_);
lean_dec_ref(v_a_2706_);
v___x_2717_ = lean_st_ref_get(v___y_2692_);
v_mctx_2718_ = lean_ctor_get(v___x_2717_, 0);
lean_inc_ref(v_mctx_2718_);
lean_dec(v___x_2717_);
v_sz_2719_ = lean_array_size(v_a_2710_);
v___x_2720_ = ((size_t)0ULL);
v___x_2721_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2685_, v_mctx_2718_, v_sz_2719_, v___x_2720_, v_a_2710_);
v___x_2722_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2704_, v___x_2721_, v_collectAll_2689_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_);
lean_dec_ref(v___x_2721_);
if (lean_obj_tag(v___x_2722_) == 0)
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2739_; 
v_a_2723_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2725_ = v___x_2722_;
v_isShared_2726_ = v_isSharedCheck_2739_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2722_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2739_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
if (lean_obj_tag(v_a_2723_) == 0)
{
lean_del_object(v___x_2725_);
lean_dec(v_val_2707_);
goto v___jp_2696_;
}
else
{
lean_object* v_val_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2738_; 
v_val_2727_ = lean_ctor_get(v_a_2723_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v_a_2723_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2729_ = v_a_2723_;
v_isShared_2730_ = v_isSharedCheck_2738_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_val_2727_);
lean_dec(v_a_2723_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2738_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2731_; lean_object* v___x_2733_; 
v___x_2731_ = l_Array_append___redArg(v_val_2707_, v_val_2727_);
lean_dec(v_val_2727_);
if (v_isShared_2730_ == 0)
{
lean_ctor_set(v___x_2729_, 0, v___x_2731_);
v___x_2733_ = v___x_2729_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v___x_2731_);
v___x_2733_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
lean_object* v___x_2735_; 
if (v_isShared_2726_ == 0)
{
lean_ctor_set(v___x_2725_, 0, v___x_2733_);
v___x_2735_ = v___x_2725_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2733_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
}
}
}
else
{
lean_dec(v_val_2707_);
return v___x_2722_;
}
}
else
{
lean_object* v___x_2741_; 
lean_dec(v_a_2710_);
lean_dec_ref(v___f_2704_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v_goal_2685_);
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 0, v_a_2706_);
v___x_2741_ = v___x_2712_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_a_2706_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
}
else
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2751_; 
lean_dec_ref(v_a_2706_);
lean_dec_ref(v___f_2704_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v_goal_2685_);
v_a_2744_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2746_ = v___x_2709_;
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2709_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2749_; 
if (v_isShared_2747_ == 0)
{
v___x_2749_ = v___x_2746_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2744_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
}
v___jp_2752_:
{
if (v_collectAll_2689_ == 0)
{
lean_object* v___x_2753_; lean_object* v___x_2754_; uint8_t v___x_2755_; 
v___x_2753_ = lean_array_get_size(v_val_2707_);
v___x_2754_ = lean_unsigned_to_nat(0u);
v___x_2755_ = lean_nat_dec_eq(v___x_2753_, v___x_2754_);
if (v___x_2755_ == 0)
{
lean_dec_ref(v_a_2706_);
lean_dec_ref(v___f_2704_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v_goal_2685_);
return v___x_2705_;
}
else
{
goto v___jp_2708_;
}
}
else
{
goto v___jp_2708_;
}
}
}
}
else
{
lean_dec_ref(v___f_2704_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v_goal_2685_);
return v___x_2705_;
}
}
else
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
lean_dec(v_a_2700_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec_ref(v_allowFailure_2688_);
lean_dec_ref(v_tactic_2687_);
lean_dec_ref(v___x_2686_);
lean_dec(v_goal_2685_);
v_a_2762_ = lean_ctor_get(v___x_2702_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v___x_2702_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2702_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_a_2762_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
}
else
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2777_; 
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec_ref(v_allowFailure_2688_);
lean_dec_ref(v_tactic_2687_);
lean_dec_ref(v___x_2686_);
lean_dec(v_goal_2685_);
v_a_2770_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2772_ = v___x_2699_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2699_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2775_; 
if (v_isShared_2773_ == 0)
{
v___x_2775_ = v___x_2772_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2770_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
v___jp_2696_:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2697_ = lean_box(0);
v___x_2698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2697_);
return v___x_2698_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed(lean_object* v_leavePercentHeartbeats_2778_, lean_object* v_goal_2779_, lean_object* v___x_2780_, lean_object* v_tactic_2781_, lean_object* v_allowFailure_2782_, lean_object* v_collectAll_2783_, lean_object* v_includeStar_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_){
_start:
{
uint8_t v_collectAll_boxed_2790_; uint8_t v_includeStar_boxed_2791_; lean_object* v_res_2792_; 
v_collectAll_boxed_2790_ = lean_unbox(v_collectAll_2783_);
v_includeStar_boxed_2791_ = lean_unbox(v_includeStar_2784_);
v_res_2792_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1(v_leavePercentHeartbeats_2778_, v_goal_2779_, v___x_2780_, v_tactic_2781_, v_allowFailure_2782_, v_collectAll_boxed_2790_, v_includeStar_boxed_2791_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
lean_dec(v_leavePercentHeartbeats_2778_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2(lean_object* v_goal_2793_, lean_object* v_x_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
lean_object* v___x_2800_; 
v___x_2800_ = l_Lean_MVarId_getType(v_goal_2793_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2809_; 
v_a_2801_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2803_ = v___x_2800_;
v_isShared_2804_ = v_isSharedCheck_2809_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2800_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2809_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2805_; lean_object* v___x_2807_; 
v___x_2805_ = l_Lean_MessageData_ofExpr(v_a_2801_);
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 0, v___x_2805_);
v___x_2807_ = v___x_2803_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v___x_2805_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
else
{
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2817_; 
v_a_2810_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2812_ = v___x_2800_;
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2800_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2815_; 
if (v_isShared_2813_ == 0)
{
v___x_2815_ = v___x_2812_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2810_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2___boxed(lean_object* v_goal_2818_, lean_object* v_x_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2(v_goal_2818_, v_x_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec_ref(v_x_2819_);
return v_res_2825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4(lean_object* v_leavePercentHeartbeats_2826_, lean_object* v_goal_2827_, lean_object* v___x_2828_, lean_object* v_tactic_2829_, lean_object* v_allowFailure_2830_, uint8_t v_collectAll_2831_, uint8_t v_includeStar_2832_, uint8_t v___x_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v___x_2842_; 
v___x_2842_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercentHeartbeats_2826_, v___y_2836_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_object* v_a_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
v_a_2843_ = lean_ctor_get(v___x_2842_, 0);
lean_inc(v_a_2843_);
lean_dec_ref(v___x_2842_);
v___x_2844_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___closed__0));
lean_inc(v___y_2837_);
lean_inc_ref(v___y_2836_);
lean_inc(v___y_2835_);
lean_inc_ref(v___y_2834_);
lean_inc(v_goal_2827_);
v___x_2845_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v___x_2844_, v_goal_2827_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_object* v_a_2846_; lean_object* v___f_2847_; lean_object* v___x_2848_; 
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
lean_inc(v_a_2846_);
lean_dec_ref(v___x_2845_);
v___f_2847_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2847_, 0, v_a_2843_);
lean_closure_set(v___f_2847_, 1, v___x_2828_);
lean_closure_set(v___f_2847_, 2, v_tactic_2829_);
lean_closure_set(v___f_2847_, 3, v_allowFailure_2830_);
lean_inc(v___y_2837_);
lean_inc_ref(v___y_2836_);
lean_inc(v___y_2835_);
lean_inc_ref(v___y_2834_);
lean_inc_ref(v___f_2847_);
v___x_2848_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2847_, v_a_2846_, v_collectAll_2831_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
lean_dec(v_a_2846_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v_a_2849_; 
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
lean_inc(v_a_2849_);
if (lean_obj_tag(v_a_2849_) == 0)
{
lean_dec_ref(v___x_2848_);
lean_dec_ref(v___f_2847_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v_goal_2827_);
goto v___jp_2839_;
}
else
{
lean_object* v_val_2850_; uint8_t v___y_2896_; lean_object* v___x_2900_; lean_object* v___x_2901_; uint8_t v___x_2902_; 
v_val_2850_ = lean_ctor_get(v_a_2849_, 0);
v___x_2900_ = lean_unsigned_to_nat(0u);
v___x_2901_ = lean_array_get_size(v_val_2850_);
v___x_2902_ = lean_nat_dec_lt(v___x_2900_, v___x_2901_);
if (v___x_2902_ == 0)
{
v___y_2896_ = v___x_2833_;
goto v___jp_2895_;
}
else
{
if (v___x_2902_ == 0)
{
v___y_2896_ = v___x_2833_;
goto v___jp_2895_;
}
else
{
size_t v___x_2903_; size_t v___x_2904_; uint8_t v___x_2905_; 
v___x_2903_ = ((size_t)0ULL);
v___x_2904_ = lean_usize_of_nat(v___x_2901_);
v___x_2905_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_val_2850_, v___x_2903_, v___x_2904_);
v___y_2896_ = v___x_2905_;
goto v___jp_2895_;
}
}
v___jp_2851_:
{
if (v_includeStar_2832_ == 0)
{
lean_dec_ref(v_a_2849_);
lean_dec_ref(v___f_2847_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v_goal_2827_);
return v___x_2848_;
}
else
{
lean_object* v___x_2852_; 
lean_dec_ref(v___x_2848_);
lean_inc(v___y_2837_);
lean_inc_ref(v___y_2836_);
lean_inc(v___y_2835_);
lean_inc_ref(v___y_2834_);
v___x_2852_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2886_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2855_ = v___x_2852_;
v_isShared_2856_ = v_isSharedCheck_2886_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2852_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2886_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; uint8_t v___x_2859_; 
v___x_2857_ = lean_array_get_size(v_a_2853_);
v___x_2858_ = lean_unsigned_to_nat(0u);
v___x_2859_ = lean_nat_dec_eq(v___x_2857_, v___x_2858_);
if (v___x_2859_ == 0)
{
lean_object* v___x_2860_; lean_object* v_mctx_2861_; size_t v_sz_2862_; size_t v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
lean_inc(v_val_2850_);
lean_del_object(v___x_2855_);
lean_dec_ref(v_a_2849_);
v___x_2860_ = lean_st_ref_get(v___y_2835_);
v_mctx_2861_ = lean_ctor_get(v___x_2860_, 0);
lean_inc_ref(v_mctx_2861_);
lean_dec(v___x_2860_);
v_sz_2862_ = lean_array_size(v_a_2853_);
v___x_2863_ = ((size_t)0ULL);
v___x_2864_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2827_, v_mctx_2861_, v_sz_2862_, v___x_2863_, v_a_2853_);
v___x_2865_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2847_, v___x_2864_, v_collectAll_2831_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
lean_dec_ref(v___x_2864_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2882_; 
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2868_ = v___x_2865_;
v_isShared_2869_ = v_isSharedCheck_2882_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2865_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2882_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
if (lean_obj_tag(v_a_2866_) == 0)
{
lean_del_object(v___x_2868_);
lean_dec(v_val_2850_);
goto v___jp_2839_;
}
else
{
lean_object* v_val_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2881_; 
v_val_2870_ = lean_ctor_get(v_a_2866_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v_a_2866_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2872_ = v_a_2866_;
v_isShared_2873_ = v_isSharedCheck_2881_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_val_2870_);
lean_dec(v_a_2866_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2881_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2874_; lean_object* v___x_2876_; 
v___x_2874_ = l_Array_append___redArg(v_val_2850_, v_val_2870_);
lean_dec(v_val_2870_);
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 0, v___x_2874_);
v___x_2876_ = v___x_2872_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v___x_2874_);
v___x_2876_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
lean_object* v___x_2878_; 
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 0, v___x_2876_);
v___x_2878_ = v___x_2868_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2876_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
}
}
}
else
{
lean_dec(v_val_2850_);
return v___x_2865_;
}
}
else
{
lean_object* v___x_2884_; 
lean_dec(v_a_2853_);
lean_dec_ref(v___f_2847_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v_goal_2827_);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 0, v_a_2849_);
v___x_2884_ = v___x_2855_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2849_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
}
else
{
lean_object* v_a_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2894_; 
lean_dec_ref(v_a_2849_);
lean_dec_ref(v___f_2847_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v_goal_2827_);
v_a_2887_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2889_ = v___x_2852_;
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_a_2887_);
lean_dec(v___x_2852_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2892_; 
if (v_isShared_2890_ == 0)
{
v___x_2892_ = v___x_2889_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_a_2887_);
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
}
v___jp_2895_:
{
if (v___y_2896_ == 0)
{
if (v_collectAll_2831_ == 0)
{
lean_object* v___x_2897_; lean_object* v___x_2898_; uint8_t v___x_2899_; 
v___x_2897_ = lean_array_get_size(v_val_2850_);
v___x_2898_ = lean_unsigned_to_nat(0u);
v___x_2899_ = lean_nat_dec_eq(v___x_2897_, v___x_2898_);
if (v___x_2899_ == 0)
{
lean_dec_ref(v_a_2849_);
lean_dec_ref(v___f_2847_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v_goal_2827_);
return v___x_2848_;
}
else
{
goto v___jp_2851_;
}
}
else
{
goto v___jp_2851_;
}
}
else
{
lean_dec_ref(v_a_2849_);
lean_dec_ref(v___f_2847_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v_goal_2827_);
return v___x_2848_;
}
}
}
}
else
{
lean_dec_ref(v___f_2847_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v_goal_2827_);
return v___x_2848_;
}
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
lean_dec(v_a_2843_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec_ref(v_allowFailure_2830_);
lean_dec_ref(v_tactic_2829_);
lean_dec_ref(v___x_2828_);
lean_dec(v_goal_2827_);
v_a_2906_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2845_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2845_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
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
return v___x_2911_;
}
}
}
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec_ref(v_allowFailure_2830_);
lean_dec_ref(v_tactic_2829_);
lean_dec_ref(v___x_2828_);
lean_dec(v_goal_2827_);
v_a_2914_ = lean_ctor_get(v___x_2842_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2842_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2842_);
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
v___jp_2839_:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2840_ = lean_box(0);
v___x_2841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2840_);
return v___x_2841_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4___boxed(lean_object* v_leavePercentHeartbeats_2922_, lean_object* v_goal_2923_, lean_object* v___x_2924_, lean_object* v_tactic_2925_, lean_object* v_allowFailure_2926_, lean_object* v_collectAll_2927_, lean_object* v_includeStar_2928_, lean_object* v___x_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_){
_start:
{
uint8_t v_collectAll_boxed_2935_; uint8_t v_includeStar_boxed_2936_; uint8_t v___x_14667__boxed_2937_; lean_object* v_res_2938_; 
v_collectAll_boxed_2935_ = lean_unbox(v_collectAll_2927_);
v_includeStar_boxed_2936_ = lean_unbox(v_includeStar_2928_);
v___x_14667__boxed_2937_ = lean_unbox(v___x_2929_);
v_res_2938_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4(v_leavePercentHeartbeats_2922_, v_goal_2923_, v___x_2924_, v_tactic_2925_, v_allowFailure_2926_, v_collectAll_boxed_2935_, v_includeStar_boxed_2936_, v___x_14667__boxed_2937_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
lean_dec(v_leavePercentHeartbeats_2922_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__5(lean_object* v_leavePercentHeartbeats_2939_, lean_object* v_goal_2940_, lean_object* v___x_2941_, lean_object* v_tactic_2942_, lean_object* v_allowFailure_2943_, uint8_t v_collectAll_2944_, uint8_t v_includeStar_2945_, uint8_t v___x_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v___x_2955_; 
v___x_2955_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercentHeartbeats_2939_, v___y_2949_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
lean_inc(v_a_2956_);
lean_dec_ref(v___x_2955_);
v___x_2957_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___closed__0));
lean_inc(v___y_2950_);
lean_inc_ref(v___y_2949_);
lean_inc(v___y_2948_);
lean_inc_ref(v___y_2947_);
lean_inc(v_goal_2940_);
v___x_2958_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v___x_2957_, v_goal_2940_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; lean_object* v___f_2960_; lean_object* v___x_2961_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
lean_inc(v_a_2959_);
lean_dec_ref(v___x_2958_);
v___f_2960_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2960_, 0, v_a_2956_);
lean_closure_set(v___f_2960_, 1, v___x_2941_);
lean_closure_set(v___f_2960_, 2, v_tactic_2942_);
lean_closure_set(v___f_2960_, 3, v_allowFailure_2943_);
lean_inc(v___y_2950_);
lean_inc_ref(v___y_2949_);
lean_inc(v___y_2948_);
lean_inc_ref(v___y_2947_);
lean_inc_ref(v___f_2960_);
v___x_2961_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2960_, v_a_2959_, v_collectAll_2944_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
lean_dec(v_a_2959_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_a_2962_; 
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
lean_inc(v_a_2962_);
if (lean_obj_tag(v_a_2962_) == 0)
{
lean_dec_ref(v___x_2961_);
lean_dec_ref(v___f_2960_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v_goal_2940_);
goto v___jp_2952_;
}
else
{
lean_object* v_val_2963_; lean_object* v___x_3013_; lean_object* v___x_3014_; uint8_t v___x_3015_; 
v_val_2963_ = lean_ctor_get(v_a_2962_, 0);
v___x_3013_ = lean_unsigned_to_nat(0u);
v___x_3014_ = lean_array_get_size(v_val_2963_);
v___x_3015_ = lean_nat_dec_lt(v___x_3013_, v___x_3014_);
if (v___x_3015_ == 0)
{
goto v___jp_3009_;
}
else
{
if (v___x_3015_ == 0)
{
goto v___jp_3009_;
}
else
{
size_t v___x_3016_; size_t v___x_3017_; uint8_t v___x_3018_; 
v___x_3016_ = ((size_t)0ULL);
v___x_3017_ = lean_usize_of_nat(v___x_3014_);
v___x_3018_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_val_2963_, v___x_3016_, v___x_3017_);
if (v___x_3018_ == 0)
{
goto v___jp_3009_;
}
else
{
if (v___x_2946_ == 0)
{
goto v___jp_3008_;
}
else
{
lean_dec_ref(v_a_2962_);
lean_dec_ref(v___f_2960_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v_goal_2940_);
return v___x_2961_;
}
}
}
}
v___jp_2964_:
{
lean_object* v___x_2965_; 
lean_inc(v___y_2950_);
lean_inc_ref(v___y_2949_);
lean_inc(v___y_2948_);
lean_inc_ref(v___y_2947_);
v___x_2965_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2999_; 
v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2968_ = v___x_2965_;
v_isShared_2969_ = v_isSharedCheck_2999_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_dec(v___x_2965_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2999_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; uint8_t v___x_2972_; 
v___x_2970_ = lean_array_get_size(v_a_2966_);
v___x_2971_ = lean_unsigned_to_nat(0u);
v___x_2972_ = lean_nat_dec_eq(v___x_2970_, v___x_2971_);
if (v___x_2972_ == 0)
{
lean_object* v___x_2973_; lean_object* v_mctx_2974_; size_t v_sz_2975_; size_t v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
lean_inc(v_val_2963_);
lean_del_object(v___x_2968_);
lean_dec_ref(v_a_2962_);
v___x_2973_ = lean_st_ref_get(v___y_2948_);
v_mctx_2974_ = lean_ctor_get(v___x_2973_, 0);
lean_inc_ref(v_mctx_2974_);
lean_dec(v___x_2973_);
v_sz_2975_ = lean_array_size(v_a_2966_);
v___x_2976_ = ((size_t)0ULL);
v___x_2977_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2940_, v_mctx_2974_, v_sz_2975_, v___x_2976_, v_a_2966_);
v___x_2978_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2960_, v___x_2977_, v_collectAll_2944_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
lean_dec_ref(v___x_2977_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2995_; 
v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2981_ = v___x_2978_;
v_isShared_2982_ = v_isSharedCheck_2995_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2978_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2995_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
if (lean_obj_tag(v_a_2979_) == 0)
{
lean_del_object(v___x_2981_);
lean_dec(v_val_2963_);
goto v___jp_2952_;
}
else
{
lean_object* v_val_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2994_; 
v_val_2983_ = lean_ctor_get(v_a_2979_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v_a_2979_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2985_ = v_a_2979_;
v_isShared_2986_ = v_isSharedCheck_2994_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_val_2983_);
lean_dec(v_a_2979_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2994_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2987_; lean_object* v___x_2989_; 
v___x_2987_ = l_Array_append___redArg(v_val_2963_, v_val_2983_);
lean_dec(v_val_2983_);
if (v_isShared_2986_ == 0)
{
lean_ctor_set(v___x_2985_, 0, v___x_2987_);
v___x_2989_ = v___x_2985_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v___x_2987_);
v___x_2989_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
lean_object* v___x_2991_; 
if (v_isShared_2982_ == 0)
{
lean_ctor_set(v___x_2981_, 0, v___x_2989_);
v___x_2991_ = v___x_2981_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v___x_2989_);
v___x_2991_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
return v___x_2991_;
}
}
}
}
}
}
else
{
lean_dec(v_val_2963_);
return v___x_2978_;
}
}
else
{
lean_object* v___x_2997_; 
lean_dec(v_a_2966_);
lean_dec_ref(v___f_2960_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v_goal_2940_);
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 0, v_a_2962_);
v___x_2997_ = v___x_2968_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_a_2962_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
}
else
{
lean_object* v_a_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3007_; 
lean_dec_ref(v_a_2962_);
lean_dec_ref(v___f_2960_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v_goal_2940_);
v_a_3000_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_3002_ = v___x_2965_;
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_a_3000_);
lean_dec(v___x_2965_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3005_; 
if (v_isShared_3003_ == 0)
{
v___x_3005_ = v___x_3002_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_a_3000_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
}
}
v___jp_3008_:
{
if (v_includeStar_2945_ == 0)
{
if (v___x_2946_ == 0)
{
lean_dec_ref(v___x_2961_);
goto v___jp_2964_;
}
else
{
lean_dec_ref(v_a_2962_);
lean_dec_ref(v___f_2960_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v_goal_2940_);
return v___x_2961_;
}
}
else
{
lean_dec_ref(v___x_2961_);
goto v___jp_2964_;
}
}
v___jp_3009_:
{
if (v_collectAll_2944_ == 0)
{
if (v___x_2946_ == 0)
{
goto v___jp_3008_;
}
else
{
lean_object* v___x_3010_; lean_object* v___x_3011_; uint8_t v___x_3012_; 
v___x_3010_ = lean_array_get_size(v_val_2963_);
v___x_3011_ = lean_unsigned_to_nat(0u);
v___x_3012_ = lean_nat_dec_eq(v___x_3010_, v___x_3011_);
if (v___x_3012_ == 0)
{
lean_dec_ref(v_a_2962_);
lean_dec_ref(v___f_2960_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v_goal_2940_);
return v___x_2961_;
}
else
{
goto v___jp_3008_;
}
}
}
else
{
goto v___jp_3008_;
}
}
}
}
else
{
lean_dec_ref(v___f_2960_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v_goal_2940_);
return v___x_2961_;
}
}
else
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
lean_dec(v_a_2956_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec_ref(v_allowFailure_2943_);
lean_dec_ref(v_tactic_2942_);
lean_dec_ref(v___x_2941_);
lean_dec(v_goal_2940_);
v_a_3019_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_2958_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_2958_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3022_ == 0)
{
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3019_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
else
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec_ref(v_allowFailure_2943_);
lean_dec_ref(v_tactic_2942_);
lean_dec_ref(v___x_2941_);
lean_dec(v_goal_2940_);
v_a_3027_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_2955_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_2955_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3032_; 
if (v_isShared_3030_ == 0)
{
v___x_3032_ = v___x_3029_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3027_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
v___jp_2952_:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2953_ = lean_box(0);
v___x_2954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2953_);
return v___x_2954_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__5___boxed(lean_object* v_leavePercentHeartbeats_3035_, lean_object* v_goal_3036_, lean_object* v___x_3037_, lean_object* v_tactic_3038_, lean_object* v_allowFailure_3039_, lean_object* v_collectAll_3040_, lean_object* v_includeStar_3041_, lean_object* v___x_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_){
_start:
{
uint8_t v_collectAll_boxed_3048_; uint8_t v_includeStar_boxed_3049_; uint8_t v___x_14856__boxed_3050_; lean_object* v_res_3051_; 
v_collectAll_boxed_3048_ = lean_unbox(v_collectAll_3040_);
v_includeStar_boxed_3049_ = lean_unbox(v_includeStar_3041_);
v___x_14856__boxed_3050_ = lean_unbox(v___x_3042_);
v_res_3051_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__5(v_leavePercentHeartbeats_3035_, v_goal_3036_, v___x_3037_, v_tactic_3038_, v_allowFailure_3039_, v_collectAll_boxed_3048_, v_includeStar_boxed_3049_, v___x_14856__boxed_3050_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
lean_dec(v_leavePercentHeartbeats_3035_);
return v_res_3051_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(lean_object* v_e_3052_){
_start:
{
if (lean_obj_tag(v_e_3052_) == 0)
{
uint8_t v___x_3053_; 
v___x_3053_ = 2;
return v___x_3053_;
}
else
{
lean_object* v_a_3054_; 
v_a_3054_ = lean_ctor_get(v_e_3052_, 0);
if (lean_obj_tag(v_a_3054_) == 0)
{
uint8_t v___x_3055_; 
v___x_3055_ = 1;
return v___x_3055_;
}
else
{
uint8_t v___x_3056_; 
v___x_3056_ = 0;
return v___x_3056_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4___boxed(lean_object* v_e_3057_){
_start:
{
uint8_t v_res_3058_; lean_object* v_r_3059_; 
v_res_3058_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(v_e_3057_);
lean_dec_ref(v_e_3057_);
v_r_3059_ = lean_box(v_res_3058_);
return v_r_3059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(lean_object* v_cls_3060_, uint8_t v_collapsed_3061_, lean_object* v_tag_3062_, lean_object* v_opts_3063_, uint8_t v_clsEnabled_3064_, lean_object* v_oldTraces_3065_, lean_object* v_msg_3066_, lean_object* v_resStartStop_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_){
_start:
{
lean_object* v_fst_3073_; lean_object* v_snd_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3172_; 
v_fst_3073_ = lean_ctor_get(v_resStartStop_3067_, 0);
v_snd_3074_ = lean_ctor_get(v_resStartStop_3067_, 1);
v_isSharedCheck_3172_ = !lean_is_exclusive(v_resStartStop_3067_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3076_ = v_resStartStop_3067_;
v_isShared_3077_ = v_isSharedCheck_3172_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_snd_3074_);
lean_inc(v_fst_3073_);
lean_dec(v_resStartStop_3067_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3172_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v_data_3081_; lean_object* v_fst_3092_; lean_object* v_snd_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3171_; 
v_fst_3092_ = lean_ctor_get(v_snd_3074_, 0);
v_snd_3093_ = lean_ctor_get(v_snd_3074_, 1);
v_isSharedCheck_3171_ = !lean_is_exclusive(v_snd_3074_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3095_ = v_snd_3074_;
v_isShared_3096_ = v_isSharedCheck_3171_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_snd_3093_);
lean_inc(v_fst_3092_);
lean_dec(v_snd_3074_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3171_;
goto v_resetjp_3094_;
}
v___jp_3078_:
{
lean_object* v___x_3082_; 
v___x_3082_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__4(v_oldTraces_3065_, v_data_3081_, v___y_3080_, v___y_3079_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_);
lean_dec(v___y_3071_);
lean_dec(v___y_3069_);
lean_dec_ref(v___y_3068_);
if (lean_obj_tag(v___x_3082_) == 0)
{
lean_object* v___x_3083_; 
lean_dec_ref(v___x_3082_);
v___x_3083_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__5___redArg(v_fst_3073_);
return v___x_3083_;
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_dec(v_fst_3073_);
v_a_3084_ = lean_ctor_get(v___x_3082_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_3082_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3082_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
v_resetjp_3094_:
{
lean_object* v___x_3097_; uint8_t v___x_3098_; lean_object* v___y_3100_; lean_object* v_a_3101_; uint8_t v___y_3125_; double v___y_3156_; 
v___x_3097_ = l_Lean_trace_profiler;
v___x_3098_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v_opts_3063_, v___x_3097_);
if (v___x_3098_ == 0)
{
v___y_3125_ = v___x_3098_;
goto v___jp_3124_;
}
else
{
lean_object* v___x_3161_; uint8_t v___x_3162_; 
v___x_3161_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3162_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v_opts_3063_, v___x_3161_);
if (v___x_3162_ == 0)
{
lean_object* v___x_3163_; lean_object* v___x_3164_; double v___x_3165_; double v___x_3166_; double v___x_3167_; 
v___x_3163_ = l_Lean_trace_profiler_threshold;
v___x_3164_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__6(v_opts_3063_, v___x_3163_);
v___x_3165_ = lean_float_of_nat(v___x_3164_);
v___x_3166_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3___closed__3);
v___x_3167_ = lean_float_div(v___x_3165_, v___x_3166_);
v___y_3156_ = v___x_3167_;
goto v___jp_3155_;
}
else
{
lean_object* v___x_3168_; lean_object* v___x_3169_; double v___x_3170_; 
v___x_3168_ = l_Lean_trace_profiler_threshold;
v___x_3169_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__6(v_opts_3063_, v___x_3168_);
v___x_3170_ = lean_float_of_nat(v___x_3169_);
v___y_3156_ = v___x_3170_;
goto v___jp_3155_;
}
}
v___jp_3099_:
{
uint8_t v_result_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3107_; 
v_result_3102_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(v_fst_3073_);
v___x_3103_ = l_Lean_TraceResult_toEmoji(v_result_3102_);
v___x_3104_ = l_Lean_stringToMessageData(v___x_3103_);
v___x_3105_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3);
if (v_isShared_3096_ == 0)
{
lean_ctor_set_tag(v___x_3095_, 7);
lean_ctor_set(v___x_3095_, 1, v___x_3105_);
lean_ctor_set(v___x_3095_, 0, v___x_3104_);
v___x_3107_ = v___x_3095_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v___x_3104_);
lean_ctor_set(v_reuseFailAlloc_3118_, 1, v___x_3105_);
v___x_3107_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
lean_object* v_m_3109_; 
if (v_isShared_3077_ == 0)
{
lean_ctor_set_tag(v___x_3076_, 7);
lean_ctor_set(v___x_3076_, 1, v_a_3101_);
lean_ctor_set(v___x_3076_, 0, v___x_3107_);
v_m_3109_ = v___x_3076_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v___x_3107_);
lean_ctor_set(v_reuseFailAlloc_3117_, 1, v_a_3101_);
v_m_3109_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
lean_object* v___x_3110_; lean_object* v___x_3111_; double v___x_3112_; lean_object* v_data_3113_; 
v___x_3110_ = lean_box(v_result_3102_);
v___x_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3110_);
v___x_3112_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3___closed__0);
lean_inc_ref(v_tag_3062_);
lean_inc_ref(v___x_3111_);
lean_inc(v_cls_3060_);
v_data_3113_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3113_, 0, v_cls_3060_);
lean_ctor_set(v_data_3113_, 1, v___x_3111_);
lean_ctor_set(v_data_3113_, 2, v_tag_3062_);
lean_ctor_set_float(v_data_3113_, sizeof(void*)*3, v___x_3112_);
lean_ctor_set_float(v_data_3113_, sizeof(void*)*3 + 8, v___x_3112_);
lean_ctor_set_uint8(v_data_3113_, sizeof(void*)*3 + 16, v_collapsed_3061_);
if (v___x_3098_ == 0)
{
lean_dec_ref(v___x_3111_);
lean_dec(v_snd_3093_);
lean_dec(v_fst_3092_);
lean_dec_ref(v_tag_3062_);
lean_dec(v_cls_3060_);
v___y_3079_ = v_m_3109_;
v___y_3080_ = v___y_3100_;
v_data_3081_ = v_data_3113_;
goto v___jp_3078_;
}
else
{
lean_object* v_data_3114_; double v___x_3115_; double v___x_3116_; 
lean_dec_ref(v_data_3113_);
v_data_3114_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3114_, 0, v_cls_3060_);
lean_ctor_set(v_data_3114_, 1, v___x_3111_);
lean_ctor_set(v_data_3114_, 2, v_tag_3062_);
v___x_3115_ = lean_unbox_float(v_fst_3092_);
lean_dec(v_fst_3092_);
lean_ctor_set_float(v_data_3114_, sizeof(void*)*3, v___x_3115_);
v___x_3116_ = lean_unbox_float(v_snd_3093_);
lean_dec(v_snd_3093_);
lean_ctor_set_float(v_data_3114_, sizeof(void*)*3 + 8, v___x_3116_);
lean_ctor_set_uint8(v_data_3114_, sizeof(void*)*3 + 16, v_collapsed_3061_);
v___y_3079_ = v_m_3109_;
v___y_3080_ = v___y_3100_;
v_data_3081_ = v_data_3114_;
goto v___jp_3078_;
}
}
}
}
v___jp_3119_:
{
lean_object* v_ref_3120_; lean_object* v___x_3121_; 
v_ref_3120_ = lean_ctor_get(v___y_3070_, 5);
lean_inc(v___y_3071_);
lean_inc_ref(v___y_3070_);
lean_inc(v___y_3069_);
lean_inc_ref(v___y_3068_);
lean_inc(v_fst_3073_);
v___x_3121_ = lean_apply_6(v_msg_3066_, v_fst_3073_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, lean_box(0));
if (lean_obj_tag(v___x_3121_) == 0)
{
lean_object* v_a_3122_; 
v_a_3122_ = lean_ctor_get(v___x_3121_, 0);
lean_inc(v_a_3122_);
lean_dec_ref(v___x_3121_);
lean_inc(v_ref_3120_);
v___y_3100_ = v_ref_3120_;
v_a_3101_ = v_a_3122_;
goto v___jp_3099_;
}
else
{
lean_object* v___x_3123_; 
lean_dec_ref(v___x_3121_);
v___x_3123_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3___closed__2);
lean_inc(v_ref_3120_);
v___y_3100_ = v_ref_3120_;
v_a_3101_ = v___x_3123_;
goto v___jp_3099_;
}
}
v___jp_3124_:
{
if (v_clsEnabled_3064_ == 0)
{
if (v___y_3125_ == 0)
{
lean_object* v___x_3126_; lean_object* v_traceState_3127_; lean_object* v_env_3128_; lean_object* v_nextMacroScope_3129_; lean_object* v_ngen_3130_; lean_object* v_auxDeclNGen_3131_; lean_object* v_cache_3132_; lean_object* v_messages_3133_; lean_object* v_infoState_3134_; lean_object* v_snapshotTasks_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3154_; 
lean_del_object(v___x_3095_);
lean_dec(v_snd_3093_);
lean_dec(v_fst_3092_);
lean_del_object(v___x_3076_);
lean_dec_ref(v___y_3070_);
lean_dec(v___y_3069_);
lean_dec_ref(v___y_3068_);
lean_dec_ref(v_msg_3066_);
lean_dec_ref(v_tag_3062_);
lean_dec(v_cls_3060_);
v___x_3126_ = lean_st_ref_take(v___y_3071_);
v_traceState_3127_ = lean_ctor_get(v___x_3126_, 4);
v_env_3128_ = lean_ctor_get(v___x_3126_, 0);
v_nextMacroScope_3129_ = lean_ctor_get(v___x_3126_, 1);
v_ngen_3130_ = lean_ctor_get(v___x_3126_, 2);
v_auxDeclNGen_3131_ = lean_ctor_get(v___x_3126_, 3);
v_cache_3132_ = lean_ctor_get(v___x_3126_, 5);
v_messages_3133_ = lean_ctor_get(v___x_3126_, 6);
v_infoState_3134_ = lean_ctor_get(v___x_3126_, 7);
v_snapshotTasks_3135_ = lean_ctor_get(v___x_3126_, 8);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3137_ = v___x_3126_;
v_isShared_3138_ = v_isSharedCheck_3154_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_snapshotTasks_3135_);
lean_inc(v_infoState_3134_);
lean_inc(v_messages_3133_);
lean_inc(v_cache_3132_);
lean_inc(v_traceState_3127_);
lean_inc(v_auxDeclNGen_3131_);
lean_inc(v_ngen_3130_);
lean_inc(v_nextMacroScope_3129_);
lean_inc(v_env_3128_);
lean_dec(v___x_3126_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3154_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
uint64_t v_tid_3139_; lean_object* v_traces_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3153_; 
v_tid_3139_ = lean_ctor_get_uint64(v_traceState_3127_, sizeof(void*)*1);
v_traces_3140_ = lean_ctor_get(v_traceState_3127_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v_traceState_3127_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3142_ = v_traceState_3127_;
v_isShared_3143_ = v_isSharedCheck_3153_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_traces_3140_);
lean_dec(v_traceState_3127_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3153_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3144_; lean_object* v___x_3146_; 
v___x_3144_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3065_, v_traces_3140_);
lean_dec_ref(v_traces_3140_);
if (v_isShared_3143_ == 0)
{
lean_ctor_set(v___x_3142_, 0, v___x_3144_);
v___x_3146_ = v___x_3142_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v___x_3144_);
lean_ctor_set_uint64(v_reuseFailAlloc_3152_, sizeof(void*)*1, v_tid_3139_);
v___x_3146_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
lean_object* v___x_3148_; 
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 4, v___x_3146_);
v___x_3148_ = v___x_3137_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_env_3128_);
lean_ctor_set(v_reuseFailAlloc_3151_, 1, v_nextMacroScope_3129_);
lean_ctor_set(v_reuseFailAlloc_3151_, 2, v_ngen_3130_);
lean_ctor_set(v_reuseFailAlloc_3151_, 3, v_auxDeclNGen_3131_);
lean_ctor_set(v_reuseFailAlloc_3151_, 4, v___x_3146_);
lean_ctor_set(v_reuseFailAlloc_3151_, 5, v_cache_3132_);
lean_ctor_set(v_reuseFailAlloc_3151_, 6, v_messages_3133_);
lean_ctor_set(v_reuseFailAlloc_3151_, 7, v_infoState_3134_);
lean_ctor_set(v_reuseFailAlloc_3151_, 8, v_snapshotTasks_3135_);
v___x_3148_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; 
v___x_3149_ = lean_st_ref_set(v___y_3071_, v___x_3148_);
lean_dec(v___y_3071_);
v___x_3150_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__3_spec__5___redArg(v_fst_3073_);
return v___x_3150_;
}
}
}
}
}
else
{
goto v___jp_3119_;
}
}
else
{
goto v___jp_3119_;
}
}
v___jp_3155_:
{
double v___x_3157_; double v___x_3158_; double v___x_3159_; uint8_t v___x_3160_; 
v___x_3157_ = lean_unbox_float(v_snd_3093_);
v___x_3158_ = lean_unbox_float(v_fst_3092_);
v___x_3159_ = lean_float_sub(v___x_3157_, v___x_3158_);
v___x_3160_ = lean_float_decLt(v___y_3156_, v___x_3159_);
v___y_3125_ = v___x_3160_;
goto v___jp_3124_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4___boxed(lean_object* v_cls_3173_, lean_object* v_collapsed_3174_, lean_object* v_tag_3175_, lean_object* v_opts_3176_, lean_object* v_clsEnabled_3177_, lean_object* v_oldTraces_3178_, lean_object* v_msg_3179_, lean_object* v_resStartStop_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_){
_start:
{
uint8_t v_collapsed_boxed_3186_; uint8_t v_clsEnabled_boxed_3187_; lean_object* v_res_3188_; 
v_collapsed_boxed_3186_ = lean_unbox(v_collapsed_3174_);
v_clsEnabled_boxed_3187_ = lean_unbox(v_clsEnabled_3177_);
v_res_3188_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v_cls_3173_, v_collapsed_boxed_3186_, v_tag_3175_, v_opts_3176_, v_clsEnabled_boxed_3187_, v_oldTraces_3178_, v_msg_3179_, v_resStartStop_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
lean_dec_ref(v_opts_3176_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(lean_object* v_goal_3192_, lean_object* v_tactic_3193_, lean_object* v_allowFailure_3194_, lean_object* v_leavePercentHeartbeats_3195_, uint8_t v_includeStar_3196_, uint8_t v_collectAll_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_){
_start:
{
lean_object* v_options_3203_; uint8_t v_hasTrace_3204_; lean_object* v___x_3205_; 
v_options_3203_ = lean_ctor_get(v_a_3200_, 2);
lean_inc_ref(v_options_3203_);
v_hasTrace_3204_ = lean_ctor_get_uint8(v_options_3203_, sizeof(void*)*1);
v___x_3205_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
if (v_hasTrace_3204_ == 0)
{
lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___f_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
v___x_3206_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___closed__0));
v___x_3207_ = lean_box(v_collectAll_3197_);
v___x_3208_ = lean_box(v_includeStar_3196_);
v___f_3209_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed), 12, 7);
lean_closure_set(v___f_3209_, 0, v_leavePercentHeartbeats_3195_);
lean_closure_set(v___f_3209_, 1, v_goal_3192_);
lean_closure_set(v___f_3209_, 2, v___x_3206_);
lean_closure_set(v___f_3209_, 3, v_tactic_3193_);
lean_closure_set(v___f_3209_, 4, v_allowFailure_3194_);
lean_closure_set(v___f_3209_, 5, v___x_3207_);
lean_closure_set(v___f_3209_, 6, v___x_3208_);
v___x_3210_ = lean_box(0);
v___x_3211_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_3205_, v_options_3203_, v___f_3209_, v___x_3210_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
lean_dec_ref(v_options_3203_);
return v___x_3211_;
}
else
{
lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v_a_3214_; lean_object* v___f_3215_; lean_object* v___x_3216_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v_a_3220_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v_a_3236_; uint8_t v___x_3301_; 
v___x_3212_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_3213_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v___x_3212_, v_a_3200_);
v_a_3214_ = lean_ctor_get(v___x_3213_, 0);
lean_inc(v_a_3214_);
lean_dec_ref(v___x_3213_);
lean_inc(v_goal_3192_);
v___f_3215_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2___boxed), 7, 1);
lean_closure_set(v___f_3215_, 0, v_goal_3192_);
v___x_3216_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__4));
v___x_3301_ = lean_unbox(v_a_3214_);
if (v___x_3301_ == 0)
{
lean_object* v___x_3302_; uint8_t v___x_3303_; 
v___x_3302_ = l_Lean_trace_profiler;
v___x_3303_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v_options_3203_, v___x_3302_);
if (v___x_3303_ == 0)
{
uint8_t v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___f_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
lean_dec_ref(v___f_3215_);
lean_dec(v_a_3214_);
v___x_3304_ = 0;
v___x_3305_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3305_, 0, v___x_3304_);
lean_ctor_set_uint8(v___x_3305_, 1, v_hasTrace_3204_);
lean_ctor_set_uint8(v___x_3305_, 2, v_hasTrace_3204_);
lean_ctor_set_uint8(v___x_3305_, 3, v_hasTrace_3204_);
v___x_3306_ = lean_box(v_collectAll_3197_);
v___x_3307_ = lean_box(v_includeStar_3196_);
v___x_3308_ = lean_box(v___x_3303_);
v___f_3309_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4___boxed), 13, 8);
lean_closure_set(v___f_3309_, 0, v_leavePercentHeartbeats_3195_);
lean_closure_set(v___f_3309_, 1, v_goal_3192_);
lean_closure_set(v___f_3309_, 2, v___x_3305_);
lean_closure_set(v___f_3309_, 3, v_tactic_3193_);
lean_closure_set(v___f_3309_, 4, v_allowFailure_3194_);
lean_closure_set(v___f_3309_, 5, v___x_3306_);
lean_closure_set(v___f_3309_, 6, v___x_3307_);
lean_closure_set(v___f_3309_, 7, v___x_3308_);
v___x_3310_ = lean_box(0);
v___x_3311_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_3205_, v_options_3203_, v___f_3309_, v___x_3310_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
lean_dec_ref(v_options_3203_);
return v___x_3311_;
}
else
{
goto v___jp_3246_;
}
}
else
{
goto v___jp_3246_;
}
v___jp_3217_:
{
lean_object* v___x_3221_; double v___x_3222_; double v___x_3223_; double v___x_3224_; double v___x_3225_; double v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; uint8_t v___x_3231_; lean_object* v___x_3232_; 
v___x_3221_ = lean_io_mono_nanos_now();
v___x_3222_ = lean_float_of_nat(v___y_3219_);
v___x_3223_ = lean_float_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__0, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__0_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__0);
v___x_3224_ = lean_float_div(v___x_3222_, v___x_3223_);
v___x_3225_ = lean_float_of_nat(v___x_3221_);
v___x_3226_ = lean_float_div(v___x_3225_, v___x_3223_);
v___x_3227_ = lean_box_float(v___x_3224_);
v___x_3228_ = lean_box_float(v___x_3226_);
v___x_3229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3229_, 0, v___x_3227_);
lean_ctor_set(v___x_3229_, 1, v___x_3228_);
v___x_3230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3230_, 0, v_a_3220_);
lean_ctor_set(v___x_3230_, 1, v___x_3229_);
v___x_3231_ = lean_unbox(v_a_3214_);
lean_dec(v_a_3214_);
v___x_3232_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v___x_3212_, v_hasTrace_3204_, v___x_3216_, v_options_3203_, v___x_3231_, v___y_3218_, v___f_3215_, v___x_3230_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
lean_dec_ref(v_options_3203_);
return v___x_3232_;
}
v___jp_3233_:
{
lean_object* v___x_3237_; double v___x_3238_; double v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; uint8_t v___x_3244_; lean_object* v___x_3245_; 
v___x_3237_ = lean_io_get_num_heartbeats();
v___x_3238_ = lean_float_of_nat(v___y_3235_);
v___x_3239_ = lean_float_of_nat(v___x_3237_);
v___x_3240_ = lean_box_float(v___x_3238_);
v___x_3241_ = lean_box_float(v___x_3239_);
v___x_3242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3240_);
lean_ctor_set(v___x_3242_, 1, v___x_3241_);
v___x_3243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3243_, 0, v_a_3236_);
lean_ctor_set(v___x_3243_, 1, v___x_3242_);
v___x_3244_ = lean_unbox(v_a_3214_);
lean_dec(v_a_3214_);
v___x_3245_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v___x_3212_, v_hasTrace_3204_, v___x_3216_, v_options_3203_, v___x_3244_, v___y_3234_, v___f_3215_, v___x_3243_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
lean_dec_ref(v_options_3203_);
return v___x_3245_;
}
v___jp_3246_:
{
lean_object* v___x_3247_; lean_object* v_a_3248_; lean_object* v___x_3249_; uint8_t v___x_3250_; 
v___x_3247_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1___redArg(v_a_3201_);
v_a_3248_ = lean_ctor_get(v___x_3247_, 0);
lean_inc(v_a_3248_);
lean_dec_ref(v___x_3247_);
v___x_3249_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3250_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v_options_3203_, v___x_3249_);
if (v___x_3250_ == 0)
{
lean_object* v___x_3251_; uint8_t v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___f_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3251_ = lean_io_mono_nanos_now();
v___x_3252_ = 0;
v___x_3253_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3253_, 0, v___x_3252_);
lean_ctor_set_uint8(v___x_3253_, 1, v_hasTrace_3204_);
lean_ctor_set_uint8(v___x_3253_, 2, v_hasTrace_3204_);
lean_ctor_set_uint8(v___x_3253_, 3, v_hasTrace_3204_);
v___x_3254_ = lean_box(v_collectAll_3197_);
v___x_3255_ = lean_box(v_includeStar_3196_);
v___x_3256_ = lean_box(v___x_3250_);
v___f_3257_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__4___boxed), 13, 8);
lean_closure_set(v___f_3257_, 0, v_leavePercentHeartbeats_3195_);
lean_closure_set(v___f_3257_, 1, v_goal_3192_);
lean_closure_set(v___f_3257_, 2, v___x_3253_);
lean_closure_set(v___f_3257_, 3, v_tactic_3193_);
lean_closure_set(v___f_3257_, 4, v_allowFailure_3194_);
lean_closure_set(v___f_3257_, 5, v___x_3254_);
lean_closure_set(v___f_3257_, 6, v___x_3255_);
lean_closure_set(v___f_3257_, 7, v___x_3256_);
v___x_3258_ = lean_box(0);
lean_inc(v_a_3201_);
lean_inc_ref(v_a_3200_);
lean_inc(v_a_3199_);
lean_inc_ref(v_a_3198_);
v___x_3259_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_3205_, v_options_3203_, v___f_3257_, v___x_3258_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3267_; 
v_a_3260_ = lean_ctor_get(v___x_3259_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3262_ = v___x_3259_;
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_a_3260_);
lean_dec(v___x_3259_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3265_; 
if (v_isShared_3263_ == 0)
{
lean_ctor_set_tag(v___x_3262_, 1);
v___x_3265_ = v___x_3262_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_a_3260_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
v___y_3218_ = v_a_3248_;
v___y_3219_ = v___x_3251_;
v_a_3220_ = v___x_3265_;
goto v___jp_3217_;
}
}
}
else
{
lean_object* v_a_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3275_; 
v_a_3268_ = lean_ctor_get(v___x_3259_, 0);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3270_ = v___x_3259_;
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_a_3268_);
lean_dec(v___x_3259_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v___x_3273_; 
if (v_isShared_3271_ == 0)
{
lean_ctor_set_tag(v___x_3270_, 0);
v___x_3273_ = v___x_3270_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_a_3268_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
v___y_3218_ = v_a_3248_;
v___y_3219_ = v___x_3251_;
v_a_3220_ = v___x_3273_;
goto v___jp_3217_;
}
}
}
}
else
{
lean_object* v___x_3276_; uint8_t v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___f_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3276_ = lean_io_get_num_heartbeats();
v___x_3277_ = 0;
v___x_3278_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3278_, 0, v___x_3277_);
lean_ctor_set_uint8(v___x_3278_, 1, v___x_3250_);
lean_ctor_set_uint8(v___x_3278_, 2, v___x_3250_);
lean_ctor_set_uint8(v___x_3278_, 3, v___x_3250_);
v___x_3279_ = lean_box(v_collectAll_3197_);
v___x_3280_ = lean_box(v_includeStar_3196_);
v___x_3281_ = lean_box(v___x_3250_);
v___f_3282_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__5___boxed), 13, 8);
lean_closure_set(v___f_3282_, 0, v_leavePercentHeartbeats_3195_);
lean_closure_set(v___f_3282_, 1, v_goal_3192_);
lean_closure_set(v___f_3282_, 2, v___x_3278_);
lean_closure_set(v___f_3282_, 3, v_tactic_3193_);
lean_closure_set(v___f_3282_, 4, v_allowFailure_3194_);
lean_closure_set(v___f_3282_, 5, v___x_3279_);
lean_closure_set(v___f_3282_, 6, v___x_3280_);
lean_closure_set(v___f_3282_, 7, v___x_3281_);
v___x_3283_ = lean_box(0);
lean_inc(v_a_3201_);
lean_inc_ref(v_a_3200_);
lean_inc(v_a_3199_);
lean_inc_ref(v_a_3198_);
v___x_3284_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_3205_, v_options_3203_, v___f_3282_, v___x_3283_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3292_; 
v_a_3285_ = lean_ctor_get(v___x_3284_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3284_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3287_ = v___x_3284_;
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_a_3285_);
lean_dec(v___x_3284_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3290_; 
if (v_isShared_3288_ == 0)
{
lean_ctor_set_tag(v___x_3287_, 1);
v___x_3290_ = v___x_3287_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_a_3285_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
v___y_3234_ = v_a_3248_;
v___y_3235_ = v___x_3276_;
v_a_3236_ = v___x_3290_;
goto v___jp_3233_;
}
}
}
else
{
lean_object* v_a_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3300_; 
v_a_3293_ = lean_ctor_get(v___x_3284_, 0);
v_isSharedCheck_3300_ = !lean_is_exclusive(v___x_3284_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3295_ = v___x_3284_;
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_a_3293_);
lean_dec(v___x_3284_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v___x_3298_; 
if (v_isShared_3296_ == 0)
{
lean_ctor_set_tag(v___x_3295_, 0);
v___x_3298_ = v___x_3295_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v_a_3293_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
v___y_3234_ = v_a_3248_;
v___y_3235_ = v___x_3276_;
v_a_3236_ = v___x_3298_;
goto v___jp_3233_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___boxed(lean_object* v_goal_3312_, lean_object* v_tactic_3313_, lean_object* v_allowFailure_3314_, lean_object* v_leavePercentHeartbeats_3315_, lean_object* v_includeStar_3316_, lean_object* v_collectAll_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_){
_start:
{
uint8_t v_includeStar_boxed_3323_; uint8_t v_collectAll_boxed_3324_; lean_object* v_res_3325_; 
v_includeStar_boxed_3323_ = lean_unbox(v_includeStar_3316_);
v_collectAll_boxed_3324_ = lean_unbox(v_collectAll_3317_);
v_res_3325_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(v_goal_3312_, v_tactic_3313_, v_allowFailure_3314_, v_leavePercentHeartbeats_3315_, v_includeStar_boxed_3323_, v_collectAll_boxed_3324_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
return v_res_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearch(lean_object* v_goal_3326_, lean_object* v_tactic_3327_, lean_object* v_allowFailure_3328_, lean_object* v_leavePercentHeartbeats_3329_, uint8_t v_includeStar_3330_, uint8_t v_collectAll_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_){
_start:
{
lean_object* v___x_3337_; 
v___x_3337_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(v_goal_3326_, v_tactic_3327_, v_allowFailure_3328_, v_leavePercentHeartbeats_3329_, v_includeStar_3330_, v_collectAll_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_);
return v___x_3337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearch___boxed(lean_object* v_goal_3338_, lean_object* v_tactic_3339_, lean_object* v_allowFailure_3340_, lean_object* v_leavePercentHeartbeats_3341_, lean_object* v_includeStar_3342_, lean_object* v_collectAll_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_){
_start:
{
uint8_t v_includeStar_boxed_3349_; uint8_t v_collectAll_boxed_3350_; lean_object* v_res_3351_; 
v_includeStar_boxed_3349_ = lean_unbox(v_includeStar_3342_);
v_collectAll_boxed_3350_ = lean_unbox(v_collectAll_3343_);
v_res_3351_ = l_Lean_Meta_LibrarySearch_librarySearch(v_goal_3338_, v_tactic_3339_, v_allowFailure_3340_, v_leavePercentHeartbeats_3341_, v_includeStar_boxed_3349_, v_collectAll_boxed_3350_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_);
return v_res_3351_;
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
