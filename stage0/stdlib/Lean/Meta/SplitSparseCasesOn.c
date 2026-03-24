// Lean compiler output
// Module: Lean.Meta.SplitSparseCasesOn
// Imports: public import Lean.Meta.Basic import Lean.Meta.Tactic.Rewrite import Lean.Meta.Constructions.SparseCasesOn import Lean.Meta.Constructions.SparseCasesOnEq import Lean.Meta.HasNotBit import Lean.Meta.Tactic.Cases import Lean.Meta.Tactic.Replace
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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_MVarId_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_unfoldDefinition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_getSparseCasesOnEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchEqHEqLHS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_rewrite(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_MVarId_modifyTargetEqLHS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x27_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_mkHasNotBitProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSparseCasesOnInfo___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_io_mono_nanos_now();
lean_object* lean_io_get_num_heartbeats();
static const lean_ctor_object l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(2, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq___closed__0 = (const lean_object*)&l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__5___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__5___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__6___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "splitSparseCasesOn"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__2___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "Not enough arguments for sparse casesOn application"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__13___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__10(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__10___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__11_spec__12(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__11_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__12___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__12___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__2;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__3_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__4;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__3;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__5_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__6 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_reduceSparseCasesOn_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_reduceSparseCasesOn_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__0;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Major premise is not a constructor application:"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_unfoldDefinition___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__0_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__1_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Match"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__2_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchEqs"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__3 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__3_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__1_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__4_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__2_value),LEAN_SCALAR_PTR_LITERAL(250, 1, 225, 180, 135, 246, 184, 244)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__4_value_aux_1),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__3_value),LEAN_SCALAR_PTR_LITERAL(142, 18, 82, 91, 15, 164, 75, 57)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__4 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__4_value;
static const lean_closure_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__2___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__5 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__5_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__6 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__6_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__7;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Not a sparse casesOn application"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__8 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__8_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__9;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Not a const application"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__10 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__10_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__11;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_reduceSparseCasesOn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Target not an equality"};
static const lean_object* l_Lean_Meta_reduceSparseCasesOn___closed__0 = (const lean_object*)&l_Lean_Meta_reduceSparseCasesOn___closed__0_value;
static lean_once_cell_t l_Lean_Meta_reduceSparseCasesOn___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_reduceSparseCasesOn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_reduceSparseCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceSparseCasesOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_splitSparseCasesOn_spec__1(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "Unexpected number of fields for catch-all branch: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(lean_object*, lean_object*, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__0_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Major premise is not a free variable:"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__1_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(lean_object*, lean_object*, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "splitSparseCasesOn failed"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__0_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "splitSparseCasesOn running on\n"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__2_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitSparseCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitSparseCasesOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq(lean_object* v_goal_6_, lean_object* v_eq_7_, uint8_t v_symm_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_14_; 
lean_inc(v_goal_6_);
v___x_14_ = l_Lean_MVarId_getType(v_goal_6_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
if (lean_obj_tag(v___x_14_) == 0)
{
lean_object* v_a_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v_a_15_ = lean_ctor_get(v___x_14_, 0);
lean_inc(v_a_15_);
lean_dec_ref(v___x_14_);
v___x_16_ = ((lean_object*)(l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq___closed__0));
lean_inc(v_goal_6_);
v___x_17_ = l_Lean_MVarId_rewrite(v_goal_6_, v_a_15_, v_eq_7_, v_symm_8_, v___x_16_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
if (lean_obj_tag(v___x_17_) == 0)
{
lean_object* v_a_18_; lean_object* v_eNew_19_; lean_object* v_eqProof_20_; lean_object* v___x_21_; 
v_a_18_ = lean_ctor_get(v___x_17_, 0);
lean_inc(v_a_18_);
lean_dec_ref(v___x_17_);
v_eNew_19_ = lean_ctor_get(v_a_18_, 0);
lean_inc_ref(v_eNew_19_);
v_eqProof_20_ = lean_ctor_get(v_a_18_, 1);
lean_inc_ref(v_eqProof_20_);
lean_dec(v_a_18_);
v___x_21_ = l_Lean_MVarId_replaceTargetEq(v_goal_6_, v_eNew_19_, v_eqProof_20_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
return v___x_21_;
}
else
{
lean_object* v_a_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_29_; 
lean_dec(v_goal_6_);
v_a_22_ = lean_ctor_get(v___x_17_, 0);
v_isSharedCheck_29_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_29_ == 0)
{
v___x_24_ = v___x_17_;
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_a_22_);
lean_dec(v___x_17_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
if (v_isShared_25_ == 0)
{
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_a_22_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
}
else
{
lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_37_; 
lean_dec_ref(v_eq_7_);
lean_dec(v_goal_6_);
v_a_30_ = lean_ctor_get(v___x_14_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_14_);
if (v_isSharedCheck_37_ == 0)
{
v___x_32_ = v___x_14_;
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_dec(v___x_14_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_35_; 
if (v_isShared_33_ == 0)
{
v___x_35_ = v___x_32_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v_a_30_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq___boxed(lean_object* v_goal_38_, lean_object* v_eq_39_, lean_object* v_symm_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_){
_start:
{
uint8_t v_symm_boxed_46_; lean_object* v_res_47_; 
v_symm_boxed_46_ = lean_unbox(v_symm_40_);
v_res_47_ = l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq(v_goal_38_, v_eq_39_, v_symm_boxed_46_, v_a_41_, v_a_42_, v_a_43_, v_a_44_);
lean_dec(v_a_44_);
lean_dec_ref(v_a_43_);
lean_dec(v_a_42_);
lean_dec_ref(v_a_41_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(lean_object* v_cls_51_, lean_object* v___y_52_){
_start:
{
lean_object* v_options_54_; uint8_t v_hasTrace_55_; 
v_options_54_ = lean_ctor_get(v___y_52_, 2);
v_hasTrace_55_ = lean_ctor_get_uint8(v_options_54_, sizeof(void*)*1);
if (v_hasTrace_55_ == 0)
{
lean_object* v___x_56_; lean_object* v___x_57_; 
lean_dec(v_cls_51_);
v___x_56_ = lean_box(v_hasTrace_55_);
v___x_57_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
return v___x_57_;
}
else
{
lean_object* v_inheritedTraceOptions_58_; lean_object* v___x_59_; lean_object* v___x_60_; uint8_t v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v_inheritedTraceOptions_58_ = lean_ctor_get(v___y_52_, 13);
v___x_59_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__1));
v___x_60_ = l_Lean_Name_append(v___x_59_, v_cls_51_);
v___x_61_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_58_, v_options_54_, v___x_60_);
lean_dec(v___x_60_);
v___x_62_ = lean_box(v___x_61_);
v___x_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
return v___x_63_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___boxed(lean_object* v_cls_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v_cls_64_, v___y_65_);
lean_dec_ref(v___y_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4(lean_object* v_cls_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v_cls_68_, v___y_71_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___boxed(lean_object* v_cls_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4(v_cls_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
return v_res_81_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_82_ = lean_unsigned_to_nat(32u);
v___x_83_ = lean_mk_empty_array_with_capacity(v___x_82_);
v___x_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
return v___x_84_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__5___redArg___closed__1(void){
_start:
{
size_t v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_85_ = ((size_t)5ULL);
v___x_86_ = lean_unsigned_to_nat(0u);
v___x_87_ = lean_unsigned_to_nat(32u);
v___x_88_ = lean_mk_empty_array_with_capacity(v___x_87_);
v___x_89_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__5___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__5___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__5___redArg___closed__0);
v___x_90_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_90_, 0, v___x_89_);
lean_ctor_set(v___x_90_, 1, v___x_88_);
lean_ctor_set(v___x_90_, 2, v___x_86_);
lean_ctor_set(v___x_90_, 3, v___x_86_);
lean_ctor_set_usize(v___x_90_, 4, v___x_85_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__5___redArg(lean_object* v___y_91_){
_start:
{
lean_object* v___x_93_; lean_object* v_traceState_94_; lean_object* v_traces_95_; lean_object* v___x_96_; lean_object* v_traceState_97_; lean_object* v_env_98_; lean_object* v_nextMacroScope_99_; lean_object* v_ngen_100_; lean_object* v_auxDeclNGen_101_; lean_object* v_cache_102_; lean_object* v_messages_103_; lean_object* v_infoState_104_; lean_object* v_snapshotTasks_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_124_; 
v___x_93_ = lean_st_ref_get(v___y_91_);
v_traceState_94_ = lean_ctor_get(v___x_93_, 4);
lean_inc_ref(v_traceState_94_);
lean_dec(v___x_93_);
v_traces_95_ = lean_ctor_get(v_traceState_94_, 0);
lean_inc_ref(v_traces_95_);
lean_dec_ref(v_traceState_94_);
v___x_96_ = lean_st_ref_take(v___y_91_);
v_traceState_97_ = lean_ctor_get(v___x_96_, 4);
v_env_98_ = lean_ctor_get(v___x_96_, 0);
v_nextMacroScope_99_ = lean_ctor_get(v___x_96_, 1);
v_ngen_100_ = lean_ctor_get(v___x_96_, 2);
v_auxDeclNGen_101_ = lean_ctor_get(v___x_96_, 3);
v_cache_102_ = lean_ctor_get(v___x_96_, 5);
v_messages_103_ = lean_ctor_get(v___x_96_, 6);
v_infoState_104_ = lean_ctor_get(v___x_96_, 7);
v_snapshotTasks_105_ = lean_ctor_get(v___x_96_, 8);
v_isSharedCheck_124_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_124_ == 0)
{
v___x_107_ = v___x_96_;
v_isShared_108_ = v_isSharedCheck_124_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_snapshotTasks_105_);
lean_inc(v_infoState_104_);
lean_inc(v_messages_103_);
lean_inc(v_cache_102_);
lean_inc(v_traceState_97_);
lean_inc(v_auxDeclNGen_101_);
lean_inc(v_ngen_100_);
lean_inc(v_nextMacroScope_99_);
lean_inc(v_env_98_);
lean_dec(v___x_96_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_124_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
uint64_t v_tid_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_122_; 
v_tid_109_ = lean_ctor_get_uint64(v_traceState_97_, sizeof(void*)*1);
v_isSharedCheck_122_ = !lean_is_exclusive(v_traceState_97_);
if (v_isSharedCheck_122_ == 0)
{
lean_object* v_unused_123_; 
v_unused_123_ = lean_ctor_get(v_traceState_97_, 0);
lean_dec(v_unused_123_);
v___x_111_ = v_traceState_97_;
v_isShared_112_ = v_isSharedCheck_122_;
goto v_resetjp_110_;
}
else
{
lean_dec(v_traceState_97_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_122_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_113_; lean_object* v___x_115_; 
v___x_113_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__5___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__5___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__5___redArg___closed__1);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_113_);
v___x_115_ = v___x_111_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_113_);
lean_ctor_set_uint64(v_reuseFailAlloc_121_, sizeof(void*)*1, v_tid_109_);
v___x_115_ = v_reuseFailAlloc_121_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
lean_object* v___x_117_; 
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 4, v___x_115_);
v___x_117_ = v___x_107_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_env_98_);
lean_ctor_set(v_reuseFailAlloc_120_, 1, v_nextMacroScope_99_);
lean_ctor_set(v_reuseFailAlloc_120_, 2, v_ngen_100_);
lean_ctor_set(v_reuseFailAlloc_120_, 3, v_auxDeclNGen_101_);
lean_ctor_set(v_reuseFailAlloc_120_, 4, v___x_115_);
lean_ctor_set(v_reuseFailAlloc_120_, 5, v_cache_102_);
lean_ctor_set(v_reuseFailAlloc_120_, 6, v_messages_103_);
lean_ctor_set(v_reuseFailAlloc_120_, 7, v_infoState_104_);
lean_ctor_set(v_reuseFailAlloc_120_, 8, v_snapshotTasks_105_);
v___x_117_ = v_reuseFailAlloc_120_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = lean_st_ref_set(v___y_91_, v___x_117_);
v___x_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_119_, 0, v_traces_95_);
return v___x_119_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__5___redArg___boxed(lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__5___redArg(v___y_125_);
lean_dec(v___y_125_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__5(lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__5___redArg(v___y_131_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__5___boxed(lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v___y_134_, v___y_135_, v___y_136_, v___y_137_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
return v_res_139_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__6(lean_object* v_opts_140_, lean_object* v_opt_141_){
_start:
{
lean_object* v_name_142_; lean_object* v_defValue_143_; lean_object* v_map_144_; lean_object* v___x_145_; 
v_name_142_ = lean_ctor_get(v_opt_141_, 0);
v_defValue_143_ = lean_ctor_get(v_opt_141_, 1);
v_map_144_ = lean_ctor_get(v_opts_140_, 0);
v___x_145_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_144_, v_name_142_);
if (lean_obj_tag(v___x_145_) == 0)
{
uint8_t v___x_146_; 
v___x_146_ = lean_unbox(v_defValue_143_);
return v___x_146_;
}
else
{
lean_object* v_val_147_; 
v_val_147_ = lean_ctor_get(v___x_145_, 0);
lean_inc(v_val_147_);
lean_dec_ref(v___x_145_);
if (lean_obj_tag(v_val_147_) == 1)
{
uint8_t v_v_148_; 
v_v_148_ = lean_ctor_get_uint8(v_val_147_, 0);
lean_dec_ref(v_val_147_);
return v_v_148_;
}
else
{
uint8_t v___x_149_; 
lean_dec(v_val_147_);
v___x_149_ = lean_unbox(v_defValue_143_);
return v___x_149_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__6___boxed(lean_object* v_opts_150_, lean_object* v_opt_151_){
_start:
{
uint8_t v_res_152_; lean_object* v_r_153_; 
v_res_152_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v_opts_150_, v_opt_151_);
lean_dec_ref(v_opt_151_);
lean_dec_ref(v_opts_150_);
v_r_153_ = lean_box(v_res_152_);
return v_r_153_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__2___closed__1(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__2___closed__0));
v___x_156_ = l_Lean_stringToMessageData(v___x_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__2(lean_object* v_x_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__2___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__2___closed__1);
v___x_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__2___boxed(lean_object* v_x_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__2(v_x_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec_ref(v_x_165_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(lean_object* v_msgData_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v___x_178_; lean_object* v_env_179_; lean_object* v___x_180_; lean_object* v_mctx_181_; lean_object* v_lctx_182_; lean_object* v_options_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_178_ = lean_st_ref_get(v___y_176_);
v_env_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc_ref(v_env_179_);
lean_dec(v___x_178_);
v___x_180_ = lean_st_ref_get(v___y_174_);
v_mctx_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc_ref(v_mctx_181_);
lean_dec(v___x_180_);
v_lctx_182_ = lean_ctor_get(v___y_173_, 2);
v_options_183_ = lean_ctor_get(v___y_175_, 2);
lean_inc_ref(v_options_183_);
lean_inc_ref(v_lctx_182_);
v___x_184_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_184_, 0, v_env_179_);
lean_ctor_set(v___x_184_, 1, v_mctx_181_);
lean_ctor_set(v___x_184_, 2, v_lctx_182_);
lean_ctor_set(v___x_184_, 3, v_options_183_);
v___x_185_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v_msgData_172_);
v___x_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5___boxed(lean_object* v_msgData_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msgData_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(lean_object* v_msg_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
lean_object* v_ref_200_; lean_object* v___x_201_; lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_210_; 
v_ref_200_ = lean_ctor_get(v___y_197_, 5);
v___x_201_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msg_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
v_a_202_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_210_ == 0)
{
v___x_204_ = v___x_201_;
v_isShared_205_ = v_isSharedCheck_210_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_201_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_210_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; lean_object* v___x_208_; 
lean_inc(v_ref_200_);
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v_ref_200_);
lean_ctor_set(v___x_206_, 1, v_a_202_);
if (v_isShared_205_ == 0)
{
lean_ctor_set_tag(v___x_204_, 1);
lean_ctor_set(v___x_204_, 0, v___x_206_);
v___x_208_ = v___x_204_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_206_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg___boxed(lean_object* v_msg_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v_msg_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
return v_res_217_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__1(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__0));
v___x_220_ = l_Lean_stringToMessageData(v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1(uint8_t v___x_221_, lean_object* v___f_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
if (v___x_221_ == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_box(0);
lean_inc(v___y_226_);
lean_inc_ref(v___y_225_);
lean_inc(v___y_224_);
lean_inc_ref(v___y_223_);
v___x_229_ = lean_apply_6(v___f_222_, v___x_228_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, lean_box(0));
return v___x_229_;
}
else
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_239_; 
lean_dec_ref(v___f_222_);
v___x_230_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__1);
v___x_231_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_230_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
v_a_232_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_239_ == 0)
{
v___x_234_ = v___x_231_;
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_231_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_237_; 
if (v_isShared_235_ == 0)
{
v___x_237_ = v___x_234_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_a_232_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___boxed(lean_object* v___x_240_, lean_object* v___f_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
uint8_t v___x_13964__boxed_247_; lean_object* v_res_248_; 
v___x_13964__boxed_247_ = lean_unbox(v___x_240_);
v_res_248_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1(v___x_13964__boxed_247_, v___f_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__13(lean_object* v_opts_249_, lean_object* v_opt_250_){
_start:
{
lean_object* v_name_251_; lean_object* v_defValue_252_; lean_object* v_map_253_; lean_object* v___x_254_; 
v_name_251_ = lean_ctor_get(v_opt_250_, 0);
v_defValue_252_ = lean_ctor_get(v_opt_250_, 1);
v_map_253_ = lean_ctor_get(v_opts_249_, 0);
v___x_254_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_253_, v_name_251_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_inc(v_defValue_252_);
return v_defValue_252_;
}
else
{
lean_object* v_val_255_; 
v_val_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc(v_val_255_);
lean_dec_ref(v___x_254_);
if (lean_obj_tag(v_val_255_) == 3)
{
lean_object* v_v_256_; 
v_v_256_ = lean_ctor_get(v_val_255_, 0);
lean_inc(v_v_256_);
lean_dec_ref(v_val_255_);
return v_v_256_;
}
else
{
lean_dec(v_val_255_);
lean_inc(v_defValue_252_);
return v_defValue_252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__13___boxed(lean_object* v_opts_257_, lean_object* v_opt_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__13(v_opts_257_, v_opt_258_);
lean_dec_ref(v_opt_258_);
lean_dec_ref(v_opts_257_);
return v_res_259_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__10(lean_object* v_e_260_){
_start:
{
if (lean_obj_tag(v_e_260_) == 0)
{
uint8_t v___x_261_; 
v___x_261_ = 2;
return v___x_261_;
}
else
{
uint8_t v___x_262_; 
v___x_262_ = 0;
return v___x_262_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__10___boxed(lean_object* v_e_263_){
_start:
{
uint8_t v_res_264_; lean_object* v_r_265_; 
v_res_264_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__10(v_e_263_);
lean_dec_ref(v_e_263_);
v_r_265_ = lean_box(v_res_264_);
return v_r_265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__11_spec__12(size_t v_sz_266_, size_t v_i_267_, lean_object* v_bs_268_){
_start:
{
uint8_t v___x_269_; 
v___x_269_ = lean_usize_dec_lt(v_i_267_, v_sz_266_);
if (v___x_269_ == 0)
{
return v_bs_268_;
}
else
{
lean_object* v_v_270_; lean_object* v_msg_271_; lean_object* v___x_272_; lean_object* v_bs_x27_273_; size_t v___x_274_; size_t v___x_275_; lean_object* v___x_276_; 
v_v_270_ = lean_array_uget_borrowed(v_bs_268_, v_i_267_);
v_msg_271_ = lean_ctor_get(v_v_270_, 1);
lean_inc_ref(v_msg_271_);
v___x_272_ = lean_unsigned_to_nat(0u);
v_bs_x27_273_ = lean_array_uset(v_bs_268_, v_i_267_, v___x_272_);
v___x_274_ = ((size_t)1ULL);
v___x_275_ = lean_usize_add(v_i_267_, v___x_274_);
v___x_276_ = lean_array_uset(v_bs_x27_273_, v_i_267_, v_msg_271_);
v_i_267_ = v___x_275_;
v_bs_268_ = v___x_276_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__11_spec__12___boxed(lean_object* v_sz_278_, lean_object* v_i_279_, lean_object* v_bs_280_){
_start:
{
size_t v_sz_boxed_281_; size_t v_i_boxed_282_; lean_object* v_res_283_; 
v_sz_boxed_281_ = lean_unbox_usize(v_sz_278_);
lean_dec(v_sz_278_);
v_i_boxed_282_ = lean_unbox_usize(v_i_279_);
lean_dec(v_i_279_);
v_res_283_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__11_spec__12(v_sz_boxed_281_, v_i_boxed_282_, v_bs_280_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__11(lean_object* v_oldTraces_284_, lean_object* v_data_285_, lean_object* v_ref_286_, lean_object* v_msg_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v_fileName_293_; lean_object* v_fileMap_294_; lean_object* v_options_295_; lean_object* v_currRecDepth_296_; lean_object* v_maxRecDepth_297_; lean_object* v_ref_298_; lean_object* v_currNamespace_299_; lean_object* v_openDecls_300_; lean_object* v_initHeartbeats_301_; lean_object* v_maxHeartbeats_302_; lean_object* v_quotContext_303_; lean_object* v_currMacroScope_304_; uint8_t v_diag_305_; lean_object* v_cancelTk_x3f_306_; uint8_t v_suppressElabErrors_307_; lean_object* v_inheritedTraceOptions_308_; lean_object* v___x_309_; lean_object* v_traceState_310_; lean_object* v_traces_311_; lean_object* v_ref_312_; lean_object* v___x_313_; lean_object* v___x_314_; size_t v_sz_315_; size_t v___x_316_; lean_object* v___x_317_; lean_object* v_msg_318_; lean_object* v___x_319_; lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_357_; 
v_fileName_293_ = lean_ctor_get(v___y_290_, 0);
v_fileMap_294_ = lean_ctor_get(v___y_290_, 1);
v_options_295_ = lean_ctor_get(v___y_290_, 2);
v_currRecDepth_296_ = lean_ctor_get(v___y_290_, 3);
v_maxRecDepth_297_ = lean_ctor_get(v___y_290_, 4);
v_ref_298_ = lean_ctor_get(v___y_290_, 5);
v_currNamespace_299_ = lean_ctor_get(v___y_290_, 6);
v_openDecls_300_ = lean_ctor_get(v___y_290_, 7);
v_initHeartbeats_301_ = lean_ctor_get(v___y_290_, 8);
v_maxHeartbeats_302_ = lean_ctor_get(v___y_290_, 9);
v_quotContext_303_ = lean_ctor_get(v___y_290_, 10);
v_currMacroScope_304_ = lean_ctor_get(v___y_290_, 11);
v_diag_305_ = lean_ctor_get_uint8(v___y_290_, sizeof(void*)*14);
v_cancelTk_x3f_306_ = lean_ctor_get(v___y_290_, 12);
v_suppressElabErrors_307_ = lean_ctor_get_uint8(v___y_290_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_308_ = lean_ctor_get(v___y_290_, 13);
v___x_309_ = lean_st_ref_get(v___y_291_);
v_traceState_310_ = lean_ctor_get(v___x_309_, 4);
lean_inc_ref(v_traceState_310_);
lean_dec(v___x_309_);
v_traces_311_ = lean_ctor_get(v_traceState_310_, 0);
lean_inc_ref(v_traces_311_);
lean_dec_ref(v_traceState_310_);
v_ref_312_ = l_Lean_replaceRef(v_ref_286_, v_ref_298_);
lean_inc_ref(v_inheritedTraceOptions_308_);
lean_inc(v_cancelTk_x3f_306_);
lean_inc(v_currMacroScope_304_);
lean_inc(v_quotContext_303_);
lean_inc(v_maxHeartbeats_302_);
lean_inc(v_initHeartbeats_301_);
lean_inc(v_openDecls_300_);
lean_inc(v_currNamespace_299_);
lean_inc(v_maxRecDepth_297_);
lean_inc(v_currRecDepth_296_);
lean_inc_ref(v_options_295_);
lean_inc_ref(v_fileMap_294_);
lean_inc_ref(v_fileName_293_);
v___x_313_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_313_, 0, v_fileName_293_);
lean_ctor_set(v___x_313_, 1, v_fileMap_294_);
lean_ctor_set(v___x_313_, 2, v_options_295_);
lean_ctor_set(v___x_313_, 3, v_currRecDepth_296_);
lean_ctor_set(v___x_313_, 4, v_maxRecDepth_297_);
lean_ctor_set(v___x_313_, 5, v_ref_312_);
lean_ctor_set(v___x_313_, 6, v_currNamespace_299_);
lean_ctor_set(v___x_313_, 7, v_openDecls_300_);
lean_ctor_set(v___x_313_, 8, v_initHeartbeats_301_);
lean_ctor_set(v___x_313_, 9, v_maxHeartbeats_302_);
lean_ctor_set(v___x_313_, 10, v_quotContext_303_);
lean_ctor_set(v___x_313_, 11, v_currMacroScope_304_);
lean_ctor_set(v___x_313_, 12, v_cancelTk_x3f_306_);
lean_ctor_set(v___x_313_, 13, v_inheritedTraceOptions_308_);
lean_ctor_set_uint8(v___x_313_, sizeof(void*)*14, v_diag_305_);
lean_ctor_set_uint8(v___x_313_, sizeof(void*)*14 + 1, v_suppressElabErrors_307_);
v___x_314_ = l_Lean_PersistentArray_toArray___redArg(v_traces_311_);
lean_dec_ref(v_traces_311_);
v_sz_315_ = lean_array_size(v___x_314_);
v___x_316_ = ((size_t)0ULL);
v___x_317_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__11_spec__12(v_sz_315_, v___x_316_, v___x_314_);
v_msg_318_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_318_, 0, v_data_285_);
lean_ctor_set(v_msg_318_, 1, v_msg_287_);
lean_ctor_set(v_msg_318_, 2, v___x_317_);
v___x_319_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msg_318_, v___y_288_, v___y_289_, v___x_313_, v___y_291_);
lean_dec_ref(v___x_313_);
v_a_320_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_357_ == 0)
{
v___x_322_ = v___x_319_;
v_isShared_323_ = v_isSharedCheck_357_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_319_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_357_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_324_; lean_object* v_traceState_325_; lean_object* v_env_326_; lean_object* v_nextMacroScope_327_; lean_object* v_ngen_328_; lean_object* v_auxDeclNGen_329_; lean_object* v_cache_330_; lean_object* v_messages_331_; lean_object* v_infoState_332_; lean_object* v_snapshotTasks_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_356_; 
v___x_324_ = lean_st_ref_take(v___y_291_);
v_traceState_325_ = lean_ctor_get(v___x_324_, 4);
v_env_326_ = lean_ctor_get(v___x_324_, 0);
v_nextMacroScope_327_ = lean_ctor_get(v___x_324_, 1);
v_ngen_328_ = lean_ctor_get(v___x_324_, 2);
v_auxDeclNGen_329_ = lean_ctor_get(v___x_324_, 3);
v_cache_330_ = lean_ctor_get(v___x_324_, 5);
v_messages_331_ = lean_ctor_get(v___x_324_, 6);
v_infoState_332_ = lean_ctor_get(v___x_324_, 7);
v_snapshotTasks_333_ = lean_ctor_get(v___x_324_, 8);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_356_ == 0)
{
v___x_335_ = v___x_324_;
v_isShared_336_ = v_isSharedCheck_356_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_snapshotTasks_333_);
lean_inc(v_infoState_332_);
lean_inc(v_messages_331_);
lean_inc(v_cache_330_);
lean_inc(v_traceState_325_);
lean_inc(v_auxDeclNGen_329_);
lean_inc(v_ngen_328_);
lean_inc(v_nextMacroScope_327_);
lean_inc(v_env_326_);
lean_dec(v___x_324_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_356_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
uint64_t v_tid_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_354_; 
v_tid_337_ = lean_ctor_get_uint64(v_traceState_325_, sizeof(void*)*1);
v_isSharedCheck_354_ = !lean_is_exclusive(v_traceState_325_);
if (v_isSharedCheck_354_ == 0)
{
lean_object* v_unused_355_; 
v_unused_355_ = lean_ctor_get(v_traceState_325_, 0);
lean_dec(v_unused_355_);
v___x_339_ = v_traceState_325_;
v_isShared_340_ = v_isSharedCheck_354_;
goto v_resetjp_338_;
}
else
{
lean_dec(v_traceState_325_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_354_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_344_; 
v___x_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_341_, 0, v_ref_286_);
lean_ctor_set(v___x_341_, 1, v_a_320_);
v___x_342_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_284_, v___x_341_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 0, v___x_342_);
v___x_344_ = v___x_339_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_342_);
lean_ctor_set_uint64(v_reuseFailAlloc_353_, sizeof(void*)*1, v_tid_337_);
v___x_344_ = v_reuseFailAlloc_353_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
lean_object* v___x_346_; 
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 4, v___x_344_);
v___x_346_ = v___x_335_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_env_326_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v_nextMacroScope_327_);
lean_ctor_set(v_reuseFailAlloc_352_, 2, v_ngen_328_);
lean_ctor_set(v_reuseFailAlloc_352_, 3, v_auxDeclNGen_329_);
lean_ctor_set(v_reuseFailAlloc_352_, 4, v___x_344_);
lean_ctor_set(v_reuseFailAlloc_352_, 5, v_cache_330_);
lean_ctor_set(v_reuseFailAlloc_352_, 6, v_messages_331_);
lean_ctor_set(v_reuseFailAlloc_352_, 7, v_infoState_332_);
lean_ctor_set(v_reuseFailAlloc_352_, 8, v_snapshotTasks_333_);
v___x_346_ = v_reuseFailAlloc_352_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_350_; 
v___x_347_ = lean_st_ref_set(v___y_291_, v___x_346_);
v___x_348_ = lean_box(0);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 0, v___x_348_);
v___x_350_ = v___x_322_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_348_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__11___boxed(lean_object* v_oldTraces_358_, lean_object* v_data_359_, lean_object* v_ref_360_, lean_object* v_msg_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__11(v_oldTraces_358_, v_data_359_, v_ref_360_, v_msg_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__12___redArg(lean_object* v_x_368_){
_start:
{
if (lean_obj_tag(v_x_368_) == 0)
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_377_; 
v_a_370_ = lean_ctor_get(v_x_368_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v_x_368_);
if (v_isSharedCheck_377_ == 0)
{
v___x_372_ = v_x_368_;
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v_x_368_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set_tag(v___x_372_, 1);
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_370_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
else
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_385_; 
v_a_378_ = lean_ctor_get(v_x_368_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v_x_368_);
if (v_isSharedCheck_385_ == 0)
{
v___x_380_ = v_x_368_;
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v_x_368_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_383_; 
if (v_isShared_381_ == 0)
{
lean_ctor_set_tag(v___x_380_, 0);
v___x_383_ = v___x_380_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_a_378_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__12___redArg___boxed(lean_object* v_x_386_, lean_object* v___y_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__12___redArg(v_x_386_);
return v_res_388_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0));
v___x_391_ = l_Lean_stringToMessageData(v___x_390_);
return v___x_391_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__2(void){
_start:
{
lean_object* v___x_392_; double v___x_393_; 
v___x_392_ = lean_unsigned_to_nat(0u);
v___x_393_ = lean_float_of_nat(v___x_392_);
return v___x_393_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__4(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__3));
v___x_396_ = l_Lean_stringToMessageData(v___x_395_);
return v___x_396_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5(void){
_start:
{
lean_object* v___x_397_; double v___x_398_; 
v___x_397_ = lean_unsigned_to_nat(1000u);
v___x_398_ = lean_float_of_nat(v___x_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7(lean_object* v_cls_399_, uint8_t v_collapsed_400_, lean_object* v_tag_401_, lean_object* v_opts_402_, uint8_t v_clsEnabled_403_, lean_object* v_oldTraces_404_, lean_object* v_msg_405_, lean_object* v_resStartStop_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v_fst_412_; lean_object* v_snd_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_511_; 
v_fst_412_ = lean_ctor_get(v_resStartStop_406_, 0);
v_snd_413_ = lean_ctor_get(v_resStartStop_406_, 1);
v_isSharedCheck_511_ = !lean_is_exclusive(v_resStartStop_406_);
if (v_isSharedCheck_511_ == 0)
{
v___x_415_ = v_resStartStop_406_;
v_isShared_416_ = v_isSharedCheck_511_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_snd_413_);
lean_inc(v_fst_412_);
lean_dec(v_resStartStop_406_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_511_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___y_418_; lean_object* v___y_419_; lean_object* v_data_420_; lean_object* v_fst_431_; lean_object* v_snd_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_510_; 
v_fst_431_ = lean_ctor_get(v_snd_413_, 0);
v_snd_432_ = lean_ctor_get(v_snd_413_, 1);
v_isSharedCheck_510_ = !lean_is_exclusive(v_snd_413_);
if (v_isSharedCheck_510_ == 0)
{
v___x_434_ = v_snd_413_;
v_isShared_435_ = v_isSharedCheck_510_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_snd_432_);
lean_inc(v_fst_431_);
lean_dec(v_snd_413_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_510_;
goto v_resetjp_433_;
}
v___jp_417_:
{
lean_object* v___x_421_; 
lean_inc(v___y_419_);
v___x_421_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__11(v_oldTraces_404_, v_data_420_, v___y_419_, v___y_418_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v___x_422_; 
lean_dec_ref(v___x_421_);
v___x_422_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__12___redArg(v_fst_412_);
return v___x_422_;
}
else
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
lean_dec(v_fst_412_);
v_a_423_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_430_ == 0)
{
v___x_425_ = v___x_421_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_421_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
v_resetjp_433_:
{
lean_object* v___x_436_; uint8_t v___x_437_; lean_object* v___y_439_; lean_object* v_a_440_; uint8_t v___y_464_; double v___y_495_; 
v___x_436_ = l_Lean_trace_profiler;
v___x_437_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v_opts_402_, v___x_436_);
if (v___x_437_ == 0)
{
v___y_464_ = v___x_437_;
goto v___jp_463_;
}
else
{
lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_500_ = l_Lean_trace_profiler_useHeartbeats;
v___x_501_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v_opts_402_, v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; double v___x_504_; double v___x_505_; double v___x_506_; 
v___x_502_ = l_Lean_trace_profiler_threshold;
v___x_503_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__13(v_opts_402_, v___x_502_);
v___x_504_ = lean_float_of_nat(v___x_503_);
v___x_505_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5);
v___x_506_ = lean_float_div(v___x_504_, v___x_505_);
v___y_495_ = v___x_506_;
goto v___jp_494_;
}
else
{
lean_object* v___x_507_; lean_object* v___x_508_; double v___x_509_; 
v___x_507_ = l_Lean_trace_profiler_threshold;
v___x_508_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__13(v_opts_402_, v___x_507_);
v___x_509_ = lean_float_of_nat(v___x_508_);
v___y_495_ = v___x_509_;
goto v___jp_494_;
}
}
v___jp_438_:
{
uint8_t v_result_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_446_; 
v_result_441_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__10(v_fst_412_);
v___x_442_ = l_Lean_TraceResult_toEmoji(v_result_441_);
v___x_443_ = l_Lean_stringToMessageData(v___x_442_);
v___x_444_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1);
if (v_isShared_435_ == 0)
{
lean_ctor_set_tag(v___x_434_, 7);
lean_ctor_set(v___x_434_, 1, v___x_444_);
lean_ctor_set(v___x_434_, 0, v___x_443_);
v___x_446_ = v___x_434_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_443_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v___x_444_);
v___x_446_ = v_reuseFailAlloc_457_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
lean_object* v_m_448_; 
if (v_isShared_416_ == 0)
{
lean_ctor_set_tag(v___x_415_, 7);
lean_ctor_set(v___x_415_, 1, v_a_440_);
lean_ctor_set(v___x_415_, 0, v___x_446_);
v_m_448_ = v___x_415_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_446_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_a_440_);
v_m_448_ = v_reuseFailAlloc_456_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_449_; lean_object* v___x_450_; double v___x_451_; lean_object* v_data_452_; 
v___x_449_ = lean_box(v_result_441_);
v___x_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
v___x_451_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__2);
lean_inc_ref(v_tag_401_);
lean_inc_ref(v___x_450_);
lean_inc(v_cls_399_);
v_data_452_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_452_, 0, v_cls_399_);
lean_ctor_set(v_data_452_, 1, v___x_450_);
lean_ctor_set(v_data_452_, 2, v_tag_401_);
lean_ctor_set_float(v_data_452_, sizeof(void*)*3, v___x_451_);
lean_ctor_set_float(v_data_452_, sizeof(void*)*3 + 8, v___x_451_);
lean_ctor_set_uint8(v_data_452_, sizeof(void*)*3 + 16, v_collapsed_400_);
if (v___x_437_ == 0)
{
lean_dec_ref(v___x_450_);
lean_dec(v_snd_432_);
lean_dec(v_fst_431_);
lean_dec_ref(v_tag_401_);
lean_dec(v_cls_399_);
v___y_418_ = v_m_448_;
v___y_419_ = v___y_439_;
v_data_420_ = v_data_452_;
goto v___jp_417_;
}
else
{
lean_object* v_data_453_; double v___x_454_; double v___x_455_; 
lean_dec_ref(v_data_452_);
v_data_453_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_453_, 0, v_cls_399_);
lean_ctor_set(v_data_453_, 1, v___x_450_);
lean_ctor_set(v_data_453_, 2, v_tag_401_);
v___x_454_ = lean_unbox_float(v_fst_431_);
lean_dec(v_fst_431_);
lean_ctor_set_float(v_data_453_, sizeof(void*)*3, v___x_454_);
v___x_455_ = lean_unbox_float(v_snd_432_);
lean_dec(v_snd_432_);
lean_ctor_set_float(v_data_453_, sizeof(void*)*3 + 8, v___x_455_);
lean_ctor_set_uint8(v_data_453_, sizeof(void*)*3 + 16, v_collapsed_400_);
v___y_418_ = v_m_448_;
v___y_419_ = v___y_439_;
v_data_420_ = v_data_453_;
goto v___jp_417_;
}
}
}
}
v___jp_458_:
{
lean_object* v_ref_459_; lean_object* v___x_460_; 
v_ref_459_ = lean_ctor_get(v___y_409_, 5);
lean_inc(v___y_410_);
lean_inc_ref(v___y_409_);
lean_inc(v___y_408_);
lean_inc_ref(v___y_407_);
lean_inc(v_fst_412_);
v___x_460_ = lean_apply_6(v_msg_405_, v_fst_412_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, lean_box(0));
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_a_461_);
lean_dec_ref(v___x_460_);
v___y_439_ = v_ref_459_;
v_a_440_ = v_a_461_;
goto v___jp_438_;
}
else
{
lean_object* v___x_462_; 
lean_dec_ref(v___x_460_);
v___x_462_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__4);
v___y_439_ = v_ref_459_;
v_a_440_ = v___x_462_;
goto v___jp_438_;
}
}
v___jp_463_:
{
if (v_clsEnabled_403_ == 0)
{
if (v___y_464_ == 0)
{
lean_object* v___x_465_; lean_object* v_traceState_466_; lean_object* v_env_467_; lean_object* v_nextMacroScope_468_; lean_object* v_ngen_469_; lean_object* v_auxDeclNGen_470_; lean_object* v_cache_471_; lean_object* v_messages_472_; lean_object* v_infoState_473_; lean_object* v_snapshotTasks_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_493_; 
lean_del_object(v___x_434_);
lean_dec(v_snd_432_);
lean_dec(v_fst_431_);
lean_del_object(v___x_415_);
lean_dec_ref(v_msg_405_);
lean_dec_ref(v_tag_401_);
lean_dec(v_cls_399_);
v___x_465_ = lean_st_ref_take(v___y_410_);
v_traceState_466_ = lean_ctor_get(v___x_465_, 4);
v_env_467_ = lean_ctor_get(v___x_465_, 0);
v_nextMacroScope_468_ = lean_ctor_get(v___x_465_, 1);
v_ngen_469_ = lean_ctor_get(v___x_465_, 2);
v_auxDeclNGen_470_ = lean_ctor_get(v___x_465_, 3);
v_cache_471_ = lean_ctor_get(v___x_465_, 5);
v_messages_472_ = lean_ctor_get(v___x_465_, 6);
v_infoState_473_ = lean_ctor_get(v___x_465_, 7);
v_snapshotTasks_474_ = lean_ctor_get(v___x_465_, 8);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_493_ == 0)
{
v___x_476_ = v___x_465_;
v_isShared_477_ = v_isSharedCheck_493_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_snapshotTasks_474_);
lean_inc(v_infoState_473_);
lean_inc(v_messages_472_);
lean_inc(v_cache_471_);
lean_inc(v_traceState_466_);
lean_inc(v_auxDeclNGen_470_);
lean_inc(v_ngen_469_);
lean_inc(v_nextMacroScope_468_);
lean_inc(v_env_467_);
lean_dec(v___x_465_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_493_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
uint64_t v_tid_478_; lean_object* v_traces_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_492_; 
v_tid_478_ = lean_ctor_get_uint64(v_traceState_466_, sizeof(void*)*1);
v_traces_479_ = lean_ctor_get(v_traceState_466_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v_traceState_466_);
if (v_isSharedCheck_492_ == 0)
{
v___x_481_ = v_traceState_466_;
v_isShared_482_ = v_isSharedCheck_492_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_traces_479_);
lean_dec(v_traceState_466_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_492_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; lean_object* v___x_485_; 
v___x_483_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_404_, v_traces_479_);
lean_dec_ref(v_traces_479_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_483_);
v___x_485_ = v___x_481_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_483_);
lean_ctor_set_uint64(v_reuseFailAlloc_491_, sizeof(void*)*1, v_tid_478_);
v___x_485_ = v_reuseFailAlloc_491_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
lean_object* v___x_487_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v___x_485_);
v___x_487_ = v___x_476_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_env_467_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v_nextMacroScope_468_);
lean_ctor_set(v_reuseFailAlloc_490_, 2, v_ngen_469_);
lean_ctor_set(v_reuseFailAlloc_490_, 3, v_auxDeclNGen_470_);
lean_ctor_set(v_reuseFailAlloc_490_, 4, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_490_, 5, v_cache_471_);
lean_ctor_set(v_reuseFailAlloc_490_, 6, v_messages_472_);
lean_ctor_set(v_reuseFailAlloc_490_, 7, v_infoState_473_);
lean_ctor_set(v_reuseFailAlloc_490_, 8, v_snapshotTasks_474_);
v___x_487_ = v_reuseFailAlloc_490_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = lean_st_ref_set(v___y_410_, v___x_487_);
v___x_489_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__12___redArg(v_fst_412_);
return v___x_489_;
}
}
}
}
}
else
{
goto v___jp_458_;
}
}
else
{
goto v___jp_458_;
}
}
v___jp_494_:
{
double v___x_496_; double v___x_497_; double v___x_498_; uint8_t v___x_499_; 
v___x_496_ = lean_unbox_float(v_snd_432_);
v___x_497_ = lean_unbox_float(v_fst_431_);
v___x_498_ = lean_float_sub(v___x_496_, v___x_497_);
v___x_499_ = lean_float_decLt(v___y_495_, v___x_498_);
v___y_464_ = v___x_499_;
goto v___jp_463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___boxed(lean_object* v_cls_512_, lean_object* v_collapsed_513_, lean_object* v_tag_514_, lean_object* v_opts_515_, lean_object* v_clsEnabled_516_, lean_object* v_oldTraces_517_, lean_object* v_msg_518_, lean_object* v_resStartStop_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
uint8_t v_collapsed_boxed_525_; uint8_t v_clsEnabled_boxed_526_; lean_object* v_res_527_; 
v_collapsed_boxed_525_ = lean_unbox(v_collapsed_513_);
v_clsEnabled_boxed_526_ = lean_unbox(v_clsEnabled_516_);
v_res_527_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7(v_cls_512_, v_collapsed_boxed_525_, v_tag_514_, v_opts_515_, v_clsEnabled_boxed_526_, v_oldTraces_517_, v_msg_518_, v_resStartStop_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec_ref(v_opts_515_);
return v_res_527_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1_spec__2(lean_object* v_a_528_, lean_object* v_as_529_, size_t v_i_530_, size_t v_stop_531_){
_start:
{
uint8_t v___x_532_; 
v___x_532_ = lean_usize_dec_eq(v_i_530_, v_stop_531_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_533_ = lean_array_uget_borrowed(v_as_529_, v_i_530_);
v___x_534_ = lean_name_eq(v_a_528_, v___x_533_);
if (v___x_534_ == 0)
{
size_t v___x_535_; size_t v___x_536_; 
v___x_535_ = ((size_t)1ULL);
v___x_536_ = lean_usize_add(v_i_530_, v___x_535_);
v_i_530_ = v___x_536_;
goto _start;
}
else
{
return v___x_534_;
}
}
else
{
uint8_t v___x_538_; 
v___x_538_ = 0;
return v___x_538_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1_spec__2___boxed(lean_object* v_a_539_, lean_object* v_as_540_, lean_object* v_i_541_, lean_object* v_stop_542_){
_start:
{
size_t v_i_boxed_543_; size_t v_stop_boxed_544_; uint8_t v_res_545_; lean_object* v_r_546_; 
v_i_boxed_543_ = lean_unbox_usize(v_i_541_);
lean_dec(v_i_541_);
v_stop_boxed_544_ = lean_unbox_usize(v_stop_542_);
lean_dec(v_stop_542_);
v_res_545_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1_spec__2(v_a_539_, v_as_540_, v_i_boxed_543_, v_stop_boxed_544_);
lean_dec_ref(v_as_540_);
lean_dec(v_a_539_);
v_r_546_ = lean_box(v_res_545_);
return v_r_546_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1(lean_object* v_as_547_, lean_object* v_a_548_){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v___x_549_ = lean_unsigned_to_nat(0u);
v___x_550_ = lean_array_get_size(v_as_547_);
v___x_551_ = lean_nat_dec_lt(v___x_549_, v___x_550_);
if (v___x_551_ == 0)
{
return v___x_551_;
}
else
{
if (v___x_551_ == 0)
{
return v___x_551_;
}
else
{
size_t v___x_552_; size_t v___x_553_; uint8_t v___x_554_; 
v___x_552_ = ((size_t)0ULL);
v___x_553_ = lean_usize_of_nat(v___x_550_);
v___x_554_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1_spec__2(v_a_548_, v_as_547_, v___x_552_, v___x_553_);
return v___x_554_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1___boxed(lean_object* v_as_555_, lean_object* v_a_556_){
_start:
{
uint8_t v_res_557_; lean_object* v_r_558_; 
v_res_557_ = l_Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1(v_as_555_, v_a_556_);
lean_dec(v_a_556_);
lean_dec_ref(v_as_555_);
v_r_558_ = lean_box(v_res_557_);
return v_r_558_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l_instMonadEIO(lean_box(0));
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0(lean_object* v_msg_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v_toApplicative_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_633_; 
v___x_570_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__0);
v___x_571_ = l_StateRefT_x27_instMonad___redArg(v___x_570_);
v_toApplicative_572_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_633_ == 0)
{
lean_object* v_unused_634_; 
v_unused_634_ = lean_ctor_get(v___x_571_, 1);
lean_dec(v_unused_634_);
v___x_574_ = v___x_571_;
v_isShared_575_ = v_isSharedCheck_633_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_toApplicative_572_);
lean_dec(v___x_571_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_633_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v_toFunctor_576_; lean_object* v_toSeq_577_; lean_object* v_toSeqLeft_578_; lean_object* v_toSeqRight_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_631_; 
v_toFunctor_576_ = lean_ctor_get(v_toApplicative_572_, 0);
v_toSeq_577_ = lean_ctor_get(v_toApplicative_572_, 2);
v_toSeqLeft_578_ = lean_ctor_get(v_toApplicative_572_, 3);
v_toSeqRight_579_ = lean_ctor_get(v_toApplicative_572_, 4);
v_isSharedCheck_631_ = !lean_is_exclusive(v_toApplicative_572_);
if (v_isSharedCheck_631_ == 0)
{
lean_object* v_unused_632_; 
v_unused_632_ = lean_ctor_get(v_toApplicative_572_, 1);
lean_dec(v_unused_632_);
v___x_581_ = v_toApplicative_572_;
v_isShared_582_ = v_isSharedCheck_631_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_toSeqRight_579_);
lean_inc(v_toSeqLeft_578_);
lean_inc(v_toSeq_577_);
lean_inc(v_toFunctor_576_);
lean_dec(v_toApplicative_572_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_631_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___f_583_; lean_object* v___f_584_; lean_object* v___f_585_; lean_object* v___f_586_; lean_object* v___x_587_; lean_object* v___f_588_; lean_object* v___f_589_; lean_object* v___f_590_; lean_object* v___x_592_; 
v___f_583_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__1));
v___f_584_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_576_);
v___f_585_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_585_, 0, v_toFunctor_576_);
v___f_586_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_586_, 0, v_toFunctor_576_);
v___x_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_587_, 0, v___f_585_);
lean_ctor_set(v___x_587_, 1, v___f_586_);
v___f_588_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_588_, 0, v_toSeqRight_579_);
v___f_589_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_589_, 0, v_toSeqLeft_578_);
v___f_590_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_590_, 0, v_toSeq_577_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 4, v___f_588_);
lean_ctor_set(v___x_581_, 3, v___f_589_);
lean_ctor_set(v___x_581_, 2, v___f_590_);
lean_ctor_set(v___x_581_, 1, v___f_583_);
lean_ctor_set(v___x_581_, 0, v___x_587_);
v___x_592_ = v___x_581_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_587_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v___f_583_);
lean_ctor_set(v_reuseFailAlloc_630_, 2, v___f_590_);
lean_ctor_set(v_reuseFailAlloc_630_, 3, v___f_589_);
lean_ctor_set(v_reuseFailAlloc_630_, 4, v___f_588_);
v___x_592_ = v_reuseFailAlloc_630_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_object* v___x_594_; 
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 1, v___f_584_);
lean_ctor_set(v___x_574_, 0, v___x_592_);
v___x_594_ = v___x_574_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_592_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v___f_584_);
v___x_594_ = v_reuseFailAlloc_629_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_595_; lean_object* v_toApplicative_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_627_; 
v___x_595_ = l_StateRefT_x27_instMonad___redArg(v___x_594_);
v_toApplicative_596_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_627_ == 0)
{
lean_object* v_unused_628_; 
v_unused_628_ = lean_ctor_get(v___x_595_, 1);
lean_dec(v_unused_628_);
v___x_598_ = v___x_595_;
v_isShared_599_ = v_isSharedCheck_627_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_toApplicative_596_);
lean_dec(v___x_595_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_627_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v_toFunctor_600_; lean_object* v_toSeq_601_; lean_object* v_toSeqLeft_602_; lean_object* v_toSeqRight_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_625_; 
v_toFunctor_600_ = lean_ctor_get(v_toApplicative_596_, 0);
v_toSeq_601_ = lean_ctor_get(v_toApplicative_596_, 2);
v_toSeqLeft_602_ = lean_ctor_get(v_toApplicative_596_, 3);
v_toSeqRight_603_ = lean_ctor_get(v_toApplicative_596_, 4);
v_isSharedCheck_625_ = !lean_is_exclusive(v_toApplicative_596_);
if (v_isSharedCheck_625_ == 0)
{
lean_object* v_unused_626_; 
v_unused_626_ = lean_ctor_get(v_toApplicative_596_, 1);
lean_dec(v_unused_626_);
v___x_605_ = v_toApplicative_596_;
v_isShared_606_ = v_isSharedCheck_625_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_toSeqRight_603_);
lean_inc(v_toSeqLeft_602_);
lean_inc(v_toSeq_601_);
lean_inc(v_toFunctor_600_);
lean_dec(v_toApplicative_596_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_625_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___f_607_; lean_object* v___f_608_; lean_object* v___f_609_; lean_object* v___f_610_; lean_object* v___x_611_; lean_object* v___f_612_; lean_object* v___f_613_; lean_object* v___f_614_; lean_object* v___x_616_; 
v___f_607_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__3));
v___f_608_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__4));
lean_inc_ref(v_toFunctor_600_);
v___f_609_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_609_, 0, v_toFunctor_600_);
v___f_610_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_610_, 0, v_toFunctor_600_);
v___x_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_611_, 0, v___f_609_);
lean_ctor_set(v___x_611_, 1, v___f_610_);
v___f_612_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_612_, 0, v_toSeqRight_603_);
v___f_613_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_613_, 0, v_toSeqLeft_602_);
v___f_614_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_614_, 0, v_toSeq_601_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 4, v___f_612_);
lean_ctor_set(v___x_605_, 3, v___f_613_);
lean_ctor_set(v___x_605_, 2, v___f_614_);
lean_ctor_set(v___x_605_, 1, v___f_607_);
lean_ctor_set(v___x_605_, 0, v___x_611_);
v___x_616_ = v___x_605_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v___f_607_);
lean_ctor_set(v_reuseFailAlloc_624_, 2, v___f_614_);
lean_ctor_set(v_reuseFailAlloc_624_, 3, v___f_613_);
lean_ctor_set(v_reuseFailAlloc_624_, 4, v___f_612_);
v___x_616_ = v_reuseFailAlloc_624_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_object* v___x_618_; 
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 1, v___f_608_);
lean_ctor_set(v___x_598_, 0, v___x_616_);
v___x_618_ = v___x_598_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_616_);
lean_ctor_set(v_reuseFailAlloc_623_, 1, v___f_608_);
v___x_618_ = v_reuseFailAlloc_623_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_10725__overap_621_; lean_object* v___x_622_; 
v___x_619_ = lean_box(0);
v___x_620_ = l_instInhabitedOfMonad___redArg(v___x_618_, v___x_619_);
v___x_10725__overap_621_ = lean_panic_fn(v___x_620_, v_msg_564_);
lean_inc(v___y_568_);
lean_inc_ref(v___y_567_);
lean_inc(v___y_566_);
lean_inc_ref(v___y_565_);
v___x_622_ = lean_apply_5(v___x_10725__overap_621_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, lean_box(0));
return v___x_622_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___boxed(lean_object* v_msg_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0(v_msg_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
return v_res_641_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__1(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__0));
v___x_644_ = l_Lean_stringToMessageData(v___x_643_);
return v___x_644_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__3(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__2));
v___x_647_ = l_Lean_stringToMessageData(v___x_646_);
return v___x_647_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__7(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_651_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__6));
v___x_652_ = lean_unsigned_to_nat(11u);
v___x_653_ = lean_unsigned_to_nat(122u);
v___x_654_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__5));
v___x_655_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__4));
v___x_656_ = l_mkPanicMessageWithDecl(v___x_655_, v___x_654_, v___x_653_, v___x_652_, v___x_651_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0(lean_object* v_constName_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v___x_671_; lean_object* v_env_672_; uint8_t v___x_673_; lean_object* v___x_674_; 
v___x_671_ = lean_st_ref_get(v___y_661_);
v_env_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc_ref(v_env_672_);
lean_dec(v___x_671_);
v___x_673_ = 0;
lean_inc(v_constName_657_);
v___x_674_ = l_Lean_Environment_findAsync_x3f(v_env_672_, v_constName_657_, v___x_673_);
if (lean_obj_tag(v___x_674_) == 1)
{
lean_object* v_val_675_; uint8_t v_kind_676_; 
v_val_675_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_val_675_);
lean_dec_ref(v___x_674_);
v_kind_676_ = lean_ctor_get_uint8(v_val_675_, sizeof(void*)*3);
if (v_kind_676_ == 6)
{
lean_object* v___x_677_; 
v___x_677_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_675_);
if (lean_obj_tag(v___x_677_) == 6)
{
lean_object* v_val_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_685_; 
lean_dec(v_constName_657_);
v_val_678_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_685_ == 0)
{
v___x_680_ = v___x_677_;
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_val_678_);
lean_dec(v___x_677_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_683_; 
if (v_isShared_681_ == 0)
{
lean_ctor_set_tag(v___x_680_, 0);
v___x_683_ = v___x_680_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_val_678_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
else
{
lean_object* v___x_686_; lean_object* v___x_687_; 
lean_dec_ref(v___x_677_);
v___x_686_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__7);
v___x_687_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0(v___x_686_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_696_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_696_ == 0)
{
v___x_690_ = v___x_687_;
v_isShared_691_ = v_isSharedCheck_696_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_687_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_696_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
if (lean_obj_tag(v_a_688_) == 0)
{
lean_del_object(v___x_690_);
goto v___jp_663_;
}
else
{
lean_object* v_val_692_; lean_object* v___x_694_; 
lean_dec(v_constName_657_);
v_val_692_ = lean_ctor_get(v_a_688_, 0);
lean_inc(v_val_692_);
lean_dec_ref(v_a_688_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v_val_692_);
v___x_694_ = v___x_690_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_val_692_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
lean_dec(v_constName_657_);
v_a_697_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_687_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_687_);
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
else
{
lean_dec(v_val_675_);
goto v___jp_663_;
}
}
else
{
lean_dec(v___x_674_);
goto v___jp_663_;
}
v___jp_663_:
{
lean_object* v___x_664_; uint8_t v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_664_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__1);
v___x_665_ = 0;
v___x_666_ = l_Lean_MessageData_ofConstName(v_constName_657_, v___x_665_);
v___x_667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_664_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
v___x_668_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__3);
v___x_669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_667_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
v___x_670_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_669_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
return v___x_670_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___boxed(lean_object* v_constName_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0(v_constName_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_reduceSparseCasesOn_spec__2(size_t v_sz_712_, size_t v_i_713_, lean_object* v_bs_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
uint8_t v___x_720_; 
v___x_720_ = lean_usize_dec_lt(v_i_713_, v_sz_712_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; 
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v_bs_714_);
return v___x_721_;
}
else
{
lean_object* v_v_722_; lean_object* v___x_723_; 
v_v_722_ = lean_array_uget_borrowed(v_bs_714_, v_i_713_);
lean_inc(v_v_722_);
v___x_723_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0(v_v_722_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v_cidx_725_; lean_object* v___x_726_; lean_object* v_bs_x27_727_; size_t v___x_728_; size_t v___x_729_; lean_object* v___x_730_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_724_);
lean_dec_ref(v___x_723_);
v_cidx_725_ = lean_ctor_get(v_a_724_, 2);
lean_inc(v_cidx_725_);
lean_dec(v_a_724_);
v___x_726_ = lean_unsigned_to_nat(0u);
v_bs_x27_727_ = lean_array_uset(v_bs_714_, v_i_713_, v___x_726_);
v___x_728_ = ((size_t)1ULL);
v___x_729_ = lean_usize_add(v_i_713_, v___x_728_);
v___x_730_ = lean_array_uset(v_bs_x27_727_, v_i_713_, v_cidx_725_);
v_i_713_ = v___x_729_;
v_bs_714_ = v___x_730_;
goto _start;
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_dec_ref(v_bs_714_);
v_a_732_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_723_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_723_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_reduceSparseCasesOn_spec__2___boxed(lean_object* v_sz_740_, lean_object* v_i_741_, lean_object* v_bs_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
size_t v_sz_boxed_748_; size_t v_i_boxed_749_; lean_object* v_res_750_; 
v_sz_boxed_748_ = lean_unbox_usize(v_sz_740_);
lean_dec(v_sz_740_);
v_i_boxed_749_ = lean_unbox_usize(v_i_741_);
lean_dec(v_i_741_);
v_res_750_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_reduceSparseCasesOn_spec__2(v_sz_boxed_748_, v_i_boxed_749_, v_bs_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
return v_res_750_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__0(void){
_start:
{
lean_object* v___x_751_; lean_object* v_dummy_752_; 
v___x_751_ = lean_box(0);
v_dummy_752_ = l_Lean_Expr_sort___override(v___x_751_);
return v_dummy_752_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__2(void){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__1));
v___x_755_ = l_Lean_stringToMessageData(v___x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0(lean_object* v___x_756_, lean_object* v_x_757_, lean_object* v_majorPos_758_, lean_object* v_insterestingCtors_759_, lean_object* v_declName_760_, lean_object* v_snd_761_, lean_object* v_arity_762_, lean_object* v_mvarId_763_, lean_object* v___f_764_, lean_object* v_____r_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = lean_array_get_borrowed(v___x_756_, v_x_757_, v_majorPos_758_);
lean_inc(v___x_771_);
v___x_772_ = l_Lean_Meta_isConstructorApp_x27_x3f(v___x_771_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_a_773_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_a_773_);
lean_dec_ref(v___x_772_);
if (lean_obj_tag(v_a_773_) == 1)
{
lean_object* v_val_774_; lean_object* v_toConstantVal_775_; lean_object* v_cidx_776_; lean_object* v_name_777_; uint8_t v___x_778_; 
v_val_774_ = lean_ctor_get(v_a_773_, 0);
lean_inc(v_val_774_);
lean_dec_ref(v_a_773_);
v_toConstantVal_775_ = lean_ctor_get(v_val_774_, 0);
lean_inc_ref(v_toConstantVal_775_);
v_cidx_776_ = lean_ctor_get(v_val_774_, 2);
lean_inc(v_cidx_776_);
lean_dec(v_val_774_);
v_name_777_ = lean_ctor_get(v_toConstantVal_775_, 0);
lean_inc(v_name_777_);
lean_dec_ref(v_toConstantVal_775_);
v___x_778_ = l_Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1(v_insterestingCtors_759_, v_name_777_);
lean_dec(v_name_777_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; 
lean_dec_ref(v___f_764_);
v___x_779_ = l_Lean_Meta_getSparseCasesOnEq(v_declName_760_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; size_t v_sz_781_; size_t v___x_782_; lean_object* v___x_783_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_a_780_);
lean_dec_ref(v___x_779_);
v_sz_781_ = lean_array_size(v_insterestingCtors_759_);
v___x_782_ = ((size_t)0ULL);
v___x_783_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_reduceSparseCasesOn_spec__2(v_sz_781_, v___x_782_, v_insterestingCtors_759_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_784_);
lean_dec_ref(v___x_783_);
v___x_785_ = l_Lean_mkRawNatLit(v_cidx_776_);
v___x_786_ = l_mkHasNotBitProof(v___x_785_, v_a_784_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec(v_a_784_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; lean_object* v___x_788_; lean_object* v_nargs_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v_dummy_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_a_787_);
lean_dec_ref(v___x_786_);
v___x_788_ = l_Lean_Expr_getAppFn(v_snd_761_);
v_nargs_789_ = l_Lean_Expr_getAppNumArgs(v_snd_761_);
v___x_790_ = l_Lean_Expr_constLevels_x21(v___x_788_);
lean_dec_ref(v___x_788_);
v___x_791_ = l_Lean_mkConst(v_a_780_, v___x_790_);
v_dummy_792_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__0);
lean_inc(v_nargs_789_);
v___x_793_ = lean_mk_array(v_nargs_789_, v_dummy_792_);
v___x_794_ = lean_unsigned_to_nat(1u);
v___x_795_ = lean_nat_sub(v_nargs_789_, v___x_794_);
lean_dec(v_nargs_789_);
v___x_796_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_snd_761_, v___x_793_, v___x_795_);
v___x_797_ = lean_unsigned_to_nat(0u);
v___x_798_ = l_Array_toSubarray___redArg(v___x_796_, v___x_797_, v_arity_762_);
v___x_799_ = l_Subarray_copy___redArg(v___x_798_);
v___x_800_ = l_Lean_mkAppN(v___x_791_, v___x_799_);
lean_dec_ref(v___x_799_);
v___x_801_ = l_Lean_Expr_app___override(v___x_800_, v_a_787_);
v___x_802_ = l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq(v_mvarId_763_, v___x_801_, v___x_778_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_812_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_812_ == 0)
{
v___x_805_ = v___x_802_;
v_isShared_806_ = v_isSharedCheck_812_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_802_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_812_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_807_ = lean_mk_empty_array_with_capacity(v___x_794_);
v___x_808_ = lean_array_push(v___x_807_, v_a_803_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v___x_808_);
v___x_810_ = v___x_805_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
else
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
v_a_813_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_802_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_802_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_813_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
else
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
lean_dec(v_a_780_);
lean_dec(v_mvarId_763_);
lean_dec(v_arity_762_);
lean_dec_ref(v_snd_761_);
v_a_821_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_786_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_786_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
lean_dec(v_a_780_);
lean_dec(v_cidx_776_);
lean_dec(v_mvarId_763_);
lean_dec(v_arity_762_);
lean_dec_ref(v_snd_761_);
v_a_829_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_783_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_783_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
else
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
lean_dec(v_cidx_776_);
lean_dec(v_mvarId_763_);
lean_dec(v_arity_762_);
lean_dec_ref(v_snd_761_);
lean_dec_ref(v_insterestingCtors_759_);
v_a_837_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_779_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_779_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
else
{
lean_object* v___x_845_; 
lean_dec(v_cidx_776_);
lean_dec(v_arity_762_);
lean_dec_ref(v_snd_761_);
lean_dec(v_declName_760_);
lean_dec_ref(v_insterestingCtors_759_);
v___x_845_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_763_, v___f_764_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_856_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_856_ == 0)
{
v___x_848_ = v___x_845_;
v_isShared_849_ = v_isSharedCheck_856_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_845_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_856_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_854_; 
v___x_850_ = lean_unsigned_to_nat(1u);
v___x_851_ = lean_mk_empty_array_with_capacity(v___x_850_);
v___x_852_ = lean_array_push(v___x_851_, v_a_846_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v___x_852_);
v___x_854_ = v___x_848_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_852_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
else
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
v_a_857_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v___x_845_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_845_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_a_857_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
}
else
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
lean_dec(v_a_773_);
lean_dec_ref(v___f_764_);
lean_dec(v_mvarId_763_);
lean_dec(v_arity_762_);
lean_dec_ref(v_snd_761_);
lean_dec(v_declName_760_);
lean_dec_ref(v_insterestingCtors_759_);
v___x_865_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__2);
lean_inc(v___x_771_);
v___x_866_ = l_Lean_indentExpr(v___x_771_);
v___x_867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_865_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v___x_868_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_867_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
return v___x_868_;
}
}
else
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
lean_dec_ref(v___f_764_);
lean_dec(v_mvarId_763_);
lean_dec(v_arity_762_);
lean_dec_ref(v_snd_761_);
lean_dec(v_declName_760_);
lean_dec_ref(v_insterestingCtors_759_);
v_a_869_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_772_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_772_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___boxed(lean_object* v___x_877_, lean_object* v_x_878_, lean_object* v_majorPos_879_, lean_object* v_insterestingCtors_880_, lean_object* v_declName_881_, lean_object* v_snd_882_, lean_object* v_arity_883_, lean_object* v_mvarId_884_, lean_object* v___f_885_, lean_object* v_____r_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0(v___x_877_, v_x_878_, v_majorPos_879_, v_insterestingCtors_880_, v_declName_881_, v_snd_882_, v_arity_883_, v_mvarId_884_, v___f_885_, v_____r_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v_majorPos_879_);
lean_dec_ref(v_x_878_);
return v_res_892_;
}
}
static double _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__7(void){
_start:
{
lean_object* v___x_903_; double v___x_904_; 
v___x_903_ = lean_unsigned_to_nat(1000000000u);
v___x_904_ = lean_float_of_nat(v___x_903_);
return v___x_904_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__9(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__8));
v___x_907_ = l_Lean_stringToMessageData(v___x_906_);
return v___x_907_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__11(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__10));
v___x_910_ = l_Lean_stringToMessageData(v___x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8(lean_object* v_snd_911_, lean_object* v_mvarId_912_, lean_object* v_x_913_, lean_object* v_x_914_, lean_object* v_x_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
if (lean_obj_tag(v_x_913_) == 5)
{
lean_object* v_fn_921_; lean_object* v_arg_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v_fn_921_ = lean_ctor_get(v_x_913_, 0);
lean_inc_ref(v_fn_921_);
v_arg_922_ = lean_ctor_get(v_x_913_, 1);
lean_inc_ref(v_arg_922_);
lean_dec_ref(v_x_913_);
v___x_923_ = lean_array_set(v_x_914_, v_x_915_, v_arg_922_);
v___x_924_ = lean_unsigned_to_nat(1u);
v___x_925_ = lean_nat_sub(v_x_915_, v___x_924_);
lean_dec(v_x_915_);
v_x_913_ = v_fn_921_;
v_x_914_ = v___x_923_;
v_x_915_ = v___x_925_;
goto _start;
}
else
{
lean_dec(v_x_915_);
if (lean_obj_tag(v_x_913_) == 4)
{
lean_object* v_declName_927_; lean_object* v___x_928_; 
v_declName_927_ = lean_ctor_get(v_x_913_, 0);
lean_inc(v_declName_927_);
lean_dec_ref(v_x_913_);
lean_inc(v_declName_927_);
v___x_928_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_declName_927_, v___y_919_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
lean_dec_ref(v___x_928_);
if (lean_obj_tag(v_a_929_) == 1)
{
lean_object* v_val_930_; lean_object* v_options_931_; lean_object* v_majorPos_932_; lean_object* v_arity_933_; lean_object* v_insterestingCtors_934_; uint8_t v_hasTrace_935_; lean_object* v___f_936_; lean_object* v___x_937_; lean_object* v___f_938_; lean_object* v___x_939_; uint8_t v___x_940_; 
v_val_930_ = lean_ctor_get(v_a_929_, 0);
lean_inc(v_val_930_);
lean_dec_ref(v_a_929_);
v_options_931_ = lean_ctor_get(v___y_918_, 2);
v_majorPos_932_ = lean_ctor_get(v_val_930_, 1);
lean_inc(v_majorPos_932_);
v_arity_933_ = lean_ctor_get(v_val_930_, 2);
lean_inc(v_arity_933_);
v_insterestingCtors_934_ = lean_ctor_get(v_val_930_, 3);
lean_inc_ref(v_insterestingCtors_934_);
lean_dec(v_val_930_);
v_hasTrace_935_ = lean_ctor_get_uint8(v_options_931_, sizeof(void*)*1);
v___f_936_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__0));
v___x_937_ = l_Lean_instInhabitedExpr;
lean_inc(v_arity_933_);
lean_inc_ref(v_x_914_);
v___f_938_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___boxed), 15, 9);
lean_closure_set(v___f_938_, 0, v___x_937_);
lean_closure_set(v___f_938_, 1, v_x_914_);
lean_closure_set(v___f_938_, 2, v_majorPos_932_);
lean_closure_set(v___f_938_, 3, v_insterestingCtors_934_);
lean_closure_set(v___f_938_, 4, v_declName_927_);
lean_closure_set(v___f_938_, 5, v_snd_911_);
lean_closure_set(v___f_938_, 6, v_arity_933_);
lean_closure_set(v___f_938_, 7, v_mvarId_912_);
lean_closure_set(v___f_938_, 8, v___f_936_);
v___x_939_ = lean_array_get_size(v_x_914_);
lean_dec_ref(v_x_914_);
v___x_940_ = lean_nat_dec_lt(v___x_939_, v_arity_933_);
lean_dec(v_arity_933_);
if (v_hasTrace_935_ == 0)
{
lean_object* v___x_941_; 
v___x_941_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1(v___x_940_, v___f_938_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
return v___x_941_;
}
else
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v_a_944_; lean_object* v___f_945_; lean_object* v___x_946_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v_a_950_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v_a_966_; uint8_t v___x_1017_; 
v___x_942_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__4));
v___x_943_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___x_942_, v___y_918_);
v_a_944_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_a_944_);
lean_dec_ref(v___x_943_);
v___f_945_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__5));
v___x_946_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__6));
v___x_1017_ = lean_unbox(v_a_944_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; uint8_t v___x_1019_; 
v___x_1018_ = l_Lean_trace_profiler;
v___x_1019_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v_options_931_, v___x_1018_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; 
lean_dec(v_a_944_);
v___x_1020_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1(v___x_940_, v___f_938_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
return v___x_1020_;
}
else
{
goto v___jp_976_;
}
}
else
{
goto v___jp_976_;
}
v___jp_947_:
{
lean_object* v___x_951_; double v___x_952_; double v___x_953_; double v___x_954_; double v___x_955_; double v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; uint8_t v___x_961_; lean_object* v___x_962_; 
v___x_951_ = lean_io_mono_nanos_now();
v___x_952_ = lean_float_of_nat(v___y_949_);
v___x_953_ = lean_float_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__7);
v___x_954_ = lean_float_div(v___x_952_, v___x_953_);
v___x_955_ = lean_float_of_nat(v___x_951_);
v___x_956_ = lean_float_div(v___x_955_, v___x_953_);
v___x_957_ = lean_box_float(v___x_954_);
v___x_958_ = lean_box_float(v___x_956_);
v___x_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_957_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_960_, 0, v_a_950_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
v___x_961_ = lean_unbox(v_a_944_);
lean_dec(v_a_944_);
v___x_962_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7(v___x_942_, v_hasTrace_935_, v___x_946_, v_options_931_, v___x_961_, v___y_948_, v___f_945_, v___x_960_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
return v___x_962_;
}
v___jp_963_:
{
lean_object* v___x_967_; double v___x_968_; double v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; uint8_t v___x_974_; lean_object* v___x_975_; 
v___x_967_ = lean_io_get_num_heartbeats();
v___x_968_ = lean_float_of_nat(v___y_965_);
v___x_969_ = lean_float_of_nat(v___x_967_);
v___x_970_ = lean_box_float(v___x_968_);
v___x_971_ = lean_box_float(v___x_969_);
v___x_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_973_, 0, v_a_966_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = lean_unbox(v_a_944_);
lean_dec(v_a_944_);
v___x_975_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7(v___x_942_, v_hasTrace_935_, v___x_946_, v_options_931_, v___x_974_, v___y_964_, v___f_945_, v___x_973_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
return v___x_975_;
}
v___jp_976_:
{
lean_object* v___x_977_; lean_object* v_a_978_; lean_object* v___x_979_; uint8_t v___x_980_; 
v___x_977_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__5___redArg(v___y_919_);
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_978_);
lean_dec_ref(v___x_977_);
v___x_979_ = l_Lean_trace_profiler_useHeartbeats;
v___x_980_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v_options_931_, v___x_979_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = lean_io_mono_nanos_now();
v___x_982_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1(v___x_940_, v___f_938_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_982_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_982_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
lean_ctor_set_tag(v___x_985_, 1);
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
v___y_948_ = v_a_978_;
v___y_949_ = v___x_981_;
v_a_950_ = v___x_988_;
goto v___jp_947_;
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
v_a_991_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_982_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_982_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
lean_ctor_set_tag(v___x_993_, 0);
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
v___y_948_ = v_a_978_;
v___y_949_ = v___x_981_;
v_a_950_ = v___x_996_;
goto v___jp_947_;
}
}
}
}
else
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = lean_io_get_num_heartbeats();
v___x_1000_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1(v___x_940_, v___f_938_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_1000_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_1000_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
lean_ctor_set_tag(v___x_1003_, 1);
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
v___y_964_ = v_a_978_;
v___y_965_ = v___x_999_;
v_a_966_ = v___x_1006_;
goto v___jp_963_;
}
}
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
v_a_1009_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_1000_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1000_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
lean_ctor_set_tag(v___x_1011_, 0);
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
v___y_964_ = v_a_978_;
v___y_965_ = v___x_999_;
v_a_966_ = v___x_1014_;
goto v___jp_963_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
lean_dec(v_a_929_);
lean_dec(v_declName_927_);
lean_dec_ref(v_x_914_);
lean_dec(v_mvarId_912_);
lean_dec_ref(v_snd_911_);
v___x_1021_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__9, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__9_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__9);
v___x_1022_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1021_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
return v___x_1022_;
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec(v_declName_927_);
lean_dec_ref(v_x_914_);
lean_dec(v_mvarId_912_);
lean_dec_ref(v_snd_911_);
v_a_1023_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_928_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_928_);
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
else
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
lean_dec_ref(v_x_914_);
lean_dec_ref(v_x_913_);
lean_dec(v_mvarId_912_);
lean_dec_ref(v_snd_911_);
v___x_1031_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__11, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__11_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__11);
v___x_1032_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1031_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
return v___x_1032_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___boxed(lean_object* v_snd_1033_, lean_object* v_mvarId_1034_, lean_object* v_x_1035_, lean_object* v_x_1036_, lean_object* v_x_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8(v_snd_1033_, v_mvarId_1034_, v_x_1035_, v_x_1036_, v_x_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
return v_res_1043_;
}
}
static lean_object* _init_l_Lean_Meta_reduceSparseCasesOn___closed__1(void){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = ((lean_object*)(l_Lean_Meta_reduceSparseCasesOn___closed__0));
v___x_1046_ = l_Lean_stringToMessageData(v___x_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceSparseCasesOn(lean_object* v_mvarId_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_){
_start:
{
lean_object* v___x_1053_; 
lean_inc(v_mvarId_1047_);
v___x_1053_ = l_Lean_MVarId_getType(v_mvarId_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v___x_1055_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_a_1054_);
lean_dec_ref(v___x_1053_);
v___x_1055_ = l_Lean_Meta_matchEqHEqLHS_x3f(v_a_1054_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v_a_1056_; 
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
lean_inc(v_a_1056_);
lean_dec_ref(v___x_1055_);
if (lean_obj_tag(v_a_1056_) == 1)
{
lean_object* v_val_1057_; lean_object* v_snd_1058_; lean_object* v_dummy_1059_; lean_object* v_nargs_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v_val_1057_ = lean_ctor_get(v_a_1056_, 0);
lean_inc(v_val_1057_);
lean_dec_ref(v_a_1056_);
v_snd_1058_ = lean_ctor_get(v_val_1057_, 1);
lean_inc(v_snd_1058_);
lean_dec(v_val_1057_);
v_dummy_1059_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__0);
v_nargs_1060_ = l_Lean_Expr_getAppNumArgs(v_snd_1058_);
lean_inc(v_nargs_1060_);
v___x_1061_ = lean_mk_array(v_nargs_1060_, v_dummy_1059_);
v___x_1062_ = lean_unsigned_to_nat(1u);
v___x_1063_ = lean_nat_sub(v_nargs_1060_, v___x_1062_);
lean_dec(v_nargs_1060_);
lean_inc(v_snd_1058_);
v___x_1064_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8(v_snd_1058_, v_mvarId_1047_, v_snd_1058_, v___x_1061_, v___x_1063_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
return v___x_1064_;
}
else
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
lean_dec(v_a_1056_);
lean_dec(v_mvarId_1047_);
v___x_1065_ = lean_obj_once(&l_Lean_Meta_reduceSparseCasesOn___closed__1, &l_Lean_Meta_reduceSparseCasesOn___closed__1_once, _init_l_Lean_Meta_reduceSparseCasesOn___closed__1);
v___x_1066_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1065_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
return v___x_1066_;
}
}
else
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
lean_dec(v_mvarId_1047_);
v_a_1067_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1069_ = v___x_1055_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1055_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_a_1067_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
lean_dec(v_mvarId_1047_);
v_a_1075_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1053_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1053_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceSparseCasesOn___boxed(lean_object* v_mvarId_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Lean_Meta_reduceSparseCasesOn(v_mvarId_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
lean_dec(v_a_1087_);
lean_dec_ref(v_a_1086_);
lean_dec(v_a_1085_);
lean_dec_ref(v_a_1084_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3(lean_object* v_00_u03b1_1090_, lean_object* v_msg_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v_msg_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___boxed(lean_object* v_00_u03b1_1098_, lean_object* v_msg_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3(v_00_u03b1_1098_, v_msg_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__12(lean_object* v_00_u03b1_1106_, lean_object* v_x_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v___x_1113_; 
v___x_1113_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__12___redArg(v_x_1107_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__12___boxed(lean_object* v_00_u03b1_1114_, lean_object* v_x_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__12(v_00_u03b1_1114_, v_x_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(lean_object* v_mvarId_1122_, lean_object* v_x_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v___x_1129_; 
v___x_1129_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1122_, v_x_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1129_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1129_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
else
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
v_a_1138_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1140_ = v___x_1129_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1129_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1141_ == 0)
{
v___x_1143_ = v___x_1140_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_a_1138_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg___boxed(lean_object* v_mvarId_1146_, lean_object* v_x_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1146_, v_x_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2(lean_object* v_00_u03b1_1154_, lean_object* v_mvarId_1155_, lean_object* v_x_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1155_, v_x_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___boxed(lean_object* v_00_u03b1_1163_, lean_object* v_mvarId_1164_, lean_object* v_x_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2(v_00_u03b1_1163_, v_mvarId_1164_, v_x_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_splitSparseCasesOn_spec__1(lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
if (lean_obj_tag(v_a_1172_) == 0)
{
lean_object* v___x_1174_; 
v___x_1174_ = l_List_reverse___redArg(v_a_1173_);
return v___x_1174_;
}
else
{
lean_object* v_head_1175_; lean_object* v_tail_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1185_; 
v_head_1175_ = lean_ctor_get(v_a_1172_, 0);
v_tail_1176_ = lean_ctor_get(v_a_1172_, 1);
v_isSharedCheck_1185_ = !lean_is_exclusive(v_a_1172_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1178_ = v_a_1172_;
v_isShared_1179_ = v_isSharedCheck_1185_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_tail_1176_);
lean_inc(v_head_1175_);
lean_dec(v_a_1172_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1185_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; lean_object* v___x_1182_; 
v___x_1180_ = l_Lean_MessageData_ofExpr(v_head_1175_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 1, v_a_1173_);
lean_ctor_set(v___x_1178_, 0, v___x_1180_);
v___x_1182_ = v___x_1178_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1180_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_a_1173_);
v___x_1182_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
v_a_1172_ = v_tail_1176_;
v_a_1173_ = v___x_1182_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__0));
v___x_1188_ = l_Lean_stringToMessageData(v___x_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0(uint8_t v___y_1189_, lean_object* v_mvarId_1190_, lean_object* v___f_1191_, lean_object* v_declName_1192_, lean_object* v_val_1193_, lean_object* v___x_1194_, lean_object* v_fields_1195_, uint8_t v___x_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1206_; 
if (v___y_1189_ == 0)
{
lean_object* v___x_1258_; 
lean_dec_ref(v_fields_1195_);
lean_dec_ref(v___x_1194_);
lean_dec_ref(v_val_1193_);
lean_dec(v_declName_1192_);
v___x_1258_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_1190_, v___f_1191_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
return v___x_1258_;
}
else
{
lean_object* v___x_1259_; lean_object* v___x_1260_; uint8_t v___x_1261_; 
lean_dec_ref(v___f_1191_);
v___x_1259_ = lean_array_get_size(v_fields_1195_);
v___x_1260_ = lean_unsigned_to_nat(1u);
v___x_1261_ = lean_nat_dec_eq(v___x_1259_, v___x_1260_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1262_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1);
lean_inc_ref(v_fields_1195_);
v___x_1263_ = lean_array_to_list(v_fields_1195_);
v___x_1264_ = lean_box(0);
v___x_1265_ = l_List_mapTR_loop___at___00Lean_Meta_splitSparseCasesOn_spec__1(v___x_1263_, v___x_1264_);
v___x_1266_ = l_Lean_MessageData_ofList(v___x_1265_);
v___x_1267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1262_);
lean_ctor_set(v___x_1267_, 1, v___x_1266_);
v___x_1268_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1267_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_dec_ref(v___x_1268_);
v___y_1203_ = v___y_1197_;
v___y_1204_ = v___y_1198_;
v___y_1205_ = v___y_1199_;
v___y_1206_ = v___y_1200_;
goto v___jp_1202_;
}
else
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
lean_dec_ref(v_fields_1195_);
lean_dec_ref(v___x_1194_);
lean_dec_ref(v_val_1193_);
lean_dec(v_declName_1192_);
lean_dec(v_mvarId_1190_);
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1268_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1268_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
else
{
v___y_1203_ = v___y_1197_;
v___y_1204_ = v___y_1198_;
v___y_1205_ = v___y_1199_;
v___y_1206_ = v___y_1200_;
goto v___jp_1202_;
}
}
v___jp_1202_:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Lean_Meta_getSparseCasesOnEq(v_declName_1192_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_object* v_a_1208_; lean_object* v___x_1209_; 
v_a_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_a_1208_);
lean_dec_ref(v___x_1207_);
lean_inc(v_mvarId_1190_);
v___x_1209_ = l_Lean_MVarId_getType(v_mvarId_1190_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; lean_object* v___x_1211_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_a_1210_);
lean_dec_ref(v___x_1209_);
v___x_1211_ = l_Lean_Meta_matchEqHEqLHS_x3f(v_a_1210_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; 
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_a_1212_);
lean_dec_ref(v___x_1211_);
if (lean_obj_tag(v_a_1212_) == 1)
{
lean_object* v_val_1213_; lean_object* v_snd_1214_; lean_object* v_arity_1215_; lean_object* v___x_1216_; lean_object* v_nargs_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v_dummy_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v_val_1213_ = lean_ctor_get(v_a_1212_, 0);
lean_inc(v_val_1213_);
lean_dec_ref(v_a_1212_);
v_snd_1214_ = lean_ctor_get(v_val_1213_, 1);
lean_inc(v_snd_1214_);
lean_dec(v_val_1213_);
v_arity_1215_ = lean_ctor_get(v_val_1193_, 2);
lean_inc(v_arity_1215_);
lean_dec_ref(v_val_1193_);
v___x_1216_ = l_Lean_Expr_getAppFn(v_snd_1214_);
v_nargs_1217_ = l_Lean_Expr_getAppNumArgs(v_snd_1214_);
v___x_1218_ = l_Lean_Expr_constLevels_x21(v___x_1216_);
lean_dec_ref(v___x_1216_);
v___x_1219_ = l_Lean_mkConst(v_a_1208_, v___x_1218_);
v_dummy_1220_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__0);
lean_inc(v_nargs_1217_);
v___x_1221_ = lean_mk_array(v_nargs_1217_, v_dummy_1220_);
v___x_1222_ = lean_unsigned_to_nat(1u);
v___x_1223_ = lean_nat_sub(v_nargs_1217_, v___x_1222_);
lean_dec(v_nargs_1217_);
v___x_1224_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_snd_1214_, v___x_1221_, v___x_1223_);
v___x_1225_ = lean_unsigned_to_nat(0u);
v___x_1226_ = l_Array_toSubarray___redArg(v___x_1224_, v___x_1225_, v_arity_1215_);
v___x_1227_ = l_Subarray_copy___redArg(v___x_1226_);
v___x_1228_ = l_Lean_mkAppN(v___x_1219_, v___x_1227_);
lean_dec_ref(v___x_1227_);
v___x_1229_ = lean_array_get(v___x_1194_, v_fields_1195_, v___x_1225_);
lean_dec_ref(v_fields_1195_);
v___x_1230_ = l_Lean_Expr_app___override(v___x_1228_, v___x_1229_);
v___x_1231_ = l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq(v_mvarId_1190_, v___x_1230_, v___x_1196_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
return v___x_1231_;
}
else
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
lean_dec(v_a_1212_);
lean_dec(v_a_1208_);
lean_dec_ref(v_fields_1195_);
lean_dec_ref(v___x_1194_);
lean_dec_ref(v_val_1193_);
lean_dec(v_mvarId_1190_);
v___x_1232_ = lean_obj_once(&l_Lean_Meta_reduceSparseCasesOn___closed__1, &l_Lean_Meta_reduceSparseCasesOn___closed__1_once, _init_l_Lean_Meta_reduceSparseCasesOn___closed__1);
v___x_1233_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1232_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
return v___x_1233_;
}
}
else
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
lean_dec(v_a_1208_);
lean_dec_ref(v_fields_1195_);
lean_dec_ref(v___x_1194_);
lean_dec_ref(v_val_1193_);
lean_dec(v_mvarId_1190_);
v_a_1234_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1236_ = v___x_1211_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1211_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1234_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
else
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
lean_dec(v_a_1208_);
lean_dec_ref(v_fields_1195_);
lean_dec_ref(v___x_1194_);
lean_dec_ref(v_val_1193_);
lean_dec(v_mvarId_1190_);
v_a_1242_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1244_ = v___x_1209_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1209_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1242_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec_ref(v_fields_1195_);
lean_dec_ref(v___x_1194_);
lean_dec_ref(v_val_1193_);
lean_dec(v_mvarId_1190_);
v_a_1250_ = lean_ctor_get(v___x_1207_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1207_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1207_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed(lean_object* v___y_1277_, lean_object* v_mvarId_1278_, lean_object* v___f_1279_, lean_object* v_declName_1280_, lean_object* v_val_1281_, lean_object* v___x_1282_, lean_object* v_fields_1283_, lean_object* v___x_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
uint8_t v___y_29133__boxed_1290_; uint8_t v___x_29138__boxed_1291_; lean_object* v_res_1292_; 
v___y_29133__boxed_1290_ = lean_unbox(v___y_1277_);
v___x_29138__boxed_1291_ = lean_unbox(v___x_1284_);
v_res_1292_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0(v___y_29133__boxed_1290_, v_mvarId_1278_, v___f_1279_, v_declName_1280_, v_val_1281_, v___x_1282_, v_fields_1283_, v___x_29138__boxed_1291_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(lean_object* v_declName_1293_, lean_object* v_val_1294_, uint8_t v___x_1295_, size_t v_sz_1296_, size_t v_i_1297_, lean_object* v_bs_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
uint8_t v___x_1304_; 
v___x_1304_ = lean_usize_dec_lt(v_i_1297_, v_sz_1296_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; 
lean_dec_ref(v_val_1294_);
lean_dec(v_declName_1293_);
v___x_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1305_, 0, v_bs_1298_);
return v___x_1305_;
}
else
{
lean_object* v_v_1306_; lean_object* v_toInductionSubgoal_1307_; lean_object* v_ctorName_1308_; lean_object* v_mvarId_1309_; lean_object* v_fields_1310_; lean_object* v___f_1311_; lean_object* v___x_1312_; uint8_t v___x_1313_; lean_object* v___x_1314_; lean_object* v_bs_x27_1315_; uint8_t v___y_1317_; 
v_v_1306_ = lean_array_uget_borrowed(v_bs_1298_, v_i_1297_);
v_toInductionSubgoal_1307_ = lean_ctor_get(v_v_1306_, 0);
v_ctorName_1308_ = lean_ctor_get(v_v_1306_, 1);
lean_inc(v_ctorName_1308_);
v_mvarId_1309_ = lean_ctor_get(v_toInductionSubgoal_1307_, 0);
lean_inc(v_mvarId_1309_);
v_fields_1310_ = lean_ctor_get(v_toInductionSubgoal_1307_, 1);
lean_inc_ref(v_fields_1310_);
v___f_1311_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__0));
v___x_1312_ = l_Lean_instInhabitedExpr;
v___x_1313_ = 0;
v___x_1314_ = lean_unsigned_to_nat(0u);
v_bs_x27_1315_ = lean_array_uset(v_bs_1298_, v_i_1297_, v___x_1314_);
if (lean_obj_tag(v_ctorName_1308_) == 0)
{
if (v___x_1295_ == 0)
{
goto v___jp_1335_;
}
else
{
v___y_1317_ = v___x_1295_;
goto v___jp_1316_;
}
}
else
{
lean_dec_ref(v_ctorName_1308_);
goto v___jp_1335_;
}
v___jp_1316_:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___y_1320_; lean_object* v___x_1321_; 
v___x_1318_ = lean_box(v___y_1317_);
v___x_1319_ = lean_box(v___x_1313_);
lean_inc_ref(v_val_1294_);
lean_inc(v_declName_1293_);
lean_inc(v_mvarId_1309_);
v___y_1320_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed), 13, 8);
lean_closure_set(v___y_1320_, 0, v___x_1318_);
lean_closure_set(v___y_1320_, 1, v_mvarId_1309_);
lean_closure_set(v___y_1320_, 2, v___f_1311_);
lean_closure_set(v___y_1320_, 3, v_declName_1293_);
lean_closure_set(v___y_1320_, 4, v_val_1294_);
lean_closure_set(v___y_1320_, 5, v___x_1312_);
lean_closure_set(v___y_1320_, 6, v_fields_1310_);
lean_closure_set(v___y_1320_, 7, v___x_1319_);
v___x_1321_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1309_, v___y_1320_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; size_t v___x_1323_; size_t v___x_1324_; lean_object* v___x_1325_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_a_1322_);
lean_dec_ref(v___x_1321_);
v___x_1323_ = ((size_t)1ULL);
v___x_1324_ = lean_usize_add(v_i_1297_, v___x_1323_);
v___x_1325_ = lean_array_uset(v_bs_x27_1315_, v_i_1297_, v_a_1322_);
v_i_1297_ = v___x_1324_;
v_bs_1298_ = v___x_1325_;
goto _start;
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_dec_ref(v_bs_x27_1315_);
lean_dec_ref(v_val_1294_);
lean_dec(v_declName_1293_);
v_a_1327_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1321_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1321_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
v___jp_1335_:
{
v___y_1317_ = v___x_1313_;
goto v___jp_1316_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4___boxed(lean_object* v_declName_1336_, lean_object* v_val_1337_, lean_object* v___x_1338_, lean_object* v_sz_1339_, lean_object* v_i_1340_, lean_object* v_bs_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
uint8_t v___x_29317__boxed_1347_; size_t v_sz_boxed_1348_; size_t v_i_boxed_1349_; lean_object* v_res_1350_; 
v___x_29317__boxed_1347_ = lean_unbox(v___x_1338_);
v_sz_boxed_1348_ = lean_unbox_usize(v_sz_1339_);
lean_dec(v_sz_1339_);
v_i_boxed_1349_ = lean_unbox_usize(v_i_1340_);
lean_dec(v_i_1340_);
v_res_1350_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(v_declName_1336_, v_val_1337_, v___x_29317__boxed_1347_, v_sz_boxed_1348_, v_i_boxed_1349_, v_bs_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
return v_res_1350_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__1));
v___x_1355_ = l_Lean_stringToMessageData(v___x_1354_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1(lean_object* v_val_1356_, lean_object* v___x_1357_, lean_object* v_x_1358_, lean_object* v_mvarId_1359_, lean_object* v_declName_1360_, uint8_t v___x_1361_, lean_object* v_____r_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v_majorPos_1393_; lean_object* v_arity_1394_; lean_object* v_insterestingCtors_1395_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___x_1415_; uint8_t v___x_1416_; 
v_majorPos_1393_ = lean_ctor_get(v_val_1356_, 1);
v_arity_1394_ = lean_ctor_get(v_val_1356_, 2);
v_insterestingCtors_1395_ = lean_ctor_get(v_val_1356_, 3);
v___x_1415_ = lean_array_get_size(v_x_1358_);
v___x_1416_ = lean_nat_dec_lt(v___x_1415_, v_arity_1394_);
if (v___x_1416_ == 0)
{
v___y_1397_ = v___y_1363_;
v___y_1398_ = v___y_1364_;
v___y_1399_ = v___y_1365_;
v___y_1400_ = v___y_1366_;
goto v___jp_1396_;
}
else
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
lean_dec(v_declName_1360_);
lean_dec(v_mvarId_1359_);
lean_dec_ref(v___x_1357_);
lean_dec_ref(v_val_1356_);
v___x_1417_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__1);
v___x_1418_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1417_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1418_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1418_);
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
v___jp_1368_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; uint8_t v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1375_ = lean_array_get_borrowed(v___x_1357_, v_x_1358_, v___y_1369_);
lean_dec(v___y_1369_);
v___x_1376_ = l_Lean_Expr_fvarId_x21(v___x_1375_);
v___x_1377_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__0));
v___x_1378_ = 0;
v___x_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1379_, 0, v___y_1370_);
v___x_1380_ = l_Lean_MVarId_cases(v_mvarId_1359_, v___x_1376_, v___x_1377_, v___x_1378_, v___x_1379_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; size_t v_sz_1382_; size_t v___x_1383_; lean_object* v___x_1384_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_a_1381_);
lean_dec_ref(v___x_1380_);
v_sz_1382_ = lean_array_size(v_a_1381_);
v___x_1383_ = ((size_t)0ULL);
v___x_1384_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(v_declName_1360_, v_val_1356_, v___x_1361_, v_sz_1382_, v___x_1383_, v_a_1381_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
return v___x_1384_;
}
else
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
lean_dec(v_declName_1360_);
lean_dec_ref(v_val_1356_);
v_a_1385_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1387_ = v___x_1380_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1380_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_a_1385_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
}
v___jp_1396_:
{
lean_object* v___x_1401_; uint8_t v___x_1402_; 
lean_inc_ref(v___x_1357_);
v___x_1401_ = lean_array_get_borrowed(v___x_1357_, v_x_1358_, v_majorPos_1393_);
v___x_1402_ = l_Lean_Expr_isFVar(v___x_1401_);
if (v___x_1402_ == 0)
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
lean_dec(v_declName_1360_);
lean_dec(v_mvarId_1359_);
lean_dec_ref(v___x_1357_);
lean_dec_ref(v_val_1356_);
v___x_1403_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2);
lean_inc(v___x_1401_);
v___x_1404_ = l_Lean_indentExpr(v___x_1401_);
v___x_1405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1403_);
lean_ctor_set(v___x_1405_, 1, v___x_1404_);
v___x_1406_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1405_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1406_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1406_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
else
{
lean_inc_ref(v_insterestingCtors_1395_);
lean_inc(v_majorPos_1393_);
v___y_1369_ = v_majorPos_1393_;
v___y_1370_ = v_insterestingCtors_1395_;
v___y_1371_ = v___y_1397_;
v___y_1372_ = v___y_1398_;
v___y_1373_ = v___y_1399_;
v___y_1374_ = v___y_1400_;
goto v___jp_1368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___boxed(lean_object* v_val_1427_, lean_object* v___x_1428_, lean_object* v_x_1429_, lean_object* v_mvarId_1430_, lean_object* v_declName_1431_, lean_object* v___x_1432_, lean_object* v_____r_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
uint8_t v___x_29409__boxed_1439_; lean_object* v_res_1440_; 
v___x_29409__boxed_1439_ = lean_unbox(v___x_1432_);
v_res_1440_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1(v_val_1427_, v___x_1428_, v_x_1429_, v_mvarId_1430_, v_declName_1431_, v___x_29409__boxed_1439_, v_____r_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec_ref(v_x_1429_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(lean_object* v_cls_1443_, lean_object* v_msg_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v_ref_1450_; lean_object* v___x_1451_; lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1496_; 
v_ref_1450_ = lean_ctor_get(v___y_1447_, 5);
v___x_1451_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msg_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1454_ = v___x_1451_;
v_isShared_1455_ = v_isSharedCheck_1496_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1451_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1496_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1456_; lean_object* v_traceState_1457_; lean_object* v_env_1458_; lean_object* v_nextMacroScope_1459_; lean_object* v_ngen_1460_; lean_object* v_auxDeclNGen_1461_; lean_object* v_cache_1462_; lean_object* v_messages_1463_; lean_object* v_infoState_1464_; lean_object* v_snapshotTasks_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1495_; 
v___x_1456_ = lean_st_ref_take(v___y_1448_);
v_traceState_1457_ = lean_ctor_get(v___x_1456_, 4);
v_env_1458_ = lean_ctor_get(v___x_1456_, 0);
v_nextMacroScope_1459_ = lean_ctor_get(v___x_1456_, 1);
v_ngen_1460_ = lean_ctor_get(v___x_1456_, 2);
v_auxDeclNGen_1461_ = lean_ctor_get(v___x_1456_, 3);
v_cache_1462_ = lean_ctor_get(v___x_1456_, 5);
v_messages_1463_ = lean_ctor_get(v___x_1456_, 6);
v_infoState_1464_ = lean_ctor_get(v___x_1456_, 7);
v_snapshotTasks_1465_ = lean_ctor_get(v___x_1456_, 8);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1467_ = v___x_1456_;
v_isShared_1468_ = v_isSharedCheck_1495_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_snapshotTasks_1465_);
lean_inc(v_infoState_1464_);
lean_inc(v_messages_1463_);
lean_inc(v_cache_1462_);
lean_inc(v_traceState_1457_);
lean_inc(v_auxDeclNGen_1461_);
lean_inc(v_ngen_1460_);
lean_inc(v_nextMacroScope_1459_);
lean_inc(v_env_1458_);
lean_dec(v___x_1456_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1495_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
uint64_t v_tid_1469_; lean_object* v_traces_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1494_; 
v_tid_1469_ = lean_ctor_get_uint64(v_traceState_1457_, sizeof(void*)*1);
v_traces_1470_ = lean_ctor_get(v_traceState_1457_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v_traceState_1457_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1472_ = v_traceState_1457_;
v_isShared_1473_ = v_isSharedCheck_1494_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_traces_1470_);
lean_dec(v_traceState_1457_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1494_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1474_; double v___x_1475_; uint8_t v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1484_; 
v___x_1474_ = lean_box(0);
v___x_1475_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__2);
v___x_1476_ = 0;
v___x_1477_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__6));
v___x_1478_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1478_, 0, v_cls_1443_);
lean_ctor_set(v___x_1478_, 1, v___x_1474_);
lean_ctor_set(v___x_1478_, 2, v___x_1477_);
lean_ctor_set_float(v___x_1478_, sizeof(void*)*3, v___x_1475_);
lean_ctor_set_float(v___x_1478_, sizeof(void*)*3 + 8, v___x_1475_);
lean_ctor_set_uint8(v___x_1478_, sizeof(void*)*3 + 16, v___x_1476_);
v___x_1479_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___closed__0));
v___x_1480_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1478_);
lean_ctor_set(v___x_1480_, 1, v_a_1452_);
lean_ctor_set(v___x_1480_, 2, v___x_1479_);
lean_inc(v_ref_1450_);
v___x_1481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1481_, 0, v_ref_1450_);
lean_ctor_set(v___x_1481_, 1, v___x_1480_);
v___x_1482_ = l_Lean_PersistentArray_push___redArg(v_traces_1470_, v___x_1481_);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 0, v___x_1482_);
v___x_1484_ = v___x_1472_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1482_);
lean_ctor_set_uint64(v_reuseFailAlloc_1493_, sizeof(void*)*1, v_tid_1469_);
v___x_1484_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1486_; 
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 4, v___x_1484_);
v___x_1486_ = v___x_1467_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_env_1458_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v_nextMacroScope_1459_);
lean_ctor_set(v_reuseFailAlloc_1492_, 2, v_ngen_1460_);
lean_ctor_set(v_reuseFailAlloc_1492_, 3, v_auxDeclNGen_1461_);
lean_ctor_set(v_reuseFailAlloc_1492_, 4, v___x_1484_);
lean_ctor_set(v_reuseFailAlloc_1492_, 5, v_cache_1462_);
lean_ctor_set(v_reuseFailAlloc_1492_, 6, v_messages_1463_);
lean_ctor_set(v_reuseFailAlloc_1492_, 7, v_infoState_1464_);
lean_ctor_set(v_reuseFailAlloc_1492_, 8, v_snapshotTasks_1465_);
v___x_1486_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1490_; 
v___x_1487_ = lean_st_ref_set(v___y_1448_, v___x_1486_);
v___x_1488_ = lean_box(0);
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 0, v___x_1488_);
v___x_1490_ = v___x_1454_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1488_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___boxed(lean_object* v_cls_1497_, lean_object* v_msg_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v_cls_1497_, v_msg_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(lean_object* v_declName_1505_, lean_object* v_val_1506_, uint8_t v___x_1507_, size_t v_sz_1508_, size_t v_i_1509_, lean_object* v_bs_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
uint8_t v___x_1516_; 
v___x_1516_ = lean_usize_dec_lt(v_i_1509_, v_sz_1508_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; 
lean_dec_ref(v_val_1506_);
lean_dec(v_declName_1505_);
v___x_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1517_, 0, v_bs_1510_);
return v___x_1517_;
}
else
{
lean_object* v_v_1518_; lean_object* v_toInductionSubgoal_1519_; lean_object* v_ctorName_1520_; lean_object* v_mvarId_1521_; lean_object* v_fields_1522_; lean_object* v___f_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v_bs_x27_1526_; uint8_t v___y_1528_; 
v_v_1518_ = lean_array_uget_borrowed(v_bs_1510_, v_i_1509_);
v_toInductionSubgoal_1519_ = lean_ctor_get(v_v_1518_, 0);
v_ctorName_1520_ = lean_ctor_get(v_v_1518_, 1);
lean_inc(v_ctorName_1520_);
v_mvarId_1521_ = lean_ctor_get(v_toInductionSubgoal_1519_, 0);
lean_inc(v_mvarId_1521_);
v_fields_1522_ = lean_ctor_get(v_toInductionSubgoal_1519_, 1);
lean_inc_ref(v_fields_1522_);
v___f_1523_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__0));
v___x_1524_ = l_Lean_instInhabitedExpr;
v___x_1525_ = lean_unsigned_to_nat(0u);
v_bs_x27_1526_ = lean_array_uset(v_bs_1510_, v_i_1509_, v___x_1525_);
if (lean_obj_tag(v_ctorName_1520_) == 0)
{
v___y_1528_ = v___x_1516_;
goto v___jp_1527_;
}
else
{
lean_dec_ref(v_ctorName_1520_);
if (v___x_1507_ == 0)
{
v___y_1528_ = v___x_1507_;
goto v___jp_1527_;
}
else
{
v___y_1528_ = v___x_1516_;
goto v___jp_1527_;
}
}
v___jp_1527_:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___y_1531_; lean_object* v___x_1532_; 
v___x_1529_ = lean_box(v___y_1528_);
v___x_1530_ = lean_box(v___x_1507_);
lean_inc_ref(v_val_1506_);
lean_inc(v_declName_1505_);
lean_inc(v_mvarId_1521_);
v___y_1531_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed), 13, 8);
lean_closure_set(v___y_1531_, 0, v___x_1529_);
lean_closure_set(v___y_1531_, 1, v_mvarId_1521_);
lean_closure_set(v___y_1531_, 2, v___f_1523_);
lean_closure_set(v___y_1531_, 3, v_declName_1505_);
lean_closure_set(v___y_1531_, 4, v_val_1506_);
lean_closure_set(v___y_1531_, 5, v___x_1524_);
lean_closure_set(v___y_1531_, 6, v_fields_1522_);
lean_closure_set(v___y_1531_, 7, v___x_1530_);
v___x_1532_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1521_, v___y_1531_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; size_t v___x_1534_; size_t v___x_1535_; lean_object* v___x_1536_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_a_1533_);
lean_dec_ref(v___x_1532_);
v___x_1534_ = ((size_t)1ULL);
v___x_1535_ = lean_usize_add(v_i_1509_, v___x_1534_);
v___x_1536_ = lean_array_uset(v_bs_x27_1526_, v_i_1509_, v_a_1533_);
v_i_1509_ = v___x_1535_;
v_bs_1510_ = v___x_1536_;
goto _start;
}
else
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
lean_dec_ref(v_bs_x27_1526_);
lean_dec_ref(v_val_1506_);
lean_dec(v_declName_1505_);
v_a_1538_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1540_ = v___x_1532_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1532_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___boxed(lean_object* v_declName_1546_, lean_object* v_val_1547_, lean_object* v___x_1548_, lean_object* v_sz_1549_, lean_object* v_i_1550_, lean_object* v_bs_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
uint8_t v___x_29653__boxed_1557_; size_t v_sz_boxed_1558_; size_t v_i_boxed_1559_; lean_object* v_res_1560_; 
v___x_29653__boxed_1557_ = lean_unbox(v___x_1548_);
v_sz_boxed_1558_ = lean_unbox_usize(v_sz_1549_);
lean_dec(v_sz_1549_);
v_i_boxed_1559_ = lean_unbox_usize(v_i_1550_);
lean_dec(v_i_1550_);
v_res_1560_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(v_declName_1546_, v_val_1547_, v___x_29653__boxed_1557_, v_sz_boxed_1558_, v_i_boxed_1559_, v_bs_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__2(lean_object* v_val_1561_, lean_object* v___x_1562_, lean_object* v_x_1563_, lean_object* v_mvarId_1564_, uint8_t v___x_1565_, lean_object* v_declName_1566_, lean_object* v_____r_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v_majorPos_1597_; lean_object* v_arity_1598_; lean_object* v_insterestingCtors_1599_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___x_1619_; uint8_t v___x_1620_; 
v_majorPos_1597_ = lean_ctor_get(v_val_1561_, 1);
v_arity_1598_ = lean_ctor_get(v_val_1561_, 2);
v_insterestingCtors_1599_ = lean_ctor_get(v_val_1561_, 3);
v___x_1619_ = lean_array_get_size(v_x_1563_);
v___x_1620_ = lean_nat_dec_lt(v___x_1619_, v_arity_1598_);
if (v___x_1620_ == 0)
{
v___y_1601_ = v___y_1568_;
v___y_1602_ = v___y_1569_;
v___y_1603_ = v___y_1570_;
v___y_1604_ = v___y_1571_;
goto v___jp_1600_;
}
else
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
lean_dec(v_declName_1566_);
lean_dec(v_mvarId_1564_);
lean_dec_ref(v___x_1562_);
lean_dec_ref(v_val_1561_);
v___x_1621_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__1);
v___x_1622_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1621_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___x_1622_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1622_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1623_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
v___jp_1573_:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1580_ = lean_array_get_borrowed(v___x_1562_, v_x_1563_, v___y_1575_);
lean_dec(v___y_1575_);
v___x_1581_ = l_Lean_Expr_fvarId_x21(v___x_1580_);
v___x_1582_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__0));
v___x_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1583_, 0, v___y_1574_);
v___x_1584_ = l_Lean_MVarId_cases(v_mvarId_1564_, v___x_1581_, v___x_1582_, v___x_1565_, v___x_1583_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; size_t v_sz_1586_; size_t v___x_1587_; lean_object* v___x_1588_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref(v___x_1584_);
v_sz_1586_ = lean_array_size(v_a_1585_);
v___x_1587_ = ((size_t)0ULL);
v___x_1588_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(v_declName_1566_, v_val_1561_, v___x_1565_, v_sz_1586_, v___x_1587_, v_a_1585_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
return v___x_1588_;
}
else
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
lean_dec(v_declName_1566_);
lean_dec_ref(v_val_1561_);
v_a_1589_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1584_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1584_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
v___jp_1600_:
{
lean_object* v___x_1605_; uint8_t v___x_1606_; 
lean_inc_ref(v___x_1562_);
v___x_1605_ = lean_array_get_borrowed(v___x_1562_, v_x_1563_, v_majorPos_1597_);
v___x_1606_ = l_Lean_Expr_isFVar(v___x_1605_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
lean_dec(v_declName_1566_);
lean_dec(v_mvarId_1564_);
lean_dec_ref(v___x_1562_);
lean_dec_ref(v_val_1561_);
v___x_1607_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2);
lean_inc(v___x_1605_);
v___x_1608_ = l_Lean_indentExpr(v___x_1605_);
v___x_1609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1607_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
v___x_1610_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1609_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_);
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1610_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1610_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
else
{
lean_inc(v_majorPos_1597_);
lean_inc_ref(v_insterestingCtors_1599_);
v___y_1574_ = v_insterestingCtors_1599_;
v___y_1575_ = v_majorPos_1597_;
v___y_1576_ = v___y_1601_;
v___y_1577_ = v___y_1602_;
v___y_1578_ = v___y_1603_;
v___y_1579_ = v___y_1604_;
goto v___jp_1573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__2___boxed(lean_object* v_val_1631_, lean_object* v___x_1632_, lean_object* v_x_1633_, lean_object* v_mvarId_1634_, lean_object* v___x_1635_, lean_object* v_declName_1636_, lean_object* v_____r_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
uint8_t v___x_29734__boxed_1643_; lean_object* v_res_1644_; 
v___x_29734__boxed_1643_ = lean_unbox(v___x_1635_);
v_res_1644_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__2(v_val_1631_, v___x_1632_, v_x_1633_, v_mvarId_1634_, v___x_29734__boxed_1643_, v_declName_1636_, v_____r_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec_ref(v_x_1633_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__3(lean_object* v_val_1645_, lean_object* v___x_1646_, lean_object* v_x_1647_, lean_object* v_mvarId_1648_, uint8_t v___x_1649_, lean_object* v_declName_1650_, lean_object* v_____r_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v_majorPos_1681_; lean_object* v_arity_1682_; lean_object* v_insterestingCtors_1683_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___x_1703_; uint8_t v___x_1704_; 
v_majorPos_1681_ = lean_ctor_get(v_val_1645_, 1);
v_arity_1682_ = lean_ctor_get(v_val_1645_, 2);
v_insterestingCtors_1683_ = lean_ctor_get(v_val_1645_, 3);
v___x_1703_ = lean_array_get_size(v_x_1647_);
v___x_1704_ = lean_nat_dec_lt(v___x_1703_, v_arity_1682_);
if (v___x_1704_ == 0)
{
v___y_1685_ = v___y_1652_;
v___y_1686_ = v___y_1653_;
v___y_1687_ = v___y_1654_;
v___y_1688_ = v___y_1655_;
goto v___jp_1684_;
}
else
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
lean_dec(v_declName_1650_);
lean_dec(v_mvarId_1648_);
lean_dec_ref(v___x_1646_);
lean_dec_ref(v_val_1645_);
v___x_1705_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__1);
v___x_1706_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1705_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_);
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1706_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1706_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1707_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
v___jp_1657_:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1664_ = lean_array_get_borrowed(v___x_1646_, v_x_1647_, v___y_1658_);
lean_dec(v___y_1658_);
v___x_1665_ = l_Lean_Expr_fvarId_x21(v___x_1664_);
v___x_1666_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__0));
v___x_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1667_, 0, v___y_1659_);
v___x_1668_ = l_Lean_MVarId_cases(v_mvarId_1648_, v___x_1665_, v___x_1666_, v___x_1649_, v___x_1667_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; size_t v_sz_1670_; size_t v___x_1671_; lean_object* v___x_1672_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
lean_inc(v_a_1669_);
lean_dec_ref(v___x_1668_);
v_sz_1670_ = lean_array_size(v_a_1669_);
v___x_1671_ = ((size_t)0ULL);
v___x_1672_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(v_declName_1650_, v_val_1645_, v___x_1649_, v_sz_1670_, v___x_1671_, v_a_1669_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
return v___x_1672_;
}
else
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
lean_dec(v_declName_1650_);
lean_dec_ref(v_val_1645_);
v_a_1673_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1668_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1668_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
v___jp_1684_:
{
lean_object* v___x_1689_; uint8_t v___x_1690_; 
lean_inc_ref(v___x_1646_);
v___x_1689_ = lean_array_get_borrowed(v___x_1646_, v_x_1647_, v_majorPos_1681_);
v___x_1690_ = l_Lean_Expr_isFVar(v___x_1689_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
lean_dec(v_declName_1650_);
lean_dec(v_mvarId_1648_);
lean_dec_ref(v___x_1646_);
lean_dec_ref(v_val_1645_);
v___x_1691_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2);
lean_inc(v___x_1689_);
v___x_1692_ = l_Lean_indentExpr(v___x_1689_);
v___x_1693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1691_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
v___x_1694_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1693_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v___x_1694_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1694_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
else
{
lean_inc_ref(v_insterestingCtors_1683_);
lean_inc(v_majorPos_1681_);
v___y_1658_ = v_majorPos_1681_;
v___y_1659_ = v_insterestingCtors_1683_;
v___y_1660_ = v___y_1685_;
v___y_1661_ = v___y_1686_;
v___y_1662_ = v___y_1687_;
v___y_1663_ = v___y_1688_;
goto v___jp_1657_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__3___boxed(lean_object* v_val_1715_, lean_object* v___x_1716_, lean_object* v_x_1717_, lean_object* v_mvarId_1718_, lean_object* v___x_1719_, lean_object* v_declName_1720_, lean_object* v_____r_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
uint8_t v___x_29888__boxed_1727_; lean_object* v_res_1728_; 
v___x_29888__boxed_1727_ = lean_unbox(v___x_1719_);
v_res_1728_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__3(v_val_1715_, v___x_1716_, v_x_1717_, v_mvarId_1718_, v___x_29888__boxed_1727_, v_declName_1720_, v_____r_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec_ref(v_x_1717_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__0(lean_object* v_val_1729_, lean_object* v___x_1730_, lean_object* v_x_1731_, lean_object* v_mvarId_1732_, uint8_t v_hasTrace_1733_, lean_object* v_declName_1734_, lean_object* v_____r_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v_majorPos_1765_; lean_object* v_arity_1766_; lean_object* v_insterestingCtors_1767_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___x_1787_; uint8_t v___x_1788_; 
v_majorPos_1765_ = lean_ctor_get(v_val_1729_, 1);
v_arity_1766_ = lean_ctor_get(v_val_1729_, 2);
v_insterestingCtors_1767_ = lean_ctor_get(v_val_1729_, 3);
v___x_1787_ = lean_array_get_size(v_x_1731_);
v___x_1788_ = lean_nat_dec_lt(v___x_1787_, v_arity_1766_);
if (v___x_1788_ == 0)
{
v___y_1769_ = v___y_1736_;
v___y_1770_ = v___y_1737_;
v___y_1771_ = v___y_1738_;
v___y_1772_ = v___y_1739_;
goto v___jp_1768_;
}
else
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
lean_dec(v_declName_1734_);
lean_dec(v_mvarId_1732_);
lean_dec_ref(v___x_1730_);
lean_dec_ref(v_val_1729_);
v___x_1789_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__1);
v___x_1790_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1789_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v___x_1790_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1790_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_a_1791_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
v___jp_1741_:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1748_ = lean_array_get_borrowed(v___x_1730_, v_x_1731_, v___y_1742_);
lean_dec(v___y_1742_);
v___x_1749_ = l_Lean_Expr_fvarId_x21(v___x_1748_);
v___x_1750_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__0));
v___x_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1751_, 0, v___y_1743_);
v___x_1752_ = l_Lean_MVarId_cases(v_mvarId_1732_, v___x_1749_, v___x_1750_, v_hasTrace_1733_, v___x_1751_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; size_t v_sz_1754_; size_t v___x_1755_; lean_object* v___x_1756_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref(v___x_1752_);
v_sz_1754_ = lean_array_size(v_a_1753_);
v___x_1755_ = ((size_t)0ULL);
v___x_1756_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(v_declName_1734_, v_val_1729_, v_hasTrace_1733_, v_sz_1754_, v___x_1755_, v_a_1753_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
return v___x_1756_;
}
else
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
lean_dec(v_declName_1734_);
lean_dec_ref(v_val_1729_);
v_a_1757_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___x_1752_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1752_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_a_1757_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
v___jp_1768_:
{
lean_object* v___x_1773_; uint8_t v___x_1774_; 
lean_inc_ref(v___x_1730_);
v___x_1773_ = lean_array_get_borrowed(v___x_1730_, v_x_1731_, v_majorPos_1765_);
v___x_1774_ = l_Lean_Expr_isFVar(v___x_1773_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_dec(v_declName_1734_);
lean_dec(v_mvarId_1732_);
lean_dec_ref(v___x_1730_);
lean_dec_ref(v_val_1729_);
v___x_1775_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2);
lean_inc(v___x_1773_);
v___x_1776_ = l_Lean_indentExpr(v___x_1773_);
v___x_1777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1775_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
v___x_1778_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1777_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1778_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1778_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
else
{
lean_inc_ref(v_insterestingCtors_1767_);
lean_inc(v_majorPos_1765_);
v___y_1742_ = v_majorPos_1765_;
v___y_1743_ = v_insterestingCtors_1767_;
v___y_1744_ = v___y_1769_;
v___y_1745_ = v___y_1770_;
v___y_1746_ = v___y_1771_;
v___y_1747_ = v___y_1772_;
goto v___jp_1741_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__0___boxed(lean_object* v_val_1799_, lean_object* v___x_1800_, lean_object* v_x_1801_, lean_object* v_mvarId_1802_, lean_object* v_hasTrace_1803_, lean_object* v_declName_1804_, lean_object* v_____r_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
uint8_t v_hasTrace_boxed_1811_; lean_object* v_res_1812_; 
v_hasTrace_boxed_1811_ = lean_unbox(v_hasTrace_1803_);
v_res_1812_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__0(v_val_1799_, v___x_1800_, v_x_1801_, v_mvarId_1802_, v_hasTrace_boxed_1811_, v_declName_1804_, v_____r_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec_ref(v_x_1801_);
return v_res_1812_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1(void){
_start:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1814_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__0));
v___x_1815_ = l_Lean_stringToMessageData(v___x_1814_);
return v___x_1815_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1817_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__2));
v___x_1818_ = l_Lean_stringToMessageData(v___x_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5(lean_object* v_mvarId_1819_, lean_object* v_x_1820_, lean_object* v_x_1821_, lean_object* v_x_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
if (lean_obj_tag(v_x_1820_) == 5)
{
lean_object* v_fn_1828_; lean_object* v_arg_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v_fn_1828_ = lean_ctor_get(v_x_1820_, 0);
lean_inc_ref(v_fn_1828_);
v_arg_1829_ = lean_ctor_get(v_x_1820_, 1);
lean_inc_ref(v_arg_1829_);
lean_dec_ref(v_x_1820_);
v___x_1830_ = lean_array_set(v_x_1821_, v_x_1822_, v_arg_1829_);
v___x_1831_ = lean_unsigned_to_nat(1u);
v___x_1832_ = lean_nat_sub(v_x_1822_, v___x_1831_);
lean_dec(v_x_1822_);
v_x_1820_ = v_fn_1828_;
v_x_1821_ = v___x_1830_;
v_x_1822_ = v___x_1832_;
goto _start;
}
else
{
lean_dec(v_x_1822_);
if (lean_obj_tag(v_x_1820_) == 4)
{
lean_object* v_declName_1834_; lean_object* v___x_1835_; 
v_declName_1834_ = lean_ctor_get(v_x_1820_, 0);
lean_inc(v_declName_1834_);
lean_dec_ref(v_x_1820_);
lean_inc(v_declName_1834_);
v___x_1835_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_declName_1834_, v___y_1826_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1836_);
lean_dec_ref(v___x_1835_);
if (lean_obj_tag(v_a_1836_) == 1)
{
lean_object* v_options_1837_; lean_object* v_val_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_2144_; 
v_options_1837_ = lean_ctor_get(v___y_1825_, 2);
v_val_1838_ = lean_ctor_get(v_a_1836_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v_a_1836_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_1840_ = v_a_1836_;
v_isShared_1841_ = v_isSharedCheck_2144_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_val_1838_);
lean_dec(v_a_1836_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_2144_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
uint8_t v_hasTrace_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___y_1846_; lean_object* v___y_1847_; uint8_t v___y_1848_; lean_object* v___y_1881_; lean_object* v_a_1882_; lean_object* v___y_1886_; lean_object* v___y_1889_; lean_object* v___y_1890_; uint8_t v___y_1891_; lean_object* v___y_1924_; lean_object* v_a_1925_; lean_object* v___y_1929_; 
v_hasTrace_1842_ = lean_ctor_get_uint8(v_options_1837_, sizeof(void*)*1);
v___x_1843_ = l_Lean_instInhabitedExpr;
v___x_1844_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__4));
if (v_hasTrace_1842_ == 0)
{
lean_object* v___x_1931_; lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1955_; 
lean_del_object(v___x_1840_);
v___x_1931_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___x_1844_, v___y_1825_);
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1934_ = v___x_1931_;
v_isShared_1935_ = v_isSharedCheck_1955_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1931_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1955_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
uint8_t v___x_1936_; 
v___x_1936_ = lean_unbox(v_a_1932_);
lean_dec(v_a_1932_);
if (v___x_1936_ == 0)
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
lean_del_object(v___x_1934_);
v___x_1937_ = lean_box(0);
v___x_1938_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__0(v_val_1838_, v___x_1843_, v_x_1821_, v_mvarId_1819_, v_hasTrace_1842_, v_declName_1834_, v___x_1937_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
lean_dec_ref(v_x_1821_);
v___y_1929_ = v___x_1938_;
goto v___jp_1928_;
}
else
{
lean_object* v___x_1939_; lean_object* v___x_1941_; 
v___x_1939_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3);
lean_inc(v_mvarId_1819_);
if (v_isShared_1935_ == 0)
{
lean_ctor_set_tag(v___x_1934_, 1);
lean_ctor_set(v___x_1934_, 0, v_mvarId_1819_);
v___x_1941_ = v___x_1934_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_mvarId_1819_);
v___x_1941_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1939_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
v___x_1943_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1844_, v___x_1942_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_a_1944_; lean_object* v___x_1945_; 
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_a_1944_);
lean_dec_ref(v___x_1943_);
v___x_1945_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__0(v_val_1838_, v___x_1843_, v_x_1821_, v_mvarId_1819_, v_hasTrace_1842_, v_declName_1834_, v_a_1944_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
lean_dec_ref(v_x_1821_);
v___y_1929_ = v___x_1945_;
goto v___jp_1928_;
}
else
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
lean_dec(v_val_1838_);
lean_dec(v_declName_1834_);
lean_dec_ref(v_x_1821_);
lean_dec(v_mvarId_1819_);
v_a_1946_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1943_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1943_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
lean_inc(v_a_1946_);
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
v___y_1924_ = v___x_1951_;
v_a_1925_ = v_a_1946_;
goto v___jp_1923_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1956_; lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_2143_; 
v___x_1956_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___x_1844_, v___y_1825_);
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_1959_ = v___x_1956_;
v_isShared_1960_ = v_isSharedCheck_2143_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1956_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_2143_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___f_1961_; lean_object* v___x_1962_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v_a_1966_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v_a_1982_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; uint8_t v___y_1990_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v_a_2003_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v_a_2022_; lean_object* v___y_2033_; lean_object* v___y_2034_; lean_object* v_a_2035_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; uint8_t v___y_2043_; lean_object* v___y_2054_; lean_object* v___y_2055_; lean_object* v_a_2056_; lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v___y_2062_; uint8_t v___x_2115_; 
v___f_1961_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__5));
v___x_1962_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__6));
v___x_2115_ = lean_unbox(v_a_1957_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; uint8_t v___x_2117_; 
v___x_2116_ = l_Lean_trace_profiler;
v___x_2117_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v_options_1837_, v___x_2116_);
if (v___x_2117_ == 0)
{
lean_object* v___x_2118_; lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2142_; 
lean_del_object(v___x_1959_);
lean_dec(v_a_1957_);
lean_del_object(v___x_1840_);
v___x_2118_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___x_1844_, v___y_1825_);
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2121_ = v___x_2118_;
v_isShared_2122_ = v_isSharedCheck_2142_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2118_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2142_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
uint8_t v___x_2123_; 
v___x_2123_ = lean_unbox(v_a_2119_);
lean_dec(v_a_2119_);
if (v___x_2123_ == 0)
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
lean_del_object(v___x_2121_);
v___x_2124_ = lean_box(0);
v___x_2125_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__3(v_val_1838_, v___x_1843_, v_x_1821_, v_mvarId_1819_, v___x_2117_, v_declName_1834_, v___x_2124_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
lean_dec_ref(v_x_1821_);
v___y_1886_ = v___x_2125_;
goto v___jp_1885_;
}
else
{
lean_object* v___x_2126_; lean_object* v___x_2128_; 
v___x_2126_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3);
lean_inc(v_mvarId_1819_);
if (v_isShared_2122_ == 0)
{
lean_ctor_set_tag(v___x_2121_, 1);
lean_ctor_set(v___x_2121_, 0, v_mvarId_1819_);
v___x_2128_ = v___x_2121_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_mvarId_1819_);
v___x_2128_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2126_);
lean_ctor_set(v___x_2129_, 1, v___x_2128_);
v___x_2130_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1844_, v___x_2129_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2132_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref(v___x_2130_);
v___x_2132_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__3(v_val_1838_, v___x_1843_, v_x_1821_, v_mvarId_1819_, v___x_2117_, v_declName_1834_, v_a_2131_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
lean_dec_ref(v_x_1821_);
v___y_1886_ = v___x_2132_;
goto v___jp_1885_;
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec(v_val_1838_);
lean_dec(v_declName_1834_);
lean_dec_ref(v_x_1821_);
lean_dec(v_mvarId_1819_);
v_a_2133_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2130_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2130_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
lean_inc(v_a_2133_);
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
v___y_1881_ = v___x_2138_;
v_a_1882_ = v_a_2133_;
goto v___jp_1880_;
}
}
}
}
}
}
}
else
{
goto v___jp_2072_;
}
}
else
{
goto v___jp_2072_;
}
v___jp_1963_:
{
lean_object* v___x_1967_; double v___x_1968_; double v___x_1969_; double v___x_1970_; double v___x_1971_; double v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; uint8_t v___x_1977_; lean_object* v___x_1978_; 
v___x_1967_ = lean_io_mono_nanos_now();
v___x_1968_ = lean_float_of_nat(v___y_1964_);
v___x_1969_ = lean_float_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__7);
v___x_1970_ = lean_float_div(v___x_1968_, v___x_1969_);
v___x_1971_ = lean_float_of_nat(v___x_1967_);
v___x_1972_ = lean_float_div(v___x_1971_, v___x_1969_);
v___x_1973_ = lean_box_float(v___x_1970_);
v___x_1974_ = lean_box_float(v___x_1972_);
v___x_1975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1973_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
v___x_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1976_, 0, v_a_1966_);
lean_ctor_set(v___x_1976_, 1, v___x_1975_);
v___x_1977_ = lean_unbox(v_a_1957_);
lean_dec(v_a_1957_);
v___x_1978_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7(v___x_1844_, v_hasTrace_1842_, v___x_1962_, v_options_1837_, v___x_1977_, v___y_1965_, v___f_1961_, v___x_1976_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
return v___x_1978_;
}
v___jp_1979_:
{
lean_object* v___x_1984_; 
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v_a_1982_);
v___x_1984_ = v___x_1959_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_a_1982_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
v___y_1964_ = v___y_1980_;
v___y_1965_ = v___y_1981_;
v_a_1966_ = v___x_1984_;
goto v___jp_1963_;
}
}
v___jp_1986_:
{
if (v___y_1990_ == 0)
{
lean_object* v___x_1991_; lean_object* v_a_1992_; uint8_t v___x_1993_; 
v___x_1991_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___x_1844_, v___y_1825_);
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_1992_);
lean_dec_ref(v___x_1991_);
v___x_1993_ = lean_unbox(v_a_1992_);
lean_dec(v_a_1992_);
if (v___x_1993_ == 0)
{
v___y_1980_ = v___y_1988_;
v___y_1981_ = v___y_1989_;
v_a_1982_ = v___y_1987_;
goto v___jp_1979_;
}
else
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1994_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1);
lean_inc_ref(v___y_1987_);
v___x_1995_ = l_Lean_Exception_toMessageData(v___y_1987_);
v___x_1996_ = l_Lean_indentD(v___x_1995_);
v___x_1997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1994_);
lean_ctor_set(v___x_1997_, 1, v___x_1996_);
v___x_1998_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1844_, v___x_1997_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_dec_ref(v___x_1998_);
v___y_1980_ = v___y_1988_;
v___y_1981_ = v___y_1989_;
v_a_1982_ = v___y_1987_;
goto v___jp_1979_;
}
else
{
lean_object* v_a_1999_; 
lean_dec_ref(v___y_1987_);
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref(v___x_1998_);
v___y_1980_ = v___y_1988_;
v___y_1981_ = v___y_1989_;
v_a_1982_ = v_a_1999_;
goto v___jp_1979_;
}
}
}
else
{
v___y_1980_ = v___y_1988_;
v___y_1981_ = v___y_1989_;
v_a_1982_ = v___y_1987_;
goto v___jp_1979_;
}
}
v___jp_2000_:
{
uint8_t v___x_2004_; 
v___x_2004_ = l_Lean_Exception_isInterrupt(v_a_2003_);
if (v___x_2004_ == 0)
{
uint8_t v___x_2005_; 
lean_inc_ref(v_a_2003_);
v___x_2005_ = l_Lean_Exception_isRuntime(v_a_2003_);
v___y_1987_ = v_a_2003_;
v___y_1988_ = v___y_2001_;
v___y_1989_ = v___y_2002_;
v___y_1990_ = v___x_2005_;
goto v___jp_1986_;
}
else
{
v___y_1987_ = v_a_2003_;
v___y_1988_ = v___y_2001_;
v___y_1989_ = v___y_2002_;
v___y_1990_ = v___x_2004_;
goto v___jp_1986_;
}
}
v___jp_2006_:
{
if (lean_obj_tag(v___y_2009_) == 0)
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2017_; 
lean_del_object(v___x_1959_);
v_a_2010_ = lean_ctor_get(v___y_2009_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___y_2009_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2012_ = v___y_2009_;
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___y_2009_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
lean_ctor_set_tag(v___x_2012_, 1);
v___x_2015_ = v___x_2012_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_a_2010_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
v___y_1964_ = v___y_2007_;
v___y_1965_ = v___y_2008_;
v_a_1966_ = v___x_2015_;
goto v___jp_1963_;
}
}
}
else
{
lean_object* v_a_2018_; 
v_a_2018_ = lean_ctor_get(v___y_2009_, 0);
lean_inc(v_a_2018_);
lean_dec_ref(v___y_2009_);
v___y_2001_ = v___y_2007_;
v___y_2002_ = v___y_2008_;
v_a_2003_ = v_a_2018_;
goto v___jp_2000_;
}
}
v___jp_2019_:
{
lean_object* v___x_2023_; double v___x_2024_; double v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; uint8_t v___x_2030_; lean_object* v___x_2031_; 
v___x_2023_ = lean_io_get_num_heartbeats();
v___x_2024_ = lean_float_of_nat(v___y_2020_);
v___x_2025_ = lean_float_of_nat(v___x_2023_);
v___x_2026_ = lean_box_float(v___x_2024_);
v___x_2027_ = lean_box_float(v___x_2025_);
v___x_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2026_);
lean_ctor_set(v___x_2028_, 1, v___x_2027_);
v___x_2029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2029_, 0, v_a_2022_);
lean_ctor_set(v___x_2029_, 1, v___x_2028_);
v___x_2030_ = lean_unbox(v_a_1957_);
lean_dec(v_a_1957_);
v___x_2031_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7(v___x_1844_, v_hasTrace_1842_, v___x_1962_, v_options_1837_, v___x_2030_, v___y_2021_, v___f_1961_, v___x_2029_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
return v___x_2031_;
}
v___jp_2032_:
{
lean_object* v___x_2037_; 
if (v_isShared_1841_ == 0)
{
lean_ctor_set_tag(v___x_1840_, 0);
lean_ctor_set(v___x_1840_, 0, v_a_2035_);
v___x_2037_ = v___x_1840_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2035_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
v___y_2020_ = v___y_2033_;
v___y_2021_ = v___y_2034_;
v_a_2022_ = v___x_2037_;
goto v___jp_2019_;
}
}
v___jp_2039_:
{
if (v___y_2043_ == 0)
{
lean_object* v___x_2044_; lean_object* v_a_2045_; uint8_t v___x_2046_; 
v___x_2044_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___x_1844_, v___y_1825_);
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_a_2045_);
lean_dec_ref(v___x_2044_);
v___x_2046_ = lean_unbox(v_a_2045_);
lean_dec(v_a_2045_);
if (v___x_2046_ == 0)
{
v___y_2033_ = v___y_2040_;
v___y_2034_ = v___y_2041_;
v_a_2035_ = v___y_2042_;
goto v___jp_2032_;
}
else
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2047_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1);
lean_inc_ref(v___y_2042_);
v___x_2048_ = l_Lean_Exception_toMessageData(v___y_2042_);
v___x_2049_ = l_Lean_indentD(v___x_2048_);
v___x_2050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2047_);
lean_ctor_set(v___x_2050_, 1, v___x_2049_);
v___x_2051_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1844_, v___x_2050_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_dec_ref(v___x_2051_);
v___y_2033_ = v___y_2040_;
v___y_2034_ = v___y_2041_;
v_a_2035_ = v___y_2042_;
goto v___jp_2032_;
}
else
{
lean_object* v_a_2052_; 
lean_dec_ref(v___y_2042_);
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2052_);
lean_dec_ref(v___x_2051_);
v___y_2033_ = v___y_2040_;
v___y_2034_ = v___y_2041_;
v_a_2035_ = v_a_2052_;
goto v___jp_2032_;
}
}
}
else
{
v___y_2033_ = v___y_2040_;
v___y_2034_ = v___y_2041_;
v_a_2035_ = v___y_2042_;
goto v___jp_2032_;
}
}
v___jp_2053_:
{
uint8_t v___x_2057_; 
v___x_2057_ = l_Lean_Exception_isInterrupt(v_a_2056_);
if (v___x_2057_ == 0)
{
uint8_t v___x_2058_; 
lean_inc_ref(v_a_2056_);
v___x_2058_ = l_Lean_Exception_isRuntime(v_a_2056_);
v___y_2040_ = v___y_2054_;
v___y_2041_ = v___y_2055_;
v___y_2042_ = v_a_2056_;
v___y_2043_ = v___x_2058_;
goto v___jp_2039_;
}
else
{
v___y_2040_ = v___y_2054_;
v___y_2041_ = v___y_2055_;
v___y_2042_ = v_a_2056_;
v___y_2043_ = v___x_2057_;
goto v___jp_2039_;
}
}
v___jp_2059_:
{
if (lean_obj_tag(v___y_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_del_object(v___x_1840_);
v_a_2063_ = lean_ctor_get(v___y_2062_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___y_2062_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___y_2062_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___y_2062_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
lean_ctor_set_tag(v___x_2065_, 1);
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
v___y_2020_ = v___y_2060_;
v___y_2021_ = v___y_2061_;
v_a_2022_ = v___x_2068_;
goto v___jp_2019_;
}
}
}
else
{
lean_object* v_a_2071_; 
v_a_2071_ = lean_ctor_get(v___y_2062_, 0);
lean_inc(v_a_2071_);
lean_dec_ref(v___y_2062_);
v___y_2054_ = v___y_2060_;
v___y_2055_ = v___y_2061_;
v_a_2056_ = v_a_2071_;
goto v___jp_2053_;
}
}
v___jp_2072_:
{
lean_object* v___x_2073_; lean_object* v_a_2074_; lean_object* v___x_2075_; uint8_t v___x_2076_; 
v___x_2073_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__5___redArg(v___y_1826_);
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_a_2074_);
lean_dec_ref(v___x_2073_);
v___x_2075_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2076_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v_options_1837_, v___x_2075_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2095_; 
lean_del_object(v___x_1840_);
v___x_2077_ = lean_io_mono_nanos_now();
v___x_2078_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___x_1844_, v___y_1825_);
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2081_ = v___x_2078_;
v_isShared_2082_ = v_isSharedCheck_2095_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2078_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2095_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
uint8_t v___x_2083_; 
v___x_2083_ = lean_unbox(v_a_2079_);
lean_dec(v_a_2079_);
if (v___x_2083_ == 0)
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
lean_del_object(v___x_2081_);
v___x_2084_ = lean_box(0);
v___x_2085_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__2(v_val_1838_, v___x_1843_, v_x_1821_, v_mvarId_1819_, v___x_2076_, v_declName_1834_, v___x_2084_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
lean_dec_ref(v_x_1821_);
v___y_2007_ = v___x_2077_;
v___y_2008_ = v_a_2074_;
v___y_2009_ = v___x_2085_;
goto v___jp_2006_;
}
else
{
lean_object* v___x_2086_; lean_object* v___x_2088_; 
v___x_2086_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3);
lean_inc(v_mvarId_1819_);
if (v_isShared_2082_ == 0)
{
lean_ctor_set_tag(v___x_2081_, 1);
lean_ctor_set(v___x_2081_, 0, v_mvarId_1819_);
v___x_2088_ = v___x_2081_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_mvarId_1819_);
v___x_2088_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2086_);
lean_ctor_set(v___x_2089_, 1, v___x_2088_);
v___x_2090_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1844_, v___x_2089_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; lean_object* v___x_2092_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2091_);
lean_dec_ref(v___x_2090_);
v___x_2092_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__2(v_val_1838_, v___x_1843_, v_x_1821_, v_mvarId_1819_, v___x_2076_, v_declName_1834_, v_a_2091_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
lean_dec_ref(v_x_1821_);
v___y_2007_ = v___x_2077_;
v___y_2008_ = v_a_2074_;
v___y_2009_ = v___x_2092_;
goto v___jp_2006_;
}
else
{
lean_object* v_a_2093_; 
lean_dec(v_val_1838_);
lean_dec(v_declName_1834_);
lean_dec_ref(v_x_1821_);
lean_dec(v_mvarId_1819_);
v_a_2093_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2093_);
lean_dec_ref(v___x_2090_);
v___y_2001_ = v___x_2077_;
v___y_2002_ = v_a_2074_;
v_a_2003_ = v_a_2093_;
goto v___jp_2000_;
}
}
}
}
}
else
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2114_; 
lean_del_object(v___x_1959_);
v___x_2096_ = lean_io_get_num_heartbeats();
v___x_2097_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___x_1844_, v___y_1825_);
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2100_ = v___x_2097_;
v_isShared_2101_ = v_isSharedCheck_2114_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2097_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2114_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
uint8_t v___x_2102_; 
v___x_2102_ = lean_unbox(v_a_2098_);
lean_dec(v_a_2098_);
if (v___x_2102_ == 0)
{
lean_object* v___x_2103_; lean_object* v___x_2104_; 
lean_del_object(v___x_2100_);
v___x_2103_ = lean_box(0);
v___x_2104_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1(v_val_1838_, v___x_1843_, v_x_1821_, v_mvarId_1819_, v_declName_1834_, v___x_2076_, v___x_2103_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
lean_dec_ref(v_x_1821_);
v___y_2060_ = v___x_2096_;
v___y_2061_ = v_a_2074_;
v___y_2062_ = v___x_2104_;
goto v___jp_2059_;
}
else
{
lean_object* v___x_2105_; lean_object* v___x_2107_; 
v___x_2105_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3);
lean_inc(v_mvarId_1819_);
if (v_isShared_2101_ == 0)
{
lean_ctor_set_tag(v___x_2100_, 1);
lean_ctor_set(v___x_2100_, 0, v_mvarId_1819_);
v___x_2107_ = v___x_2100_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_mvarId_1819_);
v___x_2107_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2105_);
lean_ctor_set(v___x_2108_, 1, v___x_2107_);
v___x_2109_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1844_, v___x_2108_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_a_2110_; lean_object* v___x_2111_; 
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_a_2110_);
lean_dec_ref(v___x_2109_);
v___x_2111_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1(v_val_1838_, v___x_1843_, v_x_1821_, v_mvarId_1819_, v_declName_1834_, v___x_2076_, v_a_2110_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
lean_dec_ref(v_x_1821_);
v___y_2060_ = v___x_2096_;
v___y_2061_ = v_a_2074_;
v___y_2062_ = v___x_2111_;
goto v___jp_2059_;
}
else
{
lean_object* v_a_2112_; 
lean_dec(v_val_1838_);
lean_dec(v_declName_1834_);
lean_dec_ref(v_x_1821_);
lean_dec(v_mvarId_1819_);
v_a_2112_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_a_2112_);
lean_dec_ref(v___x_2109_);
v___y_2054_ = v___x_2096_;
v___y_2055_ = v_a_2074_;
v_a_2056_ = v_a_2112_;
goto v___jp_2053_;
}
}
}
}
}
}
}
}
v___jp_1845_:
{
if (v___y_1848_ == 0)
{
lean_object* v___x_1849_; lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1879_; 
lean_dec_ref(v___y_1846_);
v___x_1849_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___x_1844_, v___y_1825_);
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1852_ = v___x_1849_;
v_isShared_1853_ = v_isSharedCheck_1879_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1849_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1879_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
uint8_t v___x_1854_; 
v___x_1854_ = lean_unbox(v_a_1850_);
lean_dec(v_a_1850_);
if (v___x_1854_ == 0)
{
lean_object* v___x_1856_; 
if (v_isShared_1853_ == 0)
{
lean_ctor_set_tag(v___x_1852_, 1);
lean_ctor_set(v___x_1852_, 0, v___y_1847_);
v___x_1856_ = v___x_1852_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___y_1847_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
else
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
lean_del_object(v___x_1852_);
v___x_1858_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1);
lean_inc_ref(v___y_1847_);
v___x_1859_ = l_Lean_Exception_toMessageData(v___y_1847_);
v___x_1860_ = l_Lean_indentD(v___x_1859_);
v___x_1861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1858_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
v___x_1862_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1844_, v___x_1861_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1869_ == 0)
{
lean_object* v_unused_1870_; 
v_unused_1870_ = lean_ctor_get(v___x_1862_, 0);
lean_dec(v_unused_1870_);
v___x_1864_ = v___x_1862_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_dec(v___x_1862_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
lean_ctor_set_tag(v___x_1864_, 1);
lean_ctor_set(v___x_1864_, 0, v___y_1847_);
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___y_1847_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
else
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
lean_dec_ref(v___y_1847_);
v_a_1871_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1873_ = v___x_1862_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1862_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1871_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_1847_);
return v___y_1846_;
}
}
v___jp_1880_:
{
uint8_t v___x_1883_; 
v___x_1883_ = l_Lean_Exception_isInterrupt(v_a_1882_);
if (v___x_1883_ == 0)
{
uint8_t v___x_1884_; 
lean_inc_ref(v_a_1882_);
v___x_1884_ = l_Lean_Exception_isRuntime(v_a_1882_);
v___y_1846_ = v___y_1881_;
v___y_1847_ = v_a_1882_;
v___y_1848_ = v___x_1884_;
goto v___jp_1845_;
}
else
{
v___y_1846_ = v___y_1881_;
v___y_1847_ = v_a_1882_;
v___y_1848_ = v___x_1883_;
goto v___jp_1845_;
}
}
v___jp_1885_:
{
if (lean_obj_tag(v___y_1886_) == 0)
{
return v___y_1886_;
}
else
{
lean_object* v_a_1887_; 
v_a_1887_ = lean_ctor_get(v___y_1886_, 0);
lean_inc(v_a_1887_);
v___y_1881_ = v___y_1886_;
v_a_1882_ = v_a_1887_;
goto v___jp_1880_;
}
}
v___jp_1888_:
{
if (v___y_1891_ == 0)
{
lean_object* v___x_1892_; lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1922_; 
lean_dec_ref(v___y_1890_);
v___x_1892_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___x_1844_, v___y_1825_);
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1895_ = v___x_1892_;
v_isShared_1896_ = v_isSharedCheck_1922_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1892_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1922_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
uint8_t v___x_1897_; 
v___x_1897_ = lean_unbox(v_a_1893_);
lean_dec(v_a_1893_);
if (v___x_1897_ == 0)
{
lean_object* v___x_1899_; 
if (v_isShared_1896_ == 0)
{
lean_ctor_set_tag(v___x_1895_, 1);
lean_ctor_set(v___x_1895_, 0, v___y_1889_);
v___x_1899_ = v___x_1895_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___y_1889_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
else
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
lean_del_object(v___x_1895_);
v___x_1901_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1);
lean_inc_ref(v___y_1889_);
v___x_1902_ = l_Lean_Exception_toMessageData(v___y_1889_);
v___x_1903_ = l_Lean_indentD(v___x_1902_);
v___x_1904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1901_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
v___x_1905_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1844_, v___x_1904_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1912_ == 0)
{
lean_object* v_unused_1913_; 
v_unused_1913_ = lean_ctor_get(v___x_1905_, 0);
lean_dec(v_unused_1913_);
v___x_1907_ = v___x_1905_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_dec(v___x_1905_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
lean_ctor_set_tag(v___x_1907_, 1);
lean_ctor_set(v___x_1907_, 0, v___y_1889_);
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___y_1889_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
lean_dec_ref(v___y_1889_);
v_a_1914_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1905_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1905_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_1889_);
return v___y_1890_;
}
}
v___jp_1923_:
{
uint8_t v___x_1926_; 
v___x_1926_ = l_Lean_Exception_isInterrupt(v_a_1925_);
if (v___x_1926_ == 0)
{
uint8_t v___x_1927_; 
lean_inc_ref(v_a_1925_);
v___x_1927_ = l_Lean_Exception_isRuntime(v_a_1925_);
v___y_1889_ = v_a_1925_;
v___y_1890_ = v___y_1924_;
v___y_1891_ = v___x_1927_;
goto v___jp_1888_;
}
else
{
v___y_1889_ = v_a_1925_;
v___y_1890_ = v___y_1924_;
v___y_1891_ = v___x_1926_;
goto v___jp_1888_;
}
}
v___jp_1928_:
{
if (lean_obj_tag(v___y_1929_) == 0)
{
return v___y_1929_;
}
else
{
lean_object* v_a_1930_; 
v_a_1930_ = lean_ctor_get(v___y_1929_, 0);
lean_inc(v_a_1930_);
v___y_1924_ = v___y_1929_;
v_a_1925_ = v_a_1930_;
goto v___jp_1923_;
}
}
}
}
else
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
lean_dec(v_a_1836_);
lean_dec(v_declName_1834_);
lean_dec_ref(v_x_1821_);
lean_dec(v_mvarId_1819_);
v___x_2145_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__9, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__9_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__9);
v___x_2146_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_2145_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
return v___x_2146_;
}
}
else
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2154_; 
lean_dec(v_declName_1834_);
lean_dec_ref(v_x_1821_);
lean_dec(v_mvarId_1819_);
v_a_2147_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2149_ = v___x_1835_;
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_1835_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2152_; 
if (v_isShared_2150_ == 0)
{
v___x_2152_ = v___x_2149_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_a_2147_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
else
{
lean_object* v___x_2155_; lean_object* v___x_2156_; 
lean_dec_ref(v_x_1821_);
lean_dec_ref(v_x_1820_);
lean_dec(v_mvarId_1819_);
v___x_2155_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__11, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__11_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__11);
v___x_2156_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_2155_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
return v___x_2156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___boxed(lean_object* v_mvarId_2157_, lean_object* v_x_2158_, lean_object* v_x_2159_, lean_object* v_x_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5(v_mvarId_2157_, v_x_2158_, v_x_2159_, v_x_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitSparseCasesOn(lean_object* v_mvarId_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_){
_start:
{
lean_object* v___x_2173_; 
lean_inc(v_mvarId_2167_);
v___x_2173_ = l_Lean_MVarId_getType(v_mvarId_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; lean_object* v___x_2175_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
lean_inc(v_a_2174_);
lean_dec_ref(v___x_2173_);
v___x_2175_ = l_Lean_Meta_matchEqHEqLHS_x3f(v_a_2174_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2176_);
lean_dec_ref(v___x_2175_);
if (lean_obj_tag(v_a_2176_) == 1)
{
lean_object* v_val_2177_; lean_object* v_snd_2178_; lean_object* v_dummy_2179_; lean_object* v_nargs_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v_val_2177_ = lean_ctor_get(v_a_2176_, 0);
lean_inc(v_val_2177_);
lean_dec_ref(v_a_2176_);
v_snd_2178_ = lean_ctor_get(v_val_2177_, 1);
lean_inc(v_snd_2178_);
lean_dec(v_val_2177_);
v_dummy_2179_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__0);
v_nargs_2180_ = l_Lean_Expr_getAppNumArgs(v_snd_2178_);
lean_inc(v_nargs_2180_);
v___x_2181_ = lean_mk_array(v_nargs_2180_, v_dummy_2179_);
v___x_2182_ = lean_unsigned_to_nat(1u);
v___x_2183_ = lean_nat_sub(v_nargs_2180_, v___x_2182_);
lean_dec(v_nargs_2180_);
v___x_2184_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5(v_mvarId_2167_, v_snd_2178_, v___x_2181_, v___x_2183_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
return v___x_2184_;
}
else
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
lean_dec(v_a_2176_);
lean_dec(v_mvarId_2167_);
v___x_2185_ = lean_obj_once(&l_Lean_Meta_reduceSparseCasesOn___closed__1, &l_Lean_Meta_reduceSparseCasesOn___closed__1_once, _init_l_Lean_Meta_reduceSparseCasesOn___closed__1);
v___x_2186_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_2185_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
return v___x_2186_;
}
}
else
{
lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2194_; 
lean_dec(v_mvarId_2167_);
v_a_2187_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2189_ = v___x_2175_;
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2175_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2192_; 
if (v_isShared_2190_ == 0)
{
v___x_2192_ = v___x_2189_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2187_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
else
{
lean_object* v_a_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2202_; 
lean_dec(v_mvarId_2167_);
v_a_2195_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2197_ = v___x_2173_;
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_a_2195_);
lean_dec(v___x_2173_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2200_; 
if (v_isShared_2198_ == 0)
{
v___x_2200_ = v___x_2197_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_a_2195_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitSparseCasesOn___boxed(lean_object* v_mvarId_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l_Lean_Meta_splitSparseCasesOn(v_mvarId_2203_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_);
lean_dec(v_a_2207_);
lean_dec_ref(v_a_2206_);
lean_dec(v_a_2205_);
lean_dec_ref(v_a_2204_);
return v_res_2209_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_SparseCasesOn(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_SparseCasesOnEq(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_HasNotBit(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cases(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_SplitSparseCasesOn(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_SparseCasesOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_SparseCasesOnEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_HasNotBit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_SplitSparseCasesOn(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_SparseCasesOn(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_SparseCasesOnEq(uint8_t builtin);
lean_object* initialize_Lean_Meta_HasNotBit(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cases(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_SplitSparseCasesOn(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_SparseCasesOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_SparseCasesOnEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_HasNotBit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_SplitSparseCasesOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_SplitSparseCasesOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_SplitSparseCasesOn(builtin);
}
#ifdef __cplusplus
}
#endif
