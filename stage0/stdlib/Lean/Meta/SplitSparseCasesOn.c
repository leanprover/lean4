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
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
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
lean_inc(v_a_12_);
lean_inc_ref(v_a_11_);
lean_inc(v_a_10_);
lean_inc_ref(v_a_9_);
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
lean_dec(v_a_12_);
lean_dec_ref(v_a_11_);
lean_dec(v_a_10_);
lean_dec_ref(v_a_9_);
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
lean_dec(v_a_12_);
lean_dec_ref(v_a_11_);
lean_dec(v_a_10_);
lean_dec_ref(v_a_9_);
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
v___x_229_ = lean_apply_6(v___f_222_, v___x_228_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, lean_box(0));
return v___x_229_;
}
else
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_239_; 
lean_dec_ref(v___f_222_);
v___x_230_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__1);
v___x_231_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_230_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
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
uint8_t v___x_14086__boxed_247_; lean_object* v_res_248_; 
v___x_14086__boxed_247_ = lean_unbox(v___x_240_);
v_res_248_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1(v___x_14086__boxed_247_, v___f_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
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
lean_object* v_fileName_293_; lean_object* v_fileMap_294_; lean_object* v_options_295_; lean_object* v_currRecDepth_296_; lean_object* v_maxRecDepth_297_; lean_object* v_ref_298_; lean_object* v_currNamespace_299_; lean_object* v_openDecls_300_; lean_object* v_initHeartbeats_301_; lean_object* v_maxHeartbeats_302_; lean_object* v_quotContext_303_; lean_object* v_currMacroScope_304_; uint8_t v_diag_305_; lean_object* v_cancelTk_x3f_306_; uint8_t v_suppressElabErrors_307_; lean_object* v_inheritedTraceOptions_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_363_; 
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
v_isSharedCheck_363_ = !lean_is_exclusive(v___y_290_);
if (v_isSharedCheck_363_ == 0)
{
v___x_310_ = v___y_290_;
v_isShared_311_ = v_isSharedCheck_363_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_inheritedTraceOptions_308_);
lean_inc(v_cancelTk_x3f_306_);
lean_inc(v_currMacroScope_304_);
lean_inc(v_quotContext_303_);
lean_inc(v_maxHeartbeats_302_);
lean_inc(v_initHeartbeats_301_);
lean_inc(v_openDecls_300_);
lean_inc(v_currNamespace_299_);
lean_inc(v_ref_298_);
lean_inc(v_maxRecDepth_297_);
lean_inc(v_currRecDepth_296_);
lean_inc(v_options_295_);
lean_inc(v_fileMap_294_);
lean_inc(v_fileName_293_);
lean_dec(v___y_290_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_363_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_312_; lean_object* v_traceState_313_; lean_object* v_traces_314_; lean_object* v_ref_315_; lean_object* v___x_317_; 
v___x_312_ = lean_st_ref_get(v___y_291_);
v_traceState_313_ = lean_ctor_get(v___x_312_, 4);
lean_inc_ref(v_traceState_313_);
lean_dec(v___x_312_);
v_traces_314_ = lean_ctor_get(v_traceState_313_, 0);
lean_inc_ref(v_traces_314_);
lean_dec_ref(v_traceState_313_);
v_ref_315_ = l_Lean_replaceRef(v_ref_286_, v_ref_298_);
lean_dec(v_ref_298_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 5, v_ref_315_);
v___x_317_ = v___x_310_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_fileName_293_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v_fileMap_294_);
lean_ctor_set(v_reuseFailAlloc_362_, 2, v_options_295_);
lean_ctor_set(v_reuseFailAlloc_362_, 3, v_currRecDepth_296_);
lean_ctor_set(v_reuseFailAlloc_362_, 4, v_maxRecDepth_297_);
lean_ctor_set(v_reuseFailAlloc_362_, 5, v_ref_315_);
lean_ctor_set(v_reuseFailAlloc_362_, 6, v_currNamespace_299_);
lean_ctor_set(v_reuseFailAlloc_362_, 7, v_openDecls_300_);
lean_ctor_set(v_reuseFailAlloc_362_, 8, v_initHeartbeats_301_);
lean_ctor_set(v_reuseFailAlloc_362_, 9, v_maxHeartbeats_302_);
lean_ctor_set(v_reuseFailAlloc_362_, 10, v_quotContext_303_);
lean_ctor_set(v_reuseFailAlloc_362_, 11, v_currMacroScope_304_);
lean_ctor_set(v_reuseFailAlloc_362_, 12, v_cancelTk_x3f_306_);
lean_ctor_set(v_reuseFailAlloc_362_, 13, v_inheritedTraceOptions_308_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, sizeof(void*)*14, v_diag_305_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, sizeof(void*)*14 + 1, v_suppressElabErrors_307_);
v___x_317_ = v_reuseFailAlloc_362_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
lean_object* v___x_318_; size_t v_sz_319_; size_t v___x_320_; lean_object* v___x_321_; lean_object* v_msg_322_; lean_object* v___x_323_; lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_361_; 
v___x_318_ = l_Lean_PersistentArray_toArray___redArg(v_traces_314_);
lean_dec_ref(v_traces_314_);
v_sz_319_ = lean_array_size(v___x_318_);
v___x_320_ = ((size_t)0ULL);
v___x_321_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__11_spec__12(v_sz_319_, v___x_320_, v___x_318_);
v_msg_322_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_322_, 0, v_data_285_);
lean_ctor_set(v_msg_322_, 1, v_msg_287_);
lean_ctor_set(v_msg_322_, 2, v___x_321_);
v___x_323_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msg_322_, v___y_288_, v___y_289_, v___x_317_, v___y_291_);
lean_dec_ref(v___x_317_);
v_a_324_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_361_ == 0)
{
v___x_326_ = v___x_323_;
v_isShared_327_ = v_isSharedCheck_361_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_323_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_361_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_328_; lean_object* v_traceState_329_; lean_object* v_env_330_; lean_object* v_nextMacroScope_331_; lean_object* v_ngen_332_; lean_object* v_auxDeclNGen_333_; lean_object* v_cache_334_; lean_object* v_messages_335_; lean_object* v_infoState_336_; lean_object* v_snapshotTasks_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_360_; 
v___x_328_ = lean_st_ref_take(v___y_291_);
v_traceState_329_ = lean_ctor_get(v___x_328_, 4);
v_env_330_ = lean_ctor_get(v___x_328_, 0);
v_nextMacroScope_331_ = lean_ctor_get(v___x_328_, 1);
v_ngen_332_ = lean_ctor_get(v___x_328_, 2);
v_auxDeclNGen_333_ = lean_ctor_get(v___x_328_, 3);
v_cache_334_ = lean_ctor_get(v___x_328_, 5);
v_messages_335_ = lean_ctor_get(v___x_328_, 6);
v_infoState_336_ = lean_ctor_get(v___x_328_, 7);
v_snapshotTasks_337_ = lean_ctor_get(v___x_328_, 8);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_360_ == 0)
{
v___x_339_ = v___x_328_;
v_isShared_340_ = v_isSharedCheck_360_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_snapshotTasks_337_);
lean_inc(v_infoState_336_);
lean_inc(v_messages_335_);
lean_inc(v_cache_334_);
lean_inc(v_traceState_329_);
lean_inc(v_auxDeclNGen_333_);
lean_inc(v_ngen_332_);
lean_inc(v_nextMacroScope_331_);
lean_inc(v_env_330_);
lean_dec(v___x_328_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_360_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
uint64_t v_tid_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_358_; 
v_tid_341_ = lean_ctor_get_uint64(v_traceState_329_, sizeof(void*)*1);
v_isSharedCheck_358_ = !lean_is_exclusive(v_traceState_329_);
if (v_isSharedCheck_358_ == 0)
{
lean_object* v_unused_359_; 
v_unused_359_ = lean_ctor_get(v_traceState_329_, 0);
lean_dec(v_unused_359_);
v___x_343_ = v_traceState_329_;
v_isShared_344_ = v_isSharedCheck_358_;
goto v_resetjp_342_;
}
else
{
lean_dec(v_traceState_329_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_358_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_348_; 
v___x_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_345_, 0, v_ref_286_);
lean_ctor_set(v___x_345_, 1, v_a_324_);
v___x_346_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_284_, v___x_345_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 0, v___x_346_);
v___x_348_ = v___x_343_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_346_);
lean_ctor_set_uint64(v_reuseFailAlloc_357_, sizeof(void*)*1, v_tid_341_);
v___x_348_ = v_reuseFailAlloc_357_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
lean_object* v___x_350_; 
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 4, v___x_348_);
v___x_350_ = v___x_339_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_env_330_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_nextMacroScope_331_);
lean_ctor_set(v_reuseFailAlloc_356_, 2, v_ngen_332_);
lean_ctor_set(v_reuseFailAlloc_356_, 3, v_auxDeclNGen_333_);
lean_ctor_set(v_reuseFailAlloc_356_, 4, v___x_348_);
lean_ctor_set(v_reuseFailAlloc_356_, 5, v_cache_334_);
lean_ctor_set(v_reuseFailAlloc_356_, 6, v_messages_335_);
lean_ctor_set(v_reuseFailAlloc_356_, 7, v_infoState_336_);
lean_ctor_set(v_reuseFailAlloc_356_, 8, v_snapshotTasks_337_);
v___x_350_ = v_reuseFailAlloc_356_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_351_ = lean_st_ref_set(v___y_291_, v___x_350_);
v___x_352_ = lean_box(0);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 0, v___x_352_);
v___x_354_ = v___x_326_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_352_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__11___boxed(lean_object* v_oldTraces_364_, lean_object* v_data_365_, lean_object* v_ref_366_, lean_object* v_msg_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__11(v_oldTraces_364_, v_data_365_, v_ref_366_, v_msg_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
lean_dec(v___y_371_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__12___redArg(lean_object* v_x_374_){
_start:
{
if (lean_obj_tag(v_x_374_) == 0)
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
v_a_376_ = lean_ctor_get(v_x_374_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v_x_374_);
if (v_isSharedCheck_383_ == 0)
{
v___x_378_ = v_x_374_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v_x_374_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
lean_ctor_set_tag(v___x_378_, 1);
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_376_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
else
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
v_a_384_ = lean_ctor_get(v_x_374_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v_x_374_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v_x_374_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v_x_374_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
lean_ctor_set_tag(v___x_386_, 0);
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_384_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__12___redArg___boxed(lean_object* v_x_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__12___redArg(v_x_392_);
return v_res_394_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0));
v___x_397_ = l_Lean_stringToMessageData(v___x_396_);
return v___x_397_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__2(void){
_start:
{
lean_object* v___x_398_; double v___x_399_; 
v___x_398_ = lean_unsigned_to_nat(0u);
v___x_399_ = lean_float_of_nat(v___x_398_);
return v___x_399_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__4(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__3));
v___x_402_ = l_Lean_stringToMessageData(v___x_401_);
return v___x_402_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5(void){
_start:
{
lean_object* v___x_403_; double v___x_404_; 
v___x_403_ = lean_unsigned_to_nat(1000u);
v___x_404_ = lean_float_of_nat(v___x_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7(lean_object* v_cls_405_, uint8_t v_collapsed_406_, lean_object* v_tag_407_, lean_object* v_opts_408_, uint8_t v_clsEnabled_409_, lean_object* v_oldTraces_410_, lean_object* v_msg_411_, lean_object* v_resStartStop_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v_fst_418_; lean_object* v_snd_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_517_; 
v_fst_418_ = lean_ctor_get(v_resStartStop_412_, 0);
v_snd_419_ = lean_ctor_get(v_resStartStop_412_, 1);
v_isSharedCheck_517_ = !lean_is_exclusive(v_resStartStop_412_);
if (v_isSharedCheck_517_ == 0)
{
v___x_421_ = v_resStartStop_412_;
v_isShared_422_ = v_isSharedCheck_517_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_snd_419_);
lean_inc(v_fst_418_);
lean_dec(v_resStartStop_412_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_517_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___y_424_; lean_object* v___y_425_; lean_object* v_data_426_; lean_object* v_fst_437_; lean_object* v_snd_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_516_; 
v_fst_437_ = lean_ctor_get(v_snd_419_, 0);
v_snd_438_ = lean_ctor_get(v_snd_419_, 1);
v_isSharedCheck_516_ = !lean_is_exclusive(v_snd_419_);
if (v_isSharedCheck_516_ == 0)
{
v___x_440_ = v_snd_419_;
v_isShared_441_ = v_isSharedCheck_516_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_snd_438_);
lean_inc(v_fst_437_);
lean_dec(v_snd_419_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_516_;
goto v_resetjp_439_;
}
v___jp_423_:
{
lean_object* v___x_427_; 
v___x_427_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__11(v_oldTraces_410_, v_data_426_, v___y_424_, v___y_425_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
lean_dec(v___y_416_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v___x_428_; 
lean_dec_ref(v___x_427_);
v___x_428_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__12___redArg(v_fst_418_);
return v___x_428_;
}
else
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
lean_dec(v_fst_418_);
v_a_429_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v___x_427_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_427_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_429_);
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
v_resetjp_439_:
{
lean_object* v___x_442_; uint8_t v___x_443_; lean_object* v___y_445_; lean_object* v_a_446_; uint8_t v___y_470_; double v___y_501_; 
v___x_442_ = l_Lean_trace_profiler;
v___x_443_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v_opts_408_, v___x_442_);
if (v___x_443_ == 0)
{
v___y_470_ = v___x_443_;
goto v___jp_469_;
}
else
{
lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_506_ = l_Lean_trace_profiler_useHeartbeats;
v___x_507_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v_opts_408_, v___x_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; lean_object* v___x_509_; double v___x_510_; double v___x_511_; double v___x_512_; 
v___x_508_ = l_Lean_trace_profiler_threshold;
v___x_509_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__13(v_opts_408_, v___x_508_);
v___x_510_ = lean_float_of_nat(v___x_509_);
v___x_511_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5);
v___x_512_ = lean_float_div(v___x_510_, v___x_511_);
v___y_501_ = v___x_512_;
goto v___jp_500_;
}
else
{
lean_object* v___x_513_; lean_object* v___x_514_; double v___x_515_; 
v___x_513_ = l_Lean_trace_profiler_threshold;
v___x_514_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__13(v_opts_408_, v___x_513_);
v___x_515_ = lean_float_of_nat(v___x_514_);
v___y_501_ = v___x_515_;
goto v___jp_500_;
}
}
v___jp_444_:
{
uint8_t v_result_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_452_; 
v_result_447_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__10(v_fst_418_);
v___x_448_ = l_Lean_TraceResult_toEmoji(v_result_447_);
v___x_449_ = l_Lean_stringToMessageData(v___x_448_);
v___x_450_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1);
if (v_isShared_441_ == 0)
{
lean_ctor_set_tag(v___x_440_, 7);
lean_ctor_set(v___x_440_, 1, v___x_450_);
lean_ctor_set(v___x_440_, 0, v___x_449_);
v___x_452_ = v___x_440_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_449_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v___x_450_);
v___x_452_ = v_reuseFailAlloc_463_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v_m_454_; 
if (v_isShared_422_ == 0)
{
lean_ctor_set_tag(v___x_421_, 7);
lean_ctor_set(v___x_421_, 1, v_a_446_);
lean_ctor_set(v___x_421_, 0, v___x_452_);
v_m_454_ = v___x_421_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_452_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v_a_446_);
v_m_454_ = v_reuseFailAlloc_462_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
lean_object* v___x_455_; lean_object* v___x_456_; double v___x_457_; lean_object* v_data_458_; 
v___x_455_ = lean_box(v_result_447_);
v___x_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
v___x_457_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__2);
lean_inc_ref(v_tag_407_);
lean_inc_ref(v___x_456_);
lean_inc(v_cls_405_);
v_data_458_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_458_, 0, v_cls_405_);
lean_ctor_set(v_data_458_, 1, v___x_456_);
lean_ctor_set(v_data_458_, 2, v_tag_407_);
lean_ctor_set_float(v_data_458_, sizeof(void*)*3, v___x_457_);
lean_ctor_set_float(v_data_458_, sizeof(void*)*3 + 8, v___x_457_);
lean_ctor_set_uint8(v_data_458_, sizeof(void*)*3 + 16, v_collapsed_406_);
if (v___x_443_ == 0)
{
lean_dec_ref(v___x_456_);
lean_dec(v_snd_438_);
lean_dec(v_fst_437_);
lean_dec_ref(v_tag_407_);
lean_dec(v_cls_405_);
v___y_424_ = v___y_445_;
v___y_425_ = v_m_454_;
v_data_426_ = v_data_458_;
goto v___jp_423_;
}
else
{
lean_object* v_data_459_; double v___x_460_; double v___x_461_; 
lean_dec_ref(v_data_458_);
v_data_459_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_459_, 0, v_cls_405_);
lean_ctor_set(v_data_459_, 1, v___x_456_);
lean_ctor_set(v_data_459_, 2, v_tag_407_);
v___x_460_ = lean_unbox_float(v_fst_437_);
lean_dec(v_fst_437_);
lean_ctor_set_float(v_data_459_, sizeof(void*)*3, v___x_460_);
v___x_461_ = lean_unbox_float(v_snd_438_);
lean_dec(v_snd_438_);
lean_ctor_set_float(v_data_459_, sizeof(void*)*3 + 8, v___x_461_);
lean_ctor_set_uint8(v_data_459_, sizeof(void*)*3 + 16, v_collapsed_406_);
v___y_424_ = v___y_445_;
v___y_425_ = v_m_454_;
v_data_426_ = v_data_459_;
goto v___jp_423_;
}
}
}
}
v___jp_464_:
{
lean_object* v_ref_465_; lean_object* v___x_466_; 
v_ref_465_ = lean_ctor_get(v___y_415_, 5);
lean_inc(v___y_416_);
lean_inc_ref(v___y_415_);
lean_inc(v___y_414_);
lean_inc_ref(v___y_413_);
lean_inc(v_fst_418_);
v___x_466_ = lean_apply_6(v_msg_411_, v_fst_418_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, lean_box(0));
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_a_467_; 
v_a_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_a_467_);
lean_dec_ref(v___x_466_);
lean_inc(v_ref_465_);
v___y_445_ = v_ref_465_;
v_a_446_ = v_a_467_;
goto v___jp_444_;
}
else
{
lean_object* v___x_468_; 
lean_dec_ref(v___x_466_);
v___x_468_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__4);
lean_inc(v_ref_465_);
v___y_445_ = v_ref_465_;
v_a_446_ = v___x_468_;
goto v___jp_444_;
}
}
v___jp_469_:
{
if (v_clsEnabled_409_ == 0)
{
if (v___y_470_ == 0)
{
lean_object* v___x_471_; lean_object* v_traceState_472_; lean_object* v_env_473_; lean_object* v_nextMacroScope_474_; lean_object* v_ngen_475_; lean_object* v_auxDeclNGen_476_; lean_object* v_cache_477_; lean_object* v_messages_478_; lean_object* v_infoState_479_; lean_object* v_snapshotTasks_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_499_; 
lean_del_object(v___x_440_);
lean_dec(v_snd_438_);
lean_dec(v_fst_437_);
lean_del_object(v___x_421_);
lean_dec_ref(v___y_415_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec_ref(v_msg_411_);
lean_dec_ref(v_tag_407_);
lean_dec(v_cls_405_);
v___x_471_ = lean_st_ref_take(v___y_416_);
v_traceState_472_ = lean_ctor_get(v___x_471_, 4);
v_env_473_ = lean_ctor_get(v___x_471_, 0);
v_nextMacroScope_474_ = lean_ctor_get(v___x_471_, 1);
v_ngen_475_ = lean_ctor_get(v___x_471_, 2);
v_auxDeclNGen_476_ = lean_ctor_get(v___x_471_, 3);
v_cache_477_ = lean_ctor_get(v___x_471_, 5);
v_messages_478_ = lean_ctor_get(v___x_471_, 6);
v_infoState_479_ = lean_ctor_get(v___x_471_, 7);
v_snapshotTasks_480_ = lean_ctor_get(v___x_471_, 8);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_499_ == 0)
{
v___x_482_ = v___x_471_;
v_isShared_483_ = v_isSharedCheck_499_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_snapshotTasks_480_);
lean_inc(v_infoState_479_);
lean_inc(v_messages_478_);
lean_inc(v_cache_477_);
lean_inc(v_traceState_472_);
lean_inc(v_auxDeclNGen_476_);
lean_inc(v_ngen_475_);
lean_inc(v_nextMacroScope_474_);
lean_inc(v_env_473_);
lean_dec(v___x_471_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_499_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
uint64_t v_tid_484_; lean_object* v_traces_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_498_; 
v_tid_484_ = lean_ctor_get_uint64(v_traceState_472_, sizeof(void*)*1);
v_traces_485_ = lean_ctor_get(v_traceState_472_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v_traceState_472_);
if (v_isSharedCheck_498_ == 0)
{
v___x_487_ = v_traceState_472_;
v_isShared_488_ = v_isSharedCheck_498_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_traces_485_);
lean_dec(v_traceState_472_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_498_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_489_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_410_, v_traces_485_);
lean_dec_ref(v_traces_485_);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 0, v___x_489_);
v___x_491_ = v___x_487_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_489_);
lean_ctor_set_uint64(v_reuseFailAlloc_497_, sizeof(void*)*1, v_tid_484_);
v___x_491_ = v_reuseFailAlloc_497_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
lean_object* v___x_493_; 
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 4, v___x_491_);
v___x_493_ = v___x_482_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_env_473_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_nextMacroScope_474_);
lean_ctor_set(v_reuseFailAlloc_496_, 2, v_ngen_475_);
lean_ctor_set(v_reuseFailAlloc_496_, 3, v_auxDeclNGen_476_);
lean_ctor_set(v_reuseFailAlloc_496_, 4, v___x_491_);
lean_ctor_set(v_reuseFailAlloc_496_, 5, v_cache_477_);
lean_ctor_set(v_reuseFailAlloc_496_, 6, v_messages_478_);
lean_ctor_set(v_reuseFailAlloc_496_, 7, v_infoState_479_);
lean_ctor_set(v_reuseFailAlloc_496_, 8, v_snapshotTasks_480_);
v___x_493_ = v_reuseFailAlloc_496_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = lean_st_ref_set(v___y_416_, v___x_493_);
lean_dec(v___y_416_);
v___x_495_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__12___redArg(v_fst_418_);
return v___x_495_;
}
}
}
}
}
else
{
goto v___jp_464_;
}
}
else
{
goto v___jp_464_;
}
}
v___jp_500_:
{
double v___x_502_; double v___x_503_; double v___x_504_; uint8_t v___x_505_; 
v___x_502_ = lean_unbox_float(v_snd_438_);
v___x_503_ = lean_unbox_float(v_fst_437_);
v___x_504_ = lean_float_sub(v___x_502_, v___x_503_);
v___x_505_ = lean_float_decLt(v___y_501_, v___x_504_);
v___y_470_ = v___x_505_;
goto v___jp_469_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___boxed(lean_object* v_cls_518_, lean_object* v_collapsed_519_, lean_object* v_tag_520_, lean_object* v_opts_521_, lean_object* v_clsEnabled_522_, lean_object* v_oldTraces_523_, lean_object* v_msg_524_, lean_object* v_resStartStop_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
uint8_t v_collapsed_boxed_531_; uint8_t v_clsEnabled_boxed_532_; lean_object* v_res_533_; 
v_collapsed_boxed_531_ = lean_unbox(v_collapsed_519_);
v_clsEnabled_boxed_532_ = lean_unbox(v_clsEnabled_522_);
v_res_533_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7(v_cls_518_, v_collapsed_boxed_531_, v_tag_520_, v_opts_521_, v_clsEnabled_boxed_532_, v_oldTraces_523_, v_msg_524_, v_resStartStop_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
lean_dec_ref(v_opts_521_);
return v_res_533_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1_spec__2(lean_object* v_a_534_, lean_object* v_as_535_, size_t v_i_536_, size_t v_stop_537_){
_start:
{
uint8_t v___x_538_; 
v___x_538_ = lean_usize_dec_eq(v_i_536_, v_stop_537_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_539_ = lean_array_uget_borrowed(v_as_535_, v_i_536_);
v___x_540_ = lean_name_eq(v_a_534_, v___x_539_);
if (v___x_540_ == 0)
{
size_t v___x_541_; size_t v___x_542_; 
v___x_541_ = ((size_t)1ULL);
v___x_542_ = lean_usize_add(v_i_536_, v___x_541_);
v_i_536_ = v___x_542_;
goto _start;
}
else
{
return v___x_540_;
}
}
else
{
uint8_t v___x_544_; 
v___x_544_ = 0;
return v___x_544_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1_spec__2___boxed(lean_object* v_a_545_, lean_object* v_as_546_, lean_object* v_i_547_, lean_object* v_stop_548_){
_start:
{
size_t v_i_boxed_549_; size_t v_stop_boxed_550_; uint8_t v_res_551_; lean_object* v_r_552_; 
v_i_boxed_549_ = lean_unbox_usize(v_i_547_);
lean_dec(v_i_547_);
v_stop_boxed_550_ = lean_unbox_usize(v_stop_548_);
lean_dec(v_stop_548_);
v_res_551_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1_spec__2(v_a_545_, v_as_546_, v_i_boxed_549_, v_stop_boxed_550_);
lean_dec_ref(v_as_546_);
lean_dec(v_a_545_);
v_r_552_ = lean_box(v_res_551_);
return v_r_552_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1(lean_object* v_as_553_, lean_object* v_a_554_){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_555_ = lean_unsigned_to_nat(0u);
v___x_556_ = lean_array_get_size(v_as_553_);
v___x_557_ = lean_nat_dec_lt(v___x_555_, v___x_556_);
if (v___x_557_ == 0)
{
return v___x_557_;
}
else
{
if (v___x_557_ == 0)
{
return v___x_557_;
}
else
{
size_t v___x_558_; size_t v___x_559_; uint8_t v___x_560_; 
v___x_558_ = ((size_t)0ULL);
v___x_559_ = lean_usize_of_nat(v___x_556_);
v___x_560_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1_spec__2(v_a_554_, v_as_553_, v___x_558_, v___x_559_);
return v___x_560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1___boxed(lean_object* v_as_561_, lean_object* v_a_562_){
_start:
{
uint8_t v_res_563_; lean_object* v_r_564_; 
v_res_563_ = l_Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1(v_as_561_, v_a_562_);
lean_dec(v_a_562_);
lean_dec_ref(v_as_561_);
v_r_564_ = lean_box(v_res_563_);
return v_r_564_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0(lean_object* v_msg_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v_toApplicative_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_639_; 
v___x_576_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__0);
v___x_577_ = l_ReaderT_instMonad___redArg(v___x_576_);
v_toApplicative_578_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_639_ == 0)
{
lean_object* v_unused_640_; 
v_unused_640_ = lean_ctor_get(v___x_577_, 1);
lean_dec(v_unused_640_);
v___x_580_ = v___x_577_;
v_isShared_581_ = v_isSharedCheck_639_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_toApplicative_578_);
lean_dec(v___x_577_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_639_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v_toFunctor_582_; lean_object* v_toSeq_583_; lean_object* v_toSeqLeft_584_; lean_object* v_toSeqRight_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_637_; 
v_toFunctor_582_ = lean_ctor_get(v_toApplicative_578_, 0);
v_toSeq_583_ = lean_ctor_get(v_toApplicative_578_, 2);
v_toSeqLeft_584_ = lean_ctor_get(v_toApplicative_578_, 3);
v_toSeqRight_585_ = lean_ctor_get(v_toApplicative_578_, 4);
v_isSharedCheck_637_ = !lean_is_exclusive(v_toApplicative_578_);
if (v_isSharedCheck_637_ == 0)
{
lean_object* v_unused_638_; 
v_unused_638_ = lean_ctor_get(v_toApplicative_578_, 1);
lean_dec(v_unused_638_);
v___x_587_ = v_toApplicative_578_;
v_isShared_588_ = v_isSharedCheck_637_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_toSeqRight_585_);
lean_inc(v_toSeqLeft_584_);
lean_inc(v_toSeq_583_);
lean_inc(v_toFunctor_582_);
lean_dec(v_toApplicative_578_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_637_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___f_589_; lean_object* v___f_590_; lean_object* v___f_591_; lean_object* v___f_592_; lean_object* v___x_593_; lean_object* v___f_594_; lean_object* v___f_595_; lean_object* v___f_596_; lean_object* v___x_598_; 
v___f_589_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__1));
v___f_590_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_582_);
v___f_591_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_591_, 0, v_toFunctor_582_);
v___f_592_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_592_, 0, v_toFunctor_582_);
v___x_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_593_, 0, v___f_591_);
lean_ctor_set(v___x_593_, 1, v___f_592_);
v___f_594_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_594_, 0, v_toSeqRight_585_);
v___f_595_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_595_, 0, v_toSeqLeft_584_);
v___f_596_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_596_, 0, v_toSeq_583_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 4, v___f_594_);
lean_ctor_set(v___x_587_, 3, v___f_595_);
lean_ctor_set(v___x_587_, 2, v___f_596_);
lean_ctor_set(v___x_587_, 1, v___f_589_);
lean_ctor_set(v___x_587_, 0, v___x_593_);
v___x_598_ = v___x_587_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_593_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v___f_589_);
lean_ctor_set(v_reuseFailAlloc_636_, 2, v___f_596_);
lean_ctor_set(v_reuseFailAlloc_636_, 3, v___f_595_);
lean_ctor_set(v_reuseFailAlloc_636_, 4, v___f_594_);
v___x_598_ = v_reuseFailAlloc_636_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v___x_600_; 
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 1, v___f_590_);
lean_ctor_set(v___x_580_, 0, v___x_598_);
v___x_600_ = v___x_580_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_598_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v___f_590_);
v___x_600_ = v_reuseFailAlloc_635_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_601_; lean_object* v_toApplicative_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_633_; 
v___x_601_ = l_ReaderT_instMonad___redArg(v___x_600_);
v_toApplicative_602_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_633_ == 0)
{
lean_object* v_unused_634_; 
v_unused_634_ = lean_ctor_get(v___x_601_, 1);
lean_dec(v_unused_634_);
v___x_604_ = v___x_601_;
v_isShared_605_ = v_isSharedCheck_633_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_toApplicative_602_);
lean_dec(v___x_601_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_633_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v_toFunctor_606_; lean_object* v_toSeq_607_; lean_object* v_toSeqLeft_608_; lean_object* v_toSeqRight_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_631_; 
v_toFunctor_606_ = lean_ctor_get(v_toApplicative_602_, 0);
v_toSeq_607_ = lean_ctor_get(v_toApplicative_602_, 2);
v_toSeqLeft_608_ = lean_ctor_get(v_toApplicative_602_, 3);
v_toSeqRight_609_ = lean_ctor_get(v_toApplicative_602_, 4);
v_isSharedCheck_631_ = !lean_is_exclusive(v_toApplicative_602_);
if (v_isSharedCheck_631_ == 0)
{
lean_object* v_unused_632_; 
v_unused_632_ = lean_ctor_get(v_toApplicative_602_, 1);
lean_dec(v_unused_632_);
v___x_611_ = v_toApplicative_602_;
v_isShared_612_ = v_isSharedCheck_631_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_toSeqRight_609_);
lean_inc(v_toSeqLeft_608_);
lean_inc(v_toSeq_607_);
lean_inc(v_toFunctor_606_);
lean_dec(v_toApplicative_602_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_631_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___f_613_; lean_object* v___f_614_; lean_object* v___f_615_; lean_object* v___f_616_; lean_object* v___x_617_; lean_object* v___f_618_; lean_object* v___f_619_; lean_object* v___f_620_; lean_object* v___x_622_; 
v___f_613_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__3));
v___f_614_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__4));
lean_inc_ref(v_toFunctor_606_);
v___f_615_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_615_, 0, v_toFunctor_606_);
v___f_616_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_616_, 0, v_toFunctor_606_);
v___x_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_617_, 0, v___f_615_);
lean_ctor_set(v___x_617_, 1, v___f_616_);
v___f_618_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_618_, 0, v_toSeqRight_609_);
v___f_619_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_619_, 0, v_toSeqLeft_608_);
v___f_620_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_620_, 0, v_toSeq_607_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 4, v___f_618_);
lean_ctor_set(v___x_611_, 3, v___f_619_);
lean_ctor_set(v___x_611_, 2, v___f_620_);
lean_ctor_set(v___x_611_, 1, v___f_613_);
lean_ctor_set(v___x_611_, 0, v___x_617_);
v___x_622_ = v___x_611_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v___f_613_);
lean_ctor_set(v_reuseFailAlloc_630_, 2, v___f_620_);
lean_ctor_set(v_reuseFailAlloc_630_, 3, v___f_619_);
lean_ctor_set(v_reuseFailAlloc_630_, 4, v___f_618_);
v___x_622_ = v_reuseFailAlloc_630_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_624_; 
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 1, v___f_614_);
lean_ctor_set(v___x_604_, 0, v___x_622_);
v___x_624_ = v___x_604_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v___f_614_);
v___x_624_ = v_reuseFailAlloc_629_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_10855__overap_627_; lean_object* v___x_628_; 
v___x_625_ = lean_box(0);
v___x_626_ = l_instInhabitedOfMonad___redArg(v___x_624_, v___x_625_);
v___x_10855__overap_627_ = lean_panic_fn(v___x_626_, v_msg_570_);
v___x_628_ = lean_apply_5(v___x_10855__overap_627_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, lean_box(0));
return v___x_628_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___boxed(lean_object* v_msg_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0(v_msg_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
return v_res_647_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__1(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__0));
v___x_650_ = l_Lean_stringToMessageData(v___x_649_);
return v___x_650_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__3(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__2));
v___x_653_ = l_Lean_stringToMessageData(v___x_652_);
return v___x_653_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__7(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_657_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__6));
v___x_658_ = lean_unsigned_to_nat(11u);
v___x_659_ = lean_unsigned_to_nat(122u);
v___x_660_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__5));
v___x_661_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__4));
v___x_662_ = l_mkPanicMessageWithDecl(v___x_661_, v___x_660_, v___x_659_, v___x_658_, v___x_657_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0(lean_object* v_constName_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v___x_677_; lean_object* v_env_678_; uint8_t v___x_679_; lean_object* v___x_680_; 
v___x_677_ = lean_st_ref_get(v___y_667_);
v_env_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc_ref(v_env_678_);
lean_dec(v___x_677_);
v___x_679_ = 0;
lean_inc(v_constName_663_);
v___x_680_ = l_Lean_Environment_findAsync_x3f(v_env_678_, v_constName_663_, v___x_679_);
if (lean_obj_tag(v___x_680_) == 1)
{
lean_object* v_val_681_; uint8_t v_kind_682_; 
v_val_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_val_681_);
lean_dec_ref(v___x_680_);
v_kind_682_ = lean_ctor_get_uint8(v_val_681_, sizeof(void*)*3);
if (v_kind_682_ == 6)
{
lean_object* v___x_683_; 
v___x_683_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_681_);
if (lean_obj_tag(v___x_683_) == 6)
{
lean_object* v_val_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v_constName_663_);
v_val_684_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___x_683_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_val_684_);
lean_dec(v___x_683_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
lean_ctor_set_tag(v___x_686_, 0);
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_val_684_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
else
{
lean_object* v___x_692_; lean_object* v___x_693_; 
lean_dec_ref(v___x_683_);
v___x_692_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__7);
lean_inc(v___y_667_);
lean_inc_ref(v___y_666_);
lean_inc(v___y_665_);
lean_inc_ref(v___y_664_);
v___x_693_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0(v___x_692_, v___y_664_, v___y_665_, v___y_666_, v___y_667_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_702_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_702_ == 0)
{
v___x_696_ = v___x_693_;
v_isShared_697_ = v_isSharedCheck_702_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_693_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_702_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
if (lean_obj_tag(v_a_694_) == 0)
{
lean_del_object(v___x_696_);
goto v___jp_669_;
}
else
{
lean_object* v_val_698_; lean_object* v___x_700_; 
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v_constName_663_);
v_val_698_ = lean_ctor_get(v_a_694_, 0);
lean_inc(v_val_698_);
lean_dec_ref(v_a_694_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v_val_698_);
v___x_700_ = v___x_696_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_val_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
else
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v_constName_663_);
v_a_703_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_693_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_693_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_703_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
}
else
{
lean_dec(v_val_681_);
goto v___jp_669_;
}
}
else
{
lean_dec(v___x_680_);
goto v___jp_669_;
}
v___jp_669_:
{
lean_object* v___x_670_; uint8_t v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_670_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__1);
v___x_671_ = 0;
v___x_672_ = l_Lean_MessageData_ofConstName(v_constName_663_, v___x_671_);
v___x_673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_670_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__3);
v___x_675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_673_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
v___x_676_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_675_, v___y_664_, v___y_665_, v___y_666_, v___y_667_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
return v___x_676_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___boxed(lean_object* v_constName_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0(v_constName_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_reduceSparseCasesOn_spec__2(size_t v_sz_718_, size_t v_i_719_, lean_object* v_bs_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
uint8_t v___x_726_; 
v___x_726_ = lean_usize_dec_lt(v_i_719_, v_sz_718_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; 
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v_bs_720_);
return v___x_727_;
}
else
{
lean_object* v_v_728_; lean_object* v___x_729_; 
v_v_728_ = lean_array_uget_borrowed(v_bs_720_, v_i_719_);
lean_inc(v___y_724_);
lean_inc_ref(v___y_723_);
lean_inc(v___y_722_);
lean_inc_ref(v___y_721_);
lean_inc(v_v_728_);
v___x_729_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0(v_v_728_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; lean_object* v_cidx_731_; lean_object* v___x_732_; lean_object* v_bs_x27_733_; size_t v___x_734_; size_t v___x_735_; lean_object* v___x_736_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_730_);
lean_dec_ref(v___x_729_);
v_cidx_731_ = lean_ctor_get(v_a_730_, 2);
lean_inc(v_cidx_731_);
lean_dec(v_a_730_);
v___x_732_ = lean_unsigned_to_nat(0u);
v_bs_x27_733_ = lean_array_uset(v_bs_720_, v_i_719_, v___x_732_);
v___x_734_ = ((size_t)1ULL);
v___x_735_ = lean_usize_add(v_i_719_, v___x_734_);
v___x_736_ = lean_array_uset(v_bs_x27_733_, v_i_719_, v_cidx_731_);
v_i_719_ = v___x_735_;
v_bs_720_ = v___x_736_;
goto _start;
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec_ref(v_bs_720_);
v_a_738_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_729_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_729_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_reduceSparseCasesOn_spec__2___boxed(lean_object* v_sz_746_, lean_object* v_i_747_, lean_object* v_bs_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
size_t v_sz_boxed_754_; size_t v_i_boxed_755_; lean_object* v_res_756_; 
v_sz_boxed_754_ = lean_unbox_usize(v_sz_746_);
lean_dec(v_sz_746_);
v_i_boxed_755_ = lean_unbox_usize(v_i_747_);
lean_dec(v_i_747_);
v_res_756_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_reduceSparseCasesOn_spec__2(v_sz_boxed_754_, v_i_boxed_755_, v_bs_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
return v_res_756_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__0(void){
_start:
{
lean_object* v___x_757_; lean_object* v_dummy_758_; 
v___x_757_ = lean_box(0);
v_dummy_758_ = l_Lean_Expr_sort___override(v___x_757_);
return v_dummy_758_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__2(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__1));
v___x_761_ = l_Lean_stringToMessageData(v___x_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0(lean_object* v___x_762_, lean_object* v_x_763_, lean_object* v_majorPos_764_, lean_object* v_insterestingCtors_765_, lean_object* v_declName_766_, lean_object* v_snd_767_, lean_object* v_arity_768_, lean_object* v_mvarId_769_, lean_object* v___f_770_, lean_object* v_____r_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = lean_array_get_borrowed(v___x_762_, v_x_763_, v_majorPos_764_);
lean_inc(v___y_775_);
lean_inc_ref(v___y_774_);
lean_inc(v___y_773_);
lean_inc_ref(v___y_772_);
lean_inc(v___x_777_);
v___x_778_ = l_Lean_Meta_isConstructorApp_x27_x3f(v___x_777_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
lean_inc(v_a_779_);
lean_dec_ref(v___x_778_);
if (lean_obj_tag(v_a_779_) == 1)
{
lean_object* v_val_780_; lean_object* v_toConstantVal_781_; lean_object* v_cidx_782_; lean_object* v_name_783_; uint8_t v___x_784_; 
v_val_780_ = lean_ctor_get(v_a_779_, 0);
lean_inc(v_val_780_);
lean_dec_ref(v_a_779_);
v_toConstantVal_781_ = lean_ctor_get(v_val_780_, 0);
lean_inc_ref(v_toConstantVal_781_);
v_cidx_782_ = lean_ctor_get(v_val_780_, 2);
lean_inc(v_cidx_782_);
lean_dec(v_val_780_);
v_name_783_ = lean_ctor_get(v_toConstantVal_781_, 0);
lean_inc(v_name_783_);
lean_dec_ref(v_toConstantVal_781_);
v___x_784_ = l_Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1(v_insterestingCtors_765_, v_name_783_);
lean_dec(v_name_783_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; 
lean_dec_ref(v___f_770_);
lean_inc(v___y_775_);
lean_inc_ref(v___y_774_);
lean_inc(v___y_773_);
lean_inc_ref(v___y_772_);
v___x_785_ = l_Lean_Meta_getSparseCasesOnEq(v_declName_766_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; size_t v_sz_787_; size_t v___x_788_; lean_object* v___x_789_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_a_786_);
lean_dec_ref(v___x_785_);
v_sz_787_ = lean_array_size(v_insterestingCtors_765_);
v___x_788_ = ((size_t)0ULL);
lean_inc(v___y_775_);
lean_inc_ref(v___y_774_);
lean_inc(v___y_773_);
lean_inc_ref(v___y_772_);
v___x_789_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_reduceSparseCasesOn_spec__2(v_sz_787_, v___x_788_, v_insterestingCtors_765_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_a_790_);
lean_dec_ref(v___x_789_);
v___x_791_ = l_Lean_mkRawNatLit(v_cidx_782_);
lean_inc(v___y_775_);
lean_inc_ref(v___y_774_);
lean_inc(v___y_773_);
lean_inc_ref(v___y_772_);
v___x_792_ = l_mkHasNotBitProof(v___x_791_, v_a_790_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
lean_dec(v_a_790_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v___x_794_; lean_object* v_nargs_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v_dummy_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_a_793_);
lean_dec_ref(v___x_792_);
v___x_794_ = l_Lean_Expr_getAppFn(v_snd_767_);
v_nargs_795_ = l_Lean_Expr_getAppNumArgs(v_snd_767_);
v___x_796_ = l_Lean_Expr_constLevels_x21(v___x_794_);
lean_dec_ref(v___x_794_);
v___x_797_ = l_Lean_mkConst(v_a_786_, v___x_796_);
v_dummy_798_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__0);
lean_inc(v_nargs_795_);
v___x_799_ = lean_mk_array(v_nargs_795_, v_dummy_798_);
v___x_800_ = lean_unsigned_to_nat(1u);
v___x_801_ = lean_nat_sub(v_nargs_795_, v___x_800_);
lean_dec(v_nargs_795_);
v___x_802_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_snd_767_, v___x_799_, v___x_801_);
v___x_803_ = lean_unsigned_to_nat(0u);
v___x_804_ = l_Array_toSubarray___redArg(v___x_802_, v___x_803_, v_arity_768_);
v___x_805_ = l_Subarray_copy___redArg(v___x_804_);
v___x_806_ = l_Lean_mkAppN(v___x_797_, v___x_805_);
lean_dec_ref(v___x_805_);
v___x_807_ = l_Lean_Expr_app___override(v___x_806_, v_a_793_);
v___x_808_ = l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq(v_mvarId_769_, v___x_807_, v___x_784_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_818_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_818_ == 0)
{
v___x_811_ = v___x_808_;
v_isShared_812_ = v_isSharedCheck_818_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_808_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_818_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_816_; 
v___x_813_ = lean_mk_empty_array_with_capacity(v___x_800_);
v___x_814_ = lean_array_push(v___x_813_, v_a_809_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v___x_814_);
v___x_816_ = v___x_811_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
v_a_819_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_808_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_808_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec(v_a_786_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v_mvarId_769_);
lean_dec(v_arity_768_);
lean_dec_ref(v_snd_767_);
v_a_827_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_792_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_792_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
lean_dec(v_a_786_);
lean_dec(v_cidx_782_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v_mvarId_769_);
lean_dec(v_arity_768_);
lean_dec_ref(v_snd_767_);
v_a_835_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_789_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_789_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
else
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
lean_dec(v_cidx_782_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v_mvarId_769_);
lean_dec(v_arity_768_);
lean_dec_ref(v_snd_767_);
lean_dec_ref(v_insterestingCtors_765_);
v_a_843_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_785_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_785_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
else
{
lean_object* v___x_851_; 
lean_dec(v_cidx_782_);
lean_dec(v_arity_768_);
lean_dec_ref(v_snd_767_);
lean_dec(v_declName_766_);
lean_dec_ref(v_insterestingCtors_765_);
v___x_851_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_769_, v___f_770_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_862_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_862_ == 0)
{
v___x_854_ = v___x_851_;
v_isShared_855_ = v_isSharedCheck_862_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_851_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_862_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_856_ = lean_unsigned_to_nat(1u);
v___x_857_ = lean_mk_empty_array_with_capacity(v___x_856_);
v___x_858_ = lean_array_push(v___x_857_, v_a_852_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v___x_858_);
v___x_860_ = v___x_854_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_858_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
else
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
v_a_863_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___x_851_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_851_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_863_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
}
else
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
lean_dec(v_a_779_);
lean_dec_ref(v___f_770_);
lean_dec(v_mvarId_769_);
lean_dec(v_arity_768_);
lean_dec_ref(v_snd_767_);
lean_dec(v_declName_766_);
lean_dec_ref(v_insterestingCtors_765_);
v___x_871_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__2);
lean_inc(v___x_777_);
v___x_872_ = l_Lean_indentExpr(v___x_777_);
v___x_873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_871_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_873_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
return v___x_874_;
}
}
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec_ref(v___f_770_);
lean_dec(v_mvarId_769_);
lean_dec(v_arity_768_);
lean_dec_ref(v_snd_767_);
lean_dec(v_declName_766_);
lean_dec_ref(v_insterestingCtors_765_);
v_a_875_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_778_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_778_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___boxed(lean_object* v___x_883_, lean_object* v_x_884_, lean_object* v_majorPos_885_, lean_object* v_insterestingCtors_886_, lean_object* v_declName_887_, lean_object* v_snd_888_, lean_object* v_arity_889_, lean_object* v_mvarId_890_, lean_object* v___f_891_, lean_object* v_____r_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0(v___x_883_, v_x_884_, v_majorPos_885_, v_insterestingCtors_886_, v_declName_887_, v_snd_888_, v_arity_889_, v_mvarId_890_, v___f_891_, v_____r_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
lean_dec(v_majorPos_885_);
lean_dec_ref(v_x_884_);
return v_res_898_;
}
}
static double _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__7(void){
_start:
{
lean_object* v___x_909_; double v___x_910_; 
v___x_909_ = lean_unsigned_to_nat(1000000000u);
v___x_910_ = lean_float_of_nat(v___x_909_);
return v___x_910_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__9(void){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__8));
v___x_913_ = l_Lean_stringToMessageData(v___x_912_);
return v___x_913_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__11(void){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__10));
v___x_916_ = l_Lean_stringToMessageData(v___x_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8(lean_object* v_snd_917_, lean_object* v_mvarId_918_, lean_object* v_x_919_, lean_object* v_x_920_, lean_object* v_x_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
if (lean_obj_tag(v_x_919_) == 5)
{
lean_object* v_fn_927_; lean_object* v_arg_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v_fn_927_ = lean_ctor_get(v_x_919_, 0);
lean_inc_ref(v_fn_927_);
v_arg_928_ = lean_ctor_get(v_x_919_, 1);
lean_inc_ref(v_arg_928_);
lean_dec_ref(v_x_919_);
v___x_929_ = lean_array_set(v_x_920_, v_x_921_, v_arg_928_);
v___x_930_ = lean_unsigned_to_nat(1u);
v___x_931_ = lean_nat_sub(v_x_921_, v___x_930_);
lean_dec(v_x_921_);
v_x_919_ = v_fn_927_;
v_x_920_ = v___x_929_;
v_x_921_ = v___x_931_;
goto _start;
}
else
{
lean_dec(v_x_921_);
if (lean_obj_tag(v_x_919_) == 4)
{
lean_object* v_declName_933_; lean_object* v___x_934_; 
v_declName_933_ = lean_ctor_get(v_x_919_, 0);
lean_inc(v_declName_933_);
lean_dec_ref(v_x_919_);
lean_inc(v_declName_933_);
v___x_934_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_declName_933_, v___y_925_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v_a_935_; 
v_a_935_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_a_935_);
lean_dec_ref(v___x_934_);
if (lean_obj_tag(v_a_935_) == 1)
{
lean_object* v_val_936_; lean_object* v_options_937_; lean_object* v_majorPos_938_; lean_object* v_arity_939_; lean_object* v_insterestingCtors_940_; uint8_t v_hasTrace_941_; lean_object* v___f_942_; lean_object* v___x_943_; lean_object* v___f_944_; lean_object* v___x_945_; uint8_t v___x_946_; 
v_val_936_ = lean_ctor_get(v_a_935_, 0);
lean_inc(v_val_936_);
lean_dec_ref(v_a_935_);
v_options_937_ = lean_ctor_get(v___y_924_, 2);
v_majorPos_938_ = lean_ctor_get(v_val_936_, 1);
lean_inc(v_majorPos_938_);
v_arity_939_ = lean_ctor_get(v_val_936_, 2);
lean_inc(v_arity_939_);
v_insterestingCtors_940_ = lean_ctor_get(v_val_936_, 3);
lean_inc_ref(v_insterestingCtors_940_);
lean_dec(v_val_936_);
v_hasTrace_941_ = lean_ctor_get_uint8(v_options_937_, sizeof(void*)*1);
v___f_942_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__0));
v___x_943_ = l_Lean_instInhabitedExpr;
lean_inc(v_arity_939_);
lean_inc_ref(v_x_920_);
v___f_944_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___boxed), 15, 9);
lean_closure_set(v___f_944_, 0, v___x_943_);
lean_closure_set(v___f_944_, 1, v_x_920_);
lean_closure_set(v___f_944_, 2, v_majorPos_938_);
lean_closure_set(v___f_944_, 3, v_insterestingCtors_940_);
lean_closure_set(v___f_944_, 4, v_declName_933_);
lean_closure_set(v___f_944_, 5, v_snd_917_);
lean_closure_set(v___f_944_, 6, v_arity_939_);
lean_closure_set(v___f_944_, 7, v_mvarId_918_);
lean_closure_set(v___f_944_, 8, v___f_942_);
v___x_945_ = lean_array_get_size(v_x_920_);
lean_dec_ref(v_x_920_);
v___x_946_ = lean_nat_dec_lt(v___x_945_, v_arity_939_);
lean_dec(v_arity_939_);
if (v_hasTrace_941_ == 0)
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1(v___x_946_, v___f_944_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
return v___x_947_;
}
else
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v_a_950_; lean_object* v___f_951_; lean_object* v___x_952_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v_a_956_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v_a_972_; uint8_t v___x_1023_; 
v___x_948_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__4));
v___x_949_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___x_948_, v___y_924_);
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
lean_dec_ref(v___x_949_);
v___f_951_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__5));
v___x_952_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__6));
v___x_1023_ = lean_unbox(v_a_950_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1024_; uint8_t v___x_1025_; 
v___x_1024_ = l_Lean_trace_profiler;
v___x_1025_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v_options_937_, v___x_1024_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; 
lean_dec(v_a_950_);
v___x_1026_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1(v___x_946_, v___f_944_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
return v___x_1026_;
}
else
{
lean_inc_ref(v_options_937_);
goto v___jp_982_;
}
}
else
{
lean_inc_ref(v_options_937_);
goto v___jp_982_;
}
v___jp_953_:
{
lean_object* v___x_957_; double v___x_958_; double v___x_959_; double v___x_960_; double v___x_961_; double v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; uint8_t v___x_967_; lean_object* v___x_968_; 
v___x_957_ = lean_io_mono_nanos_now();
v___x_958_ = lean_float_of_nat(v___y_954_);
v___x_959_ = lean_float_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__7);
v___x_960_ = lean_float_div(v___x_958_, v___x_959_);
v___x_961_ = lean_float_of_nat(v___x_957_);
v___x_962_ = lean_float_div(v___x_961_, v___x_959_);
v___x_963_ = lean_box_float(v___x_960_);
v___x_964_ = lean_box_float(v___x_962_);
v___x_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_963_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_966_, 0, v_a_956_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = lean_unbox(v_a_950_);
lean_dec(v_a_950_);
v___x_968_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7(v___x_948_, v_hasTrace_941_, v___x_952_, v_options_937_, v___x_967_, v___y_955_, v___f_951_, v___x_966_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
lean_dec_ref(v_options_937_);
return v___x_968_;
}
v___jp_969_:
{
lean_object* v___x_973_; double v___x_974_; double v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; uint8_t v___x_980_; lean_object* v___x_981_; 
v___x_973_ = lean_io_get_num_heartbeats();
v___x_974_ = lean_float_of_nat(v___y_970_);
v___x_975_ = lean_float_of_nat(v___x_973_);
v___x_976_ = lean_box_float(v___x_974_);
v___x_977_ = lean_box_float(v___x_975_);
v___x_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_976_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___x_979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_979_, 0, v_a_972_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
v___x_980_ = lean_unbox(v_a_950_);
lean_dec(v_a_950_);
v___x_981_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7(v___x_948_, v_hasTrace_941_, v___x_952_, v_options_937_, v___x_980_, v___y_971_, v___f_951_, v___x_979_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
lean_dec_ref(v_options_937_);
return v___x_981_;
}
v___jp_982_:
{
lean_object* v___x_983_; lean_object* v_a_984_; lean_object* v___x_985_; uint8_t v___x_986_; 
v___x_983_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__5___redArg(v___y_925_);
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
lean_dec_ref(v___x_983_);
v___x_985_ = l_Lean_trace_profiler_useHeartbeats;
v___x_986_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v_options_937_, v___x_985_);
if (v___x_986_ == 0)
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = lean_io_mono_nanos_now();
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
lean_inc(v___y_923_);
lean_inc_ref(v___y_922_);
v___x_988_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1(v___x_946_, v___f_944_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_988_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_988_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
lean_ctor_set_tag(v___x_991_, 1);
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_a_989_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
v___y_954_ = v___x_987_;
v___y_955_ = v_a_984_;
v_a_956_ = v___x_994_;
goto v___jp_953_;
}
}
}
else
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
v_a_997_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_988_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_988_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
lean_ctor_set_tag(v___x_999_, 0);
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_997_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
v___y_954_ = v___x_987_;
v___y_955_ = v_a_984_;
v_a_956_ = v___x_1002_;
goto v___jp_953_;
}
}
}
}
else
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = lean_io_get_num_heartbeats();
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
lean_inc(v___y_923_);
lean_inc_ref(v___y_922_);
v___x_1006_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1(v___x_946_, v___f_944_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_1006_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_1006_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
lean_ctor_set_tag(v___x_1009_, 1);
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
v___y_970_ = v___x_1005_;
v___y_971_ = v_a_984_;
v_a_972_ = v___x_1012_;
goto v___jp_969_;
}
}
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
v_a_1015_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_1006_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1006_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
lean_ctor_set_tag(v___x_1017_, 0);
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
v___y_970_ = v___x_1005_;
v___y_971_ = v_a_984_;
v_a_972_ = v___x_1020_;
goto v___jp_969_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
lean_dec(v_a_935_);
lean_dec(v_declName_933_);
lean_dec_ref(v_x_920_);
lean_dec(v_mvarId_918_);
lean_dec_ref(v_snd_917_);
v___x_1027_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__9, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__9_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__9);
v___x_1028_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1027_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
return v___x_1028_;
}
}
else
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
lean_dec(v_declName_933_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec_ref(v_x_920_);
lean_dec(v_mvarId_918_);
lean_dec_ref(v_snd_917_);
v_a_1029_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_934_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_934_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1029_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
else
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
lean_dec_ref(v_x_920_);
lean_dec_ref(v_x_919_);
lean_dec(v_mvarId_918_);
lean_dec_ref(v_snd_917_);
v___x_1037_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__11, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__11_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__11);
v___x_1038_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1037_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
return v___x_1038_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___boxed(lean_object* v_snd_1039_, lean_object* v_mvarId_1040_, lean_object* v_x_1041_, lean_object* v_x_1042_, lean_object* v_x_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8(v_snd_1039_, v_mvarId_1040_, v_x_1041_, v_x_1042_, v_x_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
return v_res_1049_;
}
}
static lean_object* _init_l_Lean_Meta_reduceSparseCasesOn___closed__1(void){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = ((lean_object*)(l_Lean_Meta_reduceSparseCasesOn___closed__0));
v___x_1052_ = l_Lean_stringToMessageData(v___x_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceSparseCasesOn(lean_object* v_mvarId_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v___x_1059_; 
lean_inc(v_mvarId_1053_);
v___x_1059_ = l_Lean_MVarId_getType(v_mvarId_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1061_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1060_);
lean_dec_ref(v___x_1059_);
lean_inc(v_a_1057_);
lean_inc_ref(v_a_1056_);
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
v___x_1061_ = l_Lean_Meta_matchEqHEqLHS_x3f(v_a_1060_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_a_1062_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
lean_inc(v_a_1062_);
lean_dec_ref(v___x_1061_);
if (lean_obj_tag(v_a_1062_) == 1)
{
lean_object* v_val_1063_; lean_object* v_snd_1064_; lean_object* v_dummy_1065_; lean_object* v_nargs_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v_val_1063_ = lean_ctor_get(v_a_1062_, 0);
lean_inc(v_val_1063_);
lean_dec_ref(v_a_1062_);
v_snd_1064_ = lean_ctor_get(v_val_1063_, 1);
lean_inc(v_snd_1064_);
lean_dec(v_val_1063_);
v_dummy_1065_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__0);
v_nargs_1066_ = l_Lean_Expr_getAppNumArgs(v_snd_1064_);
lean_inc(v_nargs_1066_);
v___x_1067_ = lean_mk_array(v_nargs_1066_, v_dummy_1065_);
v___x_1068_ = lean_unsigned_to_nat(1u);
v___x_1069_ = lean_nat_sub(v_nargs_1066_, v___x_1068_);
lean_dec(v_nargs_1066_);
lean_inc(v_snd_1064_);
v___x_1070_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8(v_snd_1064_, v_mvarId_1053_, v_snd_1064_, v___x_1067_, v___x_1069_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
return v___x_1070_;
}
else
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
lean_dec(v_a_1062_);
lean_dec(v_mvarId_1053_);
v___x_1071_ = lean_obj_once(&l_Lean_Meta_reduceSparseCasesOn___closed__1, &l_Lean_Meta_reduceSparseCasesOn___closed__1_once, _init_l_Lean_Meta_reduceSparseCasesOn___closed__1);
v___x_1072_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1071_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
return v___x_1072_;
}
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_mvarId_1053_);
v_a_1073_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1061_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1061_);
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
else
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_mvarId_1053_);
v_a_1081_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_1059_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1059_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceSparseCasesOn___boxed(lean_object* v_mvarId_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lean_Meta_reduceSparseCasesOn(v_mvarId_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3(lean_object* v_00_u03b1_1096_, lean_object* v_msg_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v___x_1103_; 
v___x_1103_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v_msg_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___boxed(lean_object* v_00_u03b1_1104_, lean_object* v_msg_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3(v_00_u03b1_1104_, v_msg_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__12(lean_object* v_00_u03b1_1112_, lean_object* v_x_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__12___redArg(v_x_1113_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__12___boxed(lean_object* v_00_u03b1_1120_, lean_object* v_x_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7_spec__12(v_00_u03b1_1120_, v_x_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(lean_object* v_mvarId_1128_, lean_object* v_x_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1128_, v_x_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1135_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1135_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1136_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
v_a_1144_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_1135_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1135_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1144_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg___boxed(lean_object* v_mvarId_1152_, lean_object* v_x_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1152_, v_x_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2(lean_object* v_00_u03b1_1160_, lean_object* v_mvarId_1161_, lean_object* v_x_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1161_, v_x_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___boxed(lean_object* v_00_u03b1_1169_, lean_object* v_mvarId_1170_, lean_object* v_x_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2(v_00_u03b1_1169_, v_mvarId_1170_, v_x_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_splitSparseCasesOn_spec__1(lean_object* v_a_1178_, lean_object* v_a_1179_){
_start:
{
if (lean_obj_tag(v_a_1178_) == 0)
{
lean_object* v___x_1180_; 
v___x_1180_ = l_List_reverse___redArg(v_a_1179_);
return v___x_1180_;
}
else
{
lean_object* v_head_1181_; lean_object* v_tail_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1191_; 
v_head_1181_ = lean_ctor_get(v_a_1178_, 0);
v_tail_1182_ = lean_ctor_get(v_a_1178_, 1);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_a_1178_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1184_ = v_a_1178_;
v_isShared_1185_ = v_isSharedCheck_1191_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_tail_1182_);
lean_inc(v_head_1181_);
lean_dec(v_a_1178_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1191_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1186_; lean_object* v___x_1188_; 
v___x_1186_ = l_Lean_MessageData_ofExpr(v_head_1181_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 1, v_a_1179_);
lean_ctor_set(v___x_1184_, 0, v___x_1186_);
v___x_1188_ = v___x_1184_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1186_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v_a_1179_);
v___x_1188_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
v_a_1178_ = v_tail_1182_;
v_a_1179_ = v___x_1188_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__0));
v___x_1194_ = l_Lean_stringToMessageData(v___x_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0(uint8_t v___y_1195_, lean_object* v_mvarId_1196_, lean_object* v___f_1197_, lean_object* v_declName_1198_, lean_object* v_val_1199_, lean_object* v___x_1200_, lean_object* v_fields_1201_, uint8_t v___x_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; 
if (v___y_1195_ == 0)
{
lean_object* v___x_1264_; 
lean_dec_ref(v_fields_1201_);
lean_dec_ref(v___x_1200_);
lean_dec_ref(v_val_1199_);
lean_dec(v_declName_1198_);
v___x_1264_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_1196_, v___f_1197_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
return v___x_1264_;
}
else
{
lean_object* v___x_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
lean_dec_ref(v___f_1197_);
v___x_1265_ = lean_array_get_size(v_fields_1201_);
v___x_1266_ = lean_unsigned_to_nat(1u);
v___x_1267_ = lean_nat_dec_eq(v___x_1265_, v___x_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1268_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1);
lean_inc_ref(v_fields_1201_);
v___x_1269_ = lean_array_to_list(v_fields_1201_);
v___x_1270_ = lean_box(0);
v___x_1271_ = l_List_mapTR_loop___at___00Lean_Meta_splitSparseCasesOn_spec__1(v___x_1269_, v___x_1270_);
v___x_1272_ = l_Lean_MessageData_ofList(v___x_1271_);
v___x_1273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1268_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
v___x_1274_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1273_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_dec_ref(v___x_1274_);
v___y_1209_ = v___y_1203_;
v___y_1210_ = v___y_1204_;
v___y_1211_ = v___y_1205_;
v___y_1212_ = v___y_1206_;
goto v___jp_1208_;
}
else
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec_ref(v_fields_1201_);
lean_dec_ref(v___x_1200_);
lean_dec_ref(v_val_1199_);
lean_dec(v_declName_1198_);
lean_dec(v_mvarId_1196_);
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1277_ = v___x_1274_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1274_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1275_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
else
{
v___y_1209_ = v___y_1203_;
v___y_1210_ = v___y_1204_;
v___y_1211_ = v___y_1205_;
v___y_1212_ = v___y_1206_;
goto v___jp_1208_;
}
}
v___jp_1208_:
{
lean_object* v___x_1213_; 
lean_inc(v___y_1212_);
lean_inc_ref(v___y_1211_);
lean_inc(v___y_1210_);
lean_inc_ref(v___y_1209_);
v___x_1213_ = l_Lean_Meta_getSparseCasesOnEq(v_declName_1198_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; lean_object* v___x_1215_; 
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_a_1214_);
lean_dec_ref(v___x_1213_);
lean_inc(v_mvarId_1196_);
v___x_1215_ = l_Lean_MVarId_getType(v_mvarId_1196_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v___x_1217_; 
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_a_1216_);
lean_dec_ref(v___x_1215_);
lean_inc(v___y_1212_);
lean_inc_ref(v___y_1211_);
lean_inc(v___y_1210_);
lean_inc_ref(v___y_1209_);
v___x_1217_ = l_Lean_Meta_matchEqHEqLHS_x3f(v_a_1216_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_a_1218_);
lean_dec_ref(v___x_1217_);
if (lean_obj_tag(v_a_1218_) == 1)
{
lean_object* v_val_1219_; lean_object* v_snd_1220_; lean_object* v_arity_1221_; lean_object* v___x_1222_; lean_object* v_nargs_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v_dummy_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v_val_1219_ = lean_ctor_get(v_a_1218_, 0);
lean_inc(v_val_1219_);
lean_dec_ref(v_a_1218_);
v_snd_1220_ = lean_ctor_get(v_val_1219_, 1);
lean_inc(v_snd_1220_);
lean_dec(v_val_1219_);
v_arity_1221_ = lean_ctor_get(v_val_1199_, 2);
lean_inc(v_arity_1221_);
lean_dec_ref(v_val_1199_);
v___x_1222_ = l_Lean_Expr_getAppFn(v_snd_1220_);
v_nargs_1223_ = l_Lean_Expr_getAppNumArgs(v_snd_1220_);
v___x_1224_ = l_Lean_Expr_constLevels_x21(v___x_1222_);
lean_dec_ref(v___x_1222_);
v___x_1225_ = l_Lean_mkConst(v_a_1214_, v___x_1224_);
v_dummy_1226_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__0);
lean_inc(v_nargs_1223_);
v___x_1227_ = lean_mk_array(v_nargs_1223_, v_dummy_1226_);
v___x_1228_ = lean_unsigned_to_nat(1u);
v___x_1229_ = lean_nat_sub(v_nargs_1223_, v___x_1228_);
lean_dec(v_nargs_1223_);
v___x_1230_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_snd_1220_, v___x_1227_, v___x_1229_);
v___x_1231_ = lean_unsigned_to_nat(0u);
v___x_1232_ = l_Array_toSubarray___redArg(v___x_1230_, v___x_1231_, v_arity_1221_);
v___x_1233_ = l_Subarray_copy___redArg(v___x_1232_);
v___x_1234_ = l_Lean_mkAppN(v___x_1225_, v___x_1233_);
lean_dec_ref(v___x_1233_);
v___x_1235_ = lean_array_get(v___x_1200_, v_fields_1201_, v___x_1231_);
lean_dec_ref(v_fields_1201_);
v___x_1236_ = l_Lean_Expr_app___override(v___x_1234_, v___x_1235_);
v___x_1237_ = l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq(v_mvarId_1196_, v___x_1236_, v___x_1202_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
return v___x_1237_;
}
else
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
lean_dec(v_a_1218_);
lean_dec(v_a_1214_);
lean_dec_ref(v_fields_1201_);
lean_dec_ref(v___x_1200_);
lean_dec_ref(v_val_1199_);
lean_dec(v_mvarId_1196_);
v___x_1238_ = lean_obj_once(&l_Lean_Meta_reduceSparseCasesOn___closed__1, &l_Lean_Meta_reduceSparseCasesOn___closed__1_once, _init_l_Lean_Meta_reduceSparseCasesOn___closed__1);
v___x_1239_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1238_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
return v___x_1239_;
}
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_dec(v_a_1214_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec_ref(v_fields_1201_);
lean_dec_ref(v___x_1200_);
lean_dec_ref(v_val_1199_);
lean_dec(v_mvarId_1196_);
v_a_1240_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1217_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1217_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
else
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
lean_dec(v_a_1214_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec_ref(v_fields_1201_);
lean_dec_ref(v___x_1200_);
lean_dec_ref(v_val_1199_);
lean_dec(v_mvarId_1196_);
v_a_1248_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1215_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1215_);
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
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec_ref(v_fields_1201_);
lean_dec_ref(v___x_1200_);
lean_dec_ref(v_val_1199_);
lean_dec(v_mvarId_1196_);
v_a_1256_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1213_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1213_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed(lean_object* v___y_1283_, lean_object* v_mvarId_1284_, lean_object* v___f_1285_, lean_object* v_declName_1286_, lean_object* v_val_1287_, lean_object* v___x_1288_, lean_object* v_fields_1289_, lean_object* v___x_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
uint8_t v___y_29199__boxed_1296_; uint8_t v___x_29204__boxed_1297_; lean_object* v_res_1298_; 
v___y_29199__boxed_1296_ = lean_unbox(v___y_1283_);
v___x_29204__boxed_1297_ = lean_unbox(v___x_1290_);
v_res_1298_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0(v___y_29199__boxed_1296_, v_mvarId_1284_, v___f_1285_, v_declName_1286_, v_val_1287_, v___x_1288_, v_fields_1289_, v___x_29204__boxed_1297_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(lean_object* v_declName_1299_, lean_object* v_val_1300_, uint8_t v___x_1301_, size_t v_sz_1302_, size_t v_i_1303_, lean_object* v_bs_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
uint8_t v___x_1310_; 
v___x_1310_ = lean_usize_dec_lt(v_i_1303_, v_sz_1302_);
if (v___x_1310_ == 0)
{
lean_object* v___x_1311_; 
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec_ref(v_val_1300_);
lean_dec(v_declName_1299_);
v___x_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1311_, 0, v_bs_1304_);
return v___x_1311_;
}
else
{
lean_object* v_v_1312_; lean_object* v_toInductionSubgoal_1313_; lean_object* v_ctorName_1314_; lean_object* v_mvarId_1315_; lean_object* v_fields_1316_; lean_object* v___f_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; lean_object* v___x_1320_; lean_object* v_bs_x27_1321_; uint8_t v___y_1323_; 
v_v_1312_ = lean_array_uget_borrowed(v_bs_1304_, v_i_1303_);
v_toInductionSubgoal_1313_ = lean_ctor_get(v_v_1312_, 0);
v_ctorName_1314_ = lean_ctor_get(v_v_1312_, 1);
lean_inc(v_ctorName_1314_);
v_mvarId_1315_ = lean_ctor_get(v_toInductionSubgoal_1313_, 0);
lean_inc(v_mvarId_1315_);
v_fields_1316_ = lean_ctor_get(v_toInductionSubgoal_1313_, 1);
lean_inc_ref(v_fields_1316_);
v___f_1317_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__0));
v___x_1318_ = l_Lean_instInhabitedExpr;
v___x_1319_ = 0;
v___x_1320_ = lean_unsigned_to_nat(0u);
v_bs_x27_1321_ = lean_array_uset(v_bs_1304_, v_i_1303_, v___x_1320_);
if (lean_obj_tag(v_ctorName_1314_) == 0)
{
if (v___x_1301_ == 0)
{
goto v___jp_1341_;
}
else
{
v___y_1323_ = v___x_1301_;
goto v___jp_1322_;
}
}
else
{
lean_dec_ref(v_ctorName_1314_);
goto v___jp_1341_;
}
v___jp_1322_:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___y_1326_; lean_object* v___x_1327_; 
v___x_1324_ = lean_box(v___y_1323_);
v___x_1325_ = lean_box(v___x_1319_);
lean_inc_ref(v_val_1300_);
lean_inc(v_declName_1299_);
lean_inc(v_mvarId_1315_);
v___y_1326_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed), 13, 8);
lean_closure_set(v___y_1326_, 0, v___x_1324_);
lean_closure_set(v___y_1326_, 1, v_mvarId_1315_);
lean_closure_set(v___y_1326_, 2, v___f_1317_);
lean_closure_set(v___y_1326_, 3, v_declName_1299_);
lean_closure_set(v___y_1326_, 4, v_val_1300_);
lean_closure_set(v___y_1326_, 5, v___x_1318_);
lean_closure_set(v___y_1326_, 6, v_fields_1316_);
lean_closure_set(v___y_1326_, 7, v___x_1325_);
lean_inc(v___y_1308_);
lean_inc_ref(v___y_1307_);
lean_inc(v___y_1306_);
lean_inc_ref(v___y_1305_);
v___x_1327_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1315_, v___y_1326_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; size_t v___x_1329_; size_t v___x_1330_; lean_object* v___x_1331_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_a_1328_);
lean_dec_ref(v___x_1327_);
v___x_1329_ = ((size_t)1ULL);
v___x_1330_ = lean_usize_add(v_i_1303_, v___x_1329_);
v___x_1331_ = lean_array_uset(v_bs_x27_1321_, v_i_1303_, v_a_1328_);
v_i_1303_ = v___x_1330_;
v_bs_1304_ = v___x_1331_;
goto _start;
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_dec_ref(v_bs_x27_1321_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec_ref(v_val_1300_);
lean_dec(v_declName_1299_);
v_a_1333_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1327_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1327_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
v___jp_1341_:
{
v___y_1323_ = v___x_1319_;
goto v___jp_1322_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4___boxed(lean_object* v_declName_1342_, lean_object* v_val_1343_, lean_object* v___x_1344_, lean_object* v_sz_1345_, lean_object* v_i_1346_, lean_object* v_bs_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
uint8_t v___x_29383__boxed_1353_; size_t v_sz_boxed_1354_; size_t v_i_boxed_1355_; lean_object* v_res_1356_; 
v___x_29383__boxed_1353_ = lean_unbox(v___x_1344_);
v_sz_boxed_1354_ = lean_unbox_usize(v_sz_1345_);
lean_dec(v_sz_1345_);
v_i_boxed_1355_ = lean_unbox_usize(v_i_1346_);
lean_dec(v_i_1346_);
v_res_1356_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(v_declName_1342_, v_val_1343_, v___x_29383__boxed_1353_, v_sz_boxed_1354_, v_i_boxed_1355_, v_bs_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
return v_res_1356_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__1));
v___x_1361_ = l_Lean_stringToMessageData(v___x_1360_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1(lean_object* v_val_1362_, lean_object* v___x_1363_, lean_object* v_x_1364_, lean_object* v_mvarId_1365_, lean_object* v_declName_1366_, uint8_t v___x_1367_, lean_object* v_____r_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v_majorPos_1399_; lean_object* v_arity_1400_; lean_object* v_insterestingCtors_1401_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___x_1421_; uint8_t v___x_1422_; 
v_majorPos_1399_ = lean_ctor_get(v_val_1362_, 1);
v_arity_1400_ = lean_ctor_get(v_val_1362_, 2);
v_insterestingCtors_1401_ = lean_ctor_get(v_val_1362_, 3);
v___x_1421_ = lean_array_get_size(v_x_1364_);
v___x_1422_ = lean_nat_dec_lt(v___x_1421_, v_arity_1400_);
if (v___x_1422_ == 0)
{
v___y_1403_ = v___y_1369_;
v___y_1404_ = v___y_1370_;
v___y_1405_ = v___y_1371_;
v___y_1406_ = v___y_1372_;
goto v___jp_1402_;
}
else
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_dec(v_declName_1366_);
lean_dec(v_mvarId_1365_);
lean_dec_ref(v___x_1363_);
lean_dec_ref(v_val_1362_);
v___x_1423_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__1);
v___x_1424_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1423_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1424_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1424_);
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
v___jp_1374_:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; uint8_t v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1381_ = lean_array_get_borrowed(v___x_1363_, v_x_1364_, v___y_1376_);
lean_dec(v___y_1376_);
v___x_1382_ = l_Lean_Expr_fvarId_x21(v___x_1381_);
v___x_1383_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__0));
v___x_1384_ = 0;
v___x_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1385_, 0, v___y_1375_);
lean_inc(v___y_1380_);
lean_inc_ref(v___y_1379_);
lean_inc(v___y_1378_);
lean_inc_ref(v___y_1377_);
v___x_1386_ = l_Lean_MVarId_cases(v_mvarId_1365_, v___x_1382_, v___x_1383_, v___x_1384_, v___x_1385_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; size_t v_sz_1388_; size_t v___x_1389_; lean_object* v___x_1390_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_a_1387_);
lean_dec_ref(v___x_1386_);
v_sz_1388_ = lean_array_size(v_a_1387_);
v___x_1389_ = ((size_t)0ULL);
v___x_1390_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(v_declName_1366_, v_val_1362_, v___x_1367_, v_sz_1388_, v___x_1389_, v_a_1387_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
return v___x_1390_;
}
else
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
lean_dec(v___y_1378_);
lean_dec_ref(v___y_1377_);
lean_dec(v_declName_1366_);
lean_dec_ref(v_val_1362_);
v_a_1391_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1393_ = v___x_1386_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1386_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1391_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
}
v___jp_1402_:
{
lean_object* v___x_1407_; uint8_t v___x_1408_; 
lean_inc_ref(v___x_1363_);
v___x_1407_ = lean_array_get_borrowed(v___x_1363_, v_x_1364_, v_majorPos_1399_);
v___x_1408_ = l_Lean_Expr_isFVar(v___x_1407_);
if (v___x_1408_ == 0)
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
lean_dec(v_declName_1366_);
lean_dec(v_mvarId_1365_);
lean_dec_ref(v___x_1363_);
lean_dec_ref(v_val_1362_);
v___x_1409_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2);
lean_inc(v___x_1407_);
v___x_1410_ = l_Lean_indentExpr(v___x_1407_);
v___x_1411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1409_);
lean_ctor_set(v___x_1411_, 1, v___x_1410_);
v___x_1412_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1411_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1412_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1412_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
else
{
lean_inc(v_majorPos_1399_);
lean_inc_ref(v_insterestingCtors_1401_);
v___y_1375_ = v_insterestingCtors_1401_;
v___y_1376_ = v_majorPos_1399_;
v___y_1377_ = v___y_1403_;
v___y_1378_ = v___y_1404_;
v___y_1379_ = v___y_1405_;
v___y_1380_ = v___y_1406_;
goto v___jp_1374_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___boxed(lean_object* v_val_1433_, lean_object* v___x_1434_, lean_object* v_x_1435_, lean_object* v_mvarId_1436_, lean_object* v_declName_1437_, lean_object* v___x_1438_, lean_object* v_____r_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
uint8_t v___x_29475__boxed_1445_; lean_object* v_res_1446_; 
v___x_29475__boxed_1445_ = lean_unbox(v___x_1438_);
v_res_1446_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1(v_val_1433_, v___x_1434_, v_x_1435_, v_mvarId_1436_, v_declName_1437_, v___x_29475__boxed_1445_, v_____r_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
lean_dec_ref(v_x_1435_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(lean_object* v_cls_1449_, lean_object* v_msg_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v_ref_1456_; lean_object* v___x_1457_; lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1502_; 
v_ref_1456_ = lean_ctor_get(v___y_1453_, 5);
v___x_1457_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msg_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1460_ = v___x_1457_;
v_isShared_1461_ = v_isSharedCheck_1502_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1457_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1502_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1462_; lean_object* v_traceState_1463_; lean_object* v_env_1464_; lean_object* v_nextMacroScope_1465_; lean_object* v_ngen_1466_; lean_object* v_auxDeclNGen_1467_; lean_object* v_cache_1468_; lean_object* v_messages_1469_; lean_object* v_infoState_1470_; lean_object* v_snapshotTasks_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1501_; 
v___x_1462_ = lean_st_ref_take(v___y_1454_);
v_traceState_1463_ = lean_ctor_get(v___x_1462_, 4);
v_env_1464_ = lean_ctor_get(v___x_1462_, 0);
v_nextMacroScope_1465_ = lean_ctor_get(v___x_1462_, 1);
v_ngen_1466_ = lean_ctor_get(v___x_1462_, 2);
v_auxDeclNGen_1467_ = lean_ctor_get(v___x_1462_, 3);
v_cache_1468_ = lean_ctor_get(v___x_1462_, 5);
v_messages_1469_ = lean_ctor_get(v___x_1462_, 6);
v_infoState_1470_ = lean_ctor_get(v___x_1462_, 7);
v_snapshotTasks_1471_ = lean_ctor_get(v___x_1462_, 8);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1473_ = v___x_1462_;
v_isShared_1474_ = v_isSharedCheck_1501_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_snapshotTasks_1471_);
lean_inc(v_infoState_1470_);
lean_inc(v_messages_1469_);
lean_inc(v_cache_1468_);
lean_inc(v_traceState_1463_);
lean_inc(v_auxDeclNGen_1467_);
lean_inc(v_ngen_1466_);
lean_inc(v_nextMacroScope_1465_);
lean_inc(v_env_1464_);
lean_dec(v___x_1462_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1501_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
uint64_t v_tid_1475_; lean_object* v_traces_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1500_; 
v_tid_1475_ = lean_ctor_get_uint64(v_traceState_1463_, sizeof(void*)*1);
v_traces_1476_ = lean_ctor_get(v_traceState_1463_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v_traceState_1463_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1478_ = v_traceState_1463_;
v_isShared_1479_ = v_isSharedCheck_1500_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_traces_1476_);
lean_dec(v_traceState_1463_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1500_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1480_; double v___x_1481_; uint8_t v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1490_; 
v___x_1480_ = lean_box(0);
v___x_1481_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__2);
v___x_1482_ = 0;
v___x_1483_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__6));
v___x_1484_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1484_, 0, v_cls_1449_);
lean_ctor_set(v___x_1484_, 1, v___x_1480_);
lean_ctor_set(v___x_1484_, 2, v___x_1483_);
lean_ctor_set_float(v___x_1484_, sizeof(void*)*3, v___x_1481_);
lean_ctor_set_float(v___x_1484_, sizeof(void*)*3 + 8, v___x_1481_);
lean_ctor_set_uint8(v___x_1484_, sizeof(void*)*3 + 16, v___x_1482_);
v___x_1485_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___closed__0));
v___x_1486_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1484_);
lean_ctor_set(v___x_1486_, 1, v_a_1458_);
lean_ctor_set(v___x_1486_, 2, v___x_1485_);
lean_inc(v_ref_1456_);
v___x_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1487_, 0, v_ref_1456_);
lean_ctor_set(v___x_1487_, 1, v___x_1486_);
v___x_1488_ = l_Lean_PersistentArray_push___redArg(v_traces_1476_, v___x_1487_);
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 0, v___x_1488_);
v___x_1490_ = v___x_1478_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1488_);
lean_ctor_set_uint64(v_reuseFailAlloc_1499_, sizeof(void*)*1, v_tid_1475_);
v___x_1490_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
lean_object* v___x_1492_; 
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 4, v___x_1490_);
v___x_1492_ = v___x_1473_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_env_1464_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_nextMacroScope_1465_);
lean_ctor_set(v_reuseFailAlloc_1498_, 2, v_ngen_1466_);
lean_ctor_set(v_reuseFailAlloc_1498_, 3, v_auxDeclNGen_1467_);
lean_ctor_set(v_reuseFailAlloc_1498_, 4, v___x_1490_);
lean_ctor_set(v_reuseFailAlloc_1498_, 5, v_cache_1468_);
lean_ctor_set(v_reuseFailAlloc_1498_, 6, v_messages_1469_);
lean_ctor_set(v_reuseFailAlloc_1498_, 7, v_infoState_1470_);
lean_ctor_set(v_reuseFailAlloc_1498_, 8, v_snapshotTasks_1471_);
v___x_1492_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1496_; 
v___x_1493_ = lean_st_ref_set(v___y_1454_, v___x_1492_);
v___x_1494_ = lean_box(0);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v___x_1494_);
v___x_1496_ = v___x_1460_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1494_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___boxed(lean_object* v_cls_1503_, lean_object* v_msg_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v_cls_1503_, v_msg_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(lean_object* v_declName_1511_, lean_object* v_val_1512_, uint8_t v___x_1513_, size_t v_sz_1514_, size_t v_i_1515_, lean_object* v_bs_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
uint8_t v___x_1522_; 
v___x_1522_ = lean_usize_dec_lt(v_i_1515_, v_sz_1514_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; 
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec_ref(v_val_1512_);
lean_dec(v_declName_1511_);
v___x_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1523_, 0, v_bs_1516_);
return v___x_1523_;
}
else
{
lean_object* v_v_1524_; lean_object* v_toInductionSubgoal_1525_; lean_object* v_ctorName_1526_; lean_object* v_mvarId_1527_; lean_object* v_fields_1528_; lean_object* v___f_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v_bs_x27_1532_; uint8_t v___y_1534_; 
v_v_1524_ = lean_array_uget_borrowed(v_bs_1516_, v_i_1515_);
v_toInductionSubgoal_1525_ = lean_ctor_get(v_v_1524_, 0);
v_ctorName_1526_ = lean_ctor_get(v_v_1524_, 1);
lean_inc(v_ctorName_1526_);
v_mvarId_1527_ = lean_ctor_get(v_toInductionSubgoal_1525_, 0);
lean_inc(v_mvarId_1527_);
v_fields_1528_ = lean_ctor_get(v_toInductionSubgoal_1525_, 1);
lean_inc_ref(v_fields_1528_);
v___f_1529_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__0));
v___x_1530_ = l_Lean_instInhabitedExpr;
v___x_1531_ = lean_unsigned_to_nat(0u);
v_bs_x27_1532_ = lean_array_uset(v_bs_1516_, v_i_1515_, v___x_1531_);
if (lean_obj_tag(v_ctorName_1526_) == 0)
{
v___y_1534_ = v___x_1522_;
goto v___jp_1533_;
}
else
{
lean_dec_ref(v_ctorName_1526_);
if (v___x_1513_ == 0)
{
v___y_1534_ = v___x_1513_;
goto v___jp_1533_;
}
else
{
v___y_1534_ = v___x_1522_;
goto v___jp_1533_;
}
}
v___jp_1533_:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___y_1537_; lean_object* v___x_1538_; 
v___x_1535_ = lean_box(v___y_1534_);
v___x_1536_ = lean_box(v___x_1513_);
lean_inc_ref(v_val_1512_);
lean_inc(v_declName_1511_);
lean_inc(v_mvarId_1527_);
v___y_1537_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed), 13, 8);
lean_closure_set(v___y_1537_, 0, v___x_1535_);
lean_closure_set(v___y_1537_, 1, v_mvarId_1527_);
lean_closure_set(v___y_1537_, 2, v___f_1529_);
lean_closure_set(v___y_1537_, 3, v_declName_1511_);
lean_closure_set(v___y_1537_, 4, v_val_1512_);
lean_closure_set(v___y_1537_, 5, v___x_1530_);
lean_closure_set(v___y_1537_, 6, v_fields_1528_);
lean_closure_set(v___y_1537_, 7, v___x_1536_);
lean_inc(v___y_1520_);
lean_inc_ref(v___y_1519_);
lean_inc(v___y_1518_);
lean_inc_ref(v___y_1517_);
v___x_1538_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1527_, v___y_1537_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; size_t v___x_1540_; size_t v___x_1541_; lean_object* v___x_1542_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_a_1539_);
lean_dec_ref(v___x_1538_);
v___x_1540_ = ((size_t)1ULL);
v___x_1541_ = lean_usize_add(v_i_1515_, v___x_1540_);
v___x_1542_ = lean_array_uset(v_bs_x27_1532_, v_i_1515_, v_a_1539_);
v_i_1515_ = v___x_1541_;
v_bs_1516_ = v___x_1542_;
goto _start;
}
else
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1551_; 
lean_dec_ref(v_bs_x27_1532_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec_ref(v_val_1512_);
lean_dec(v_declName_1511_);
v_a_1544_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1546_ = v___x_1538_;
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1538_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1549_; 
if (v_isShared_1547_ == 0)
{
v___x_1549_ = v___x_1546_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_a_1544_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___boxed(lean_object* v_declName_1552_, lean_object* v_val_1553_, lean_object* v___x_1554_, lean_object* v_sz_1555_, lean_object* v_i_1556_, lean_object* v_bs_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
uint8_t v___x_29719__boxed_1563_; size_t v_sz_boxed_1564_; size_t v_i_boxed_1565_; lean_object* v_res_1566_; 
v___x_29719__boxed_1563_ = lean_unbox(v___x_1554_);
v_sz_boxed_1564_ = lean_unbox_usize(v_sz_1555_);
lean_dec(v_sz_1555_);
v_i_boxed_1565_ = lean_unbox_usize(v_i_1556_);
lean_dec(v_i_1556_);
v_res_1566_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(v_declName_1552_, v_val_1553_, v___x_29719__boxed_1563_, v_sz_boxed_1564_, v_i_boxed_1565_, v_bs_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__2(lean_object* v_val_1567_, lean_object* v___x_1568_, lean_object* v_x_1569_, lean_object* v_mvarId_1570_, uint8_t v___x_1571_, lean_object* v_declName_1572_, lean_object* v_____r_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v_majorPos_1603_; lean_object* v_arity_1604_; lean_object* v_insterestingCtors_1605_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___x_1625_; uint8_t v___x_1626_; 
v_majorPos_1603_ = lean_ctor_get(v_val_1567_, 1);
v_arity_1604_ = lean_ctor_get(v_val_1567_, 2);
v_insterestingCtors_1605_ = lean_ctor_get(v_val_1567_, 3);
v___x_1625_ = lean_array_get_size(v_x_1569_);
v___x_1626_ = lean_nat_dec_lt(v___x_1625_, v_arity_1604_);
if (v___x_1626_ == 0)
{
v___y_1607_ = v___y_1574_;
v___y_1608_ = v___y_1575_;
v___y_1609_ = v___y_1576_;
v___y_1610_ = v___y_1577_;
goto v___jp_1606_;
}
else
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
lean_dec(v_declName_1572_);
lean_dec(v_mvarId_1570_);
lean_dec_ref(v___x_1568_);
lean_dec_ref(v_val_1567_);
v___x_1627_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__1);
v___x_1628_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1627_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1628_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1628_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1629_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
v___jp_1579_:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1586_ = lean_array_get_borrowed(v___x_1568_, v_x_1569_, v___y_1580_);
lean_dec(v___y_1580_);
v___x_1587_ = l_Lean_Expr_fvarId_x21(v___x_1586_);
v___x_1588_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__0));
v___x_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1589_, 0, v___y_1581_);
lean_inc(v___y_1585_);
lean_inc_ref(v___y_1584_);
lean_inc(v___y_1583_);
lean_inc_ref(v___y_1582_);
v___x_1590_ = l_Lean_MVarId_cases(v_mvarId_1570_, v___x_1587_, v___x_1588_, v___x_1571_, v___x_1589_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; size_t v_sz_1592_; size_t v___x_1593_; lean_object* v___x_1594_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1591_);
lean_dec_ref(v___x_1590_);
v_sz_1592_ = lean_array_size(v_a_1591_);
v___x_1593_ = ((size_t)0ULL);
v___x_1594_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(v_declName_1572_, v_val_1567_, v___x_1571_, v_sz_1592_, v___x_1593_, v_a_1591_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
return v___x_1594_;
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v_declName_1572_);
lean_dec_ref(v_val_1567_);
v_a_1595_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1590_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1590_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
v___jp_1606_:
{
lean_object* v___x_1611_; uint8_t v___x_1612_; 
lean_inc_ref(v___x_1568_);
v___x_1611_ = lean_array_get_borrowed(v___x_1568_, v_x_1569_, v_majorPos_1603_);
v___x_1612_ = l_Lean_Expr_isFVar(v___x_1611_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
lean_dec(v_declName_1572_);
lean_dec(v_mvarId_1570_);
lean_dec_ref(v___x_1568_);
lean_dec_ref(v_val_1567_);
v___x_1613_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2);
lean_inc(v___x_1611_);
v___x_1614_ = l_Lean_indentExpr(v___x_1611_);
v___x_1615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1613_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
v___x_1616_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1615_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1616_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1616_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
else
{
lean_inc_ref(v_insterestingCtors_1605_);
lean_inc(v_majorPos_1603_);
v___y_1580_ = v_majorPos_1603_;
v___y_1581_ = v_insterestingCtors_1605_;
v___y_1582_ = v___y_1607_;
v___y_1583_ = v___y_1608_;
v___y_1584_ = v___y_1609_;
v___y_1585_ = v___y_1610_;
goto v___jp_1579_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__2___boxed(lean_object* v_val_1637_, lean_object* v___x_1638_, lean_object* v_x_1639_, lean_object* v_mvarId_1640_, lean_object* v___x_1641_, lean_object* v_declName_1642_, lean_object* v_____r_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
uint8_t v___x_29800__boxed_1649_; lean_object* v_res_1650_; 
v___x_29800__boxed_1649_ = lean_unbox(v___x_1641_);
v_res_1650_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__2(v_val_1637_, v___x_1638_, v_x_1639_, v_mvarId_1640_, v___x_29800__boxed_1649_, v_declName_1642_, v_____r_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec_ref(v_x_1639_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__3(lean_object* v_val_1651_, lean_object* v___x_1652_, lean_object* v_x_1653_, lean_object* v_mvarId_1654_, uint8_t v___x_1655_, lean_object* v_declName_1656_, lean_object* v_____r_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v_majorPos_1687_; lean_object* v_arity_1688_; lean_object* v_insterestingCtors_1689_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___x_1709_; uint8_t v___x_1710_; 
v_majorPos_1687_ = lean_ctor_get(v_val_1651_, 1);
v_arity_1688_ = lean_ctor_get(v_val_1651_, 2);
v_insterestingCtors_1689_ = lean_ctor_get(v_val_1651_, 3);
v___x_1709_ = lean_array_get_size(v_x_1653_);
v___x_1710_ = lean_nat_dec_lt(v___x_1709_, v_arity_1688_);
if (v___x_1710_ == 0)
{
v___y_1691_ = v___y_1658_;
v___y_1692_ = v___y_1659_;
v___y_1693_ = v___y_1660_;
v___y_1694_ = v___y_1661_;
goto v___jp_1690_;
}
else
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
lean_dec(v_declName_1656_);
lean_dec(v_mvarId_1654_);
lean_dec_ref(v___x_1652_);
lean_dec_ref(v_val_1651_);
v___x_1711_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__1);
v___x_1712_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1711_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1712_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1712_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1713_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
v___jp_1663_:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1670_ = lean_array_get_borrowed(v___x_1652_, v_x_1653_, v___y_1665_);
lean_dec(v___y_1665_);
v___x_1671_ = l_Lean_Expr_fvarId_x21(v___x_1670_);
v___x_1672_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__0));
v___x_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1673_, 0, v___y_1664_);
lean_inc(v___y_1669_);
lean_inc_ref(v___y_1668_);
lean_inc(v___y_1667_);
lean_inc_ref(v___y_1666_);
v___x_1674_ = l_Lean_MVarId_cases(v_mvarId_1654_, v___x_1671_, v___x_1672_, v___x_1655_, v___x_1673_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v_a_1675_; size_t v_sz_1676_; size_t v___x_1677_; lean_object* v___x_1678_; 
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
lean_inc(v_a_1675_);
lean_dec_ref(v___x_1674_);
v_sz_1676_ = lean_array_size(v_a_1675_);
v___x_1677_ = ((size_t)0ULL);
v___x_1678_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(v_declName_1656_, v_val_1651_, v___x_1655_, v_sz_1676_, v___x_1677_, v_a_1675_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
return v___x_1678_;
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v_declName_1656_);
lean_dec_ref(v_val_1651_);
v_a_1679_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1674_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1674_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
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
}
v___jp_1690_:
{
lean_object* v___x_1695_; uint8_t v___x_1696_; 
lean_inc_ref(v___x_1652_);
v___x_1695_ = lean_array_get_borrowed(v___x_1652_, v_x_1653_, v_majorPos_1687_);
v___x_1696_ = l_Lean_Expr_isFVar(v___x_1695_);
if (v___x_1696_ == 0)
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1708_; 
lean_dec(v_declName_1656_);
lean_dec(v_mvarId_1654_);
lean_dec_ref(v___x_1652_);
lean_dec_ref(v_val_1651_);
v___x_1697_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2);
lean_inc(v___x_1695_);
v___x_1698_ = l_Lean_indentExpr(v___x_1695_);
v___x_1699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1697_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
v___x_1700_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1699_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1703_ = v___x_1700_;
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1700_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1706_; 
if (v_isShared_1704_ == 0)
{
v___x_1706_ = v___x_1703_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1701_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
else
{
lean_inc(v_majorPos_1687_);
lean_inc_ref(v_insterestingCtors_1689_);
v___y_1664_ = v_insterestingCtors_1689_;
v___y_1665_ = v_majorPos_1687_;
v___y_1666_ = v___y_1691_;
v___y_1667_ = v___y_1692_;
v___y_1668_ = v___y_1693_;
v___y_1669_ = v___y_1694_;
goto v___jp_1663_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__3___boxed(lean_object* v_val_1721_, lean_object* v___x_1722_, lean_object* v_x_1723_, lean_object* v_mvarId_1724_, lean_object* v___x_1725_, lean_object* v_declName_1726_, lean_object* v_____r_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
uint8_t v___x_29954__boxed_1733_; lean_object* v_res_1734_; 
v___x_29954__boxed_1733_ = lean_unbox(v___x_1725_);
v_res_1734_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__3(v_val_1721_, v___x_1722_, v_x_1723_, v_mvarId_1724_, v___x_29954__boxed_1733_, v_declName_1726_, v_____r_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
lean_dec_ref(v_x_1723_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__0(lean_object* v_val_1735_, lean_object* v___x_1736_, lean_object* v_x_1737_, lean_object* v_mvarId_1738_, uint8_t v_hasTrace_1739_, lean_object* v_declName_1740_, lean_object* v_____r_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v_majorPos_1771_; lean_object* v_arity_1772_; lean_object* v_insterestingCtors_1773_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___x_1793_; uint8_t v___x_1794_; 
v_majorPos_1771_ = lean_ctor_get(v_val_1735_, 1);
v_arity_1772_ = lean_ctor_get(v_val_1735_, 2);
v_insterestingCtors_1773_ = lean_ctor_get(v_val_1735_, 3);
v___x_1793_ = lean_array_get_size(v_x_1737_);
v___x_1794_ = lean_nat_dec_lt(v___x_1793_, v_arity_1772_);
if (v___x_1794_ == 0)
{
v___y_1775_ = v___y_1742_;
v___y_1776_ = v___y_1743_;
v___y_1777_ = v___y_1744_;
v___y_1778_ = v___y_1745_;
goto v___jp_1774_;
}
else
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
lean_dec(v_declName_1740_);
lean_dec(v_mvarId_1738_);
lean_dec_ref(v___x_1736_);
lean_dec_ref(v_val_1735_);
v___x_1795_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__1___closed__1);
v___x_1796_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1795_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___x_1796_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1796_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
v___jp_1747_:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1754_ = lean_array_get_borrowed(v___x_1736_, v_x_1737_, v___y_1748_);
lean_dec(v___y_1748_);
v___x_1755_ = l_Lean_Expr_fvarId_x21(v___x_1754_);
v___x_1756_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__0));
v___x_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1757_, 0, v___y_1749_);
lean_inc(v___y_1753_);
lean_inc_ref(v___y_1752_);
lean_inc(v___y_1751_);
lean_inc_ref(v___y_1750_);
v___x_1758_ = l_Lean_MVarId_cases(v_mvarId_1738_, v___x_1755_, v___x_1756_, v_hasTrace_1739_, v___x_1757_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; size_t v_sz_1760_; size_t v___x_1761_; lean_object* v___x_1762_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1759_);
lean_dec_ref(v___x_1758_);
v_sz_1760_ = lean_array_size(v_a_1759_);
v___x_1761_ = ((size_t)0ULL);
v___x_1762_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(v_declName_1740_, v_val_1735_, v_hasTrace_1739_, v_sz_1760_, v___x_1761_, v_a_1759_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
return v___x_1762_;
}
else
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v_declName_1740_);
lean_dec_ref(v_val_1735_);
v_a_1763_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1758_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1758_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1763_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
v___jp_1774_:
{
lean_object* v___x_1779_; uint8_t v___x_1780_; 
lean_inc_ref(v___x_1736_);
v___x_1779_ = lean_array_get_borrowed(v___x_1736_, v_x_1737_, v_majorPos_1771_);
v___x_1780_ = l_Lean_Expr_isFVar(v___x_1779_);
if (v___x_1780_ == 0)
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
lean_dec(v_declName_1740_);
lean_dec(v_mvarId_1738_);
lean_dec_ref(v___x_1736_);
lean_dec_ref(v_val_1735_);
v___x_1781_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2);
lean_inc(v___x_1779_);
v___x_1782_ = l_Lean_indentExpr(v___x_1779_);
v___x_1783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1781_);
lean_ctor_set(v___x_1783_, 1, v___x_1782_);
v___x_1784_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1783_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___x_1784_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1784_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1785_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
else
{
lean_inc_ref(v_insterestingCtors_1773_);
lean_inc(v_majorPos_1771_);
v___y_1748_ = v_majorPos_1771_;
v___y_1749_ = v_insterestingCtors_1773_;
v___y_1750_ = v___y_1775_;
v___y_1751_ = v___y_1776_;
v___y_1752_ = v___y_1777_;
v___y_1753_ = v___y_1778_;
goto v___jp_1747_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__0___boxed(lean_object* v_val_1805_, lean_object* v___x_1806_, lean_object* v_x_1807_, lean_object* v_mvarId_1808_, lean_object* v_hasTrace_1809_, lean_object* v_declName_1810_, lean_object* v_____r_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
uint8_t v_hasTrace_boxed_1817_; lean_object* v_res_1818_; 
v_hasTrace_boxed_1817_ = lean_unbox(v_hasTrace_1809_);
v_res_1818_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__0(v_val_1805_, v___x_1806_, v_x_1807_, v_mvarId_1808_, v_hasTrace_boxed_1817_, v_declName_1810_, v_____r_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
lean_dec_ref(v_x_1807_);
return v_res_1818_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1(void){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__0));
v___x_1821_ = l_Lean_stringToMessageData(v___x_1820_);
return v___x_1821_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1823_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__2));
v___x_1824_ = l_Lean_stringToMessageData(v___x_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5(lean_object* v_mvarId_1825_, lean_object* v_x_1826_, lean_object* v_x_1827_, lean_object* v_x_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
if (lean_obj_tag(v_x_1826_) == 5)
{
lean_object* v_fn_1834_; lean_object* v_arg_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v_fn_1834_ = lean_ctor_get(v_x_1826_, 0);
lean_inc_ref(v_fn_1834_);
v_arg_1835_ = lean_ctor_get(v_x_1826_, 1);
lean_inc_ref(v_arg_1835_);
lean_dec_ref(v_x_1826_);
v___x_1836_ = lean_array_set(v_x_1827_, v_x_1828_, v_arg_1835_);
v___x_1837_ = lean_unsigned_to_nat(1u);
v___x_1838_ = lean_nat_sub(v_x_1828_, v___x_1837_);
lean_dec(v_x_1828_);
v_x_1826_ = v_fn_1834_;
v_x_1827_ = v___x_1836_;
v_x_1828_ = v___x_1838_;
goto _start;
}
else
{
lean_dec(v_x_1828_);
if (lean_obj_tag(v_x_1826_) == 4)
{
lean_object* v_declName_1840_; lean_object* v___x_1841_; 
v_declName_1840_ = lean_ctor_get(v_x_1826_, 0);
lean_inc(v_declName_1840_);
lean_dec_ref(v_x_1826_);
lean_inc(v_declName_1840_);
v___x_1841_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_declName_1840_, v___y_1832_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_a_1842_);
lean_dec_ref(v___x_1841_);
if (lean_obj_tag(v_a_1842_) == 1)
{
lean_object* v_options_1843_; lean_object* v_val_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_2150_; 
v_options_1843_ = lean_ctor_get(v___y_1831_, 2);
v_val_1844_ = lean_ctor_get(v_a_1842_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v_a_1842_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_1846_ = v_a_1842_;
v_isShared_1847_ = v_isSharedCheck_2150_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_val_1844_);
lean_dec(v_a_1842_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_2150_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
uint8_t v_hasTrace_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___y_1852_; lean_object* v___y_1853_; uint8_t v___y_1854_; lean_object* v___y_1887_; lean_object* v_a_1888_; lean_object* v___y_1892_; lean_object* v___y_1895_; lean_object* v___y_1896_; uint8_t v___y_1897_; lean_object* v___y_1930_; lean_object* v_a_1931_; lean_object* v___y_1935_; 
v_hasTrace_1848_ = lean_ctor_get_uint8(v_options_1843_, sizeof(void*)*1);
v___x_1849_ = l_Lean_instInhabitedExpr;
v___x_1850_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__4));
if (v_hasTrace_1848_ == 0)
{
lean_object* v___x_1937_; lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1961_; 
lean_del_object(v___x_1846_);
v___x_1937_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___x_1850_, v___y_1831_);
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1940_ = v___x_1937_;
v_isShared_1941_ = v_isSharedCheck_1961_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1937_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1961_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
uint8_t v___x_1942_; 
v___x_1942_ = lean_unbox(v_a_1938_);
lean_dec(v_a_1938_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1943_; lean_object* v___x_1944_; 
lean_del_object(v___x_1940_);
v___x_1943_ = lean_box(0);
lean_inc(v___y_1832_);
lean_inc_ref(v___y_1831_);
lean_inc(v___y_1830_);
lean_inc_ref(v___y_1829_);
v___x_1944_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__0(v_val_1844_, v___x_1849_, v_x_1827_, v_mvarId_1825_, v_hasTrace_1848_, v_declName_1840_, v___x_1943_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec_ref(v_x_1827_);
v___y_1935_ = v___x_1944_;
goto v___jp_1934_;
}
else
{
lean_object* v___x_1945_; lean_object* v___x_1947_; 
v___x_1945_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3);
lean_inc(v_mvarId_1825_);
if (v_isShared_1941_ == 0)
{
lean_ctor_set_tag(v___x_1940_, 1);
lean_ctor_set(v___x_1940_, 0, v_mvarId_1825_);
v___x_1947_ = v___x_1940_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_mvarId_1825_);
v___x_1947_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1945_);
lean_ctor_set(v___x_1948_, 1, v___x_1947_);
v___x_1949_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1850_, v___x_1948_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v_a_1950_; lean_object* v___x_1951_; 
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_a_1950_);
lean_dec_ref(v___x_1949_);
lean_inc(v___y_1832_);
lean_inc_ref(v___y_1831_);
lean_inc(v___y_1830_);
lean_inc_ref(v___y_1829_);
v___x_1951_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__0(v_val_1844_, v___x_1849_, v_x_1827_, v_mvarId_1825_, v_hasTrace_1848_, v_declName_1840_, v_a_1950_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec_ref(v_x_1827_);
v___y_1935_ = v___x_1951_;
goto v___jp_1934_;
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec(v_val_1844_);
lean_dec(v_declName_1840_);
lean_dec_ref(v_x_1827_);
lean_dec(v_mvarId_1825_);
v_a_1952_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1949_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1949_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
lean_inc(v_a_1952_);
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
v___y_1930_ = v___x_1957_;
v_a_1931_ = v_a_1952_;
goto v___jp_1929_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1962_; lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_2149_; 
v___x_1962_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___x_1850_, v___y_1831_);
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_1965_ = v___x_1962_;
v_isShared_1966_ = v_isSharedCheck_2149_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1962_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_2149_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___f_1967_; lean_object* v___x_1968_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v_a_1972_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v_a_1988_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; uint8_t v___y_1996_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v_a_2009_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2026_; lean_object* v___y_2027_; lean_object* v_a_2028_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v_a_2041_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; uint8_t v___y_2049_; lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v_a_2062_; lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v___y_2068_; uint8_t v___x_2121_; 
v___f_1967_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__5));
v___x_1968_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__6));
v___x_2121_ = lean_unbox(v_a_1963_);
if (v___x_2121_ == 0)
{
lean_object* v___x_2122_; uint8_t v___x_2123_; 
v___x_2122_ = l_Lean_trace_profiler;
v___x_2123_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v_options_1843_, v___x_2122_);
if (v___x_2123_ == 0)
{
lean_object* v___x_2124_; lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2148_; 
lean_del_object(v___x_1965_);
lean_dec(v_a_1963_);
lean_del_object(v___x_1846_);
v___x_2124_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___x_1850_, v___y_1831_);
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2127_ = v___x_2124_;
v_isShared_2128_ = v_isSharedCheck_2148_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2124_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2148_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
uint8_t v___x_2129_; 
v___x_2129_ = lean_unbox(v_a_2125_);
lean_dec(v_a_2125_);
if (v___x_2129_ == 0)
{
lean_object* v___x_2130_; lean_object* v___x_2131_; 
lean_del_object(v___x_2127_);
v___x_2130_ = lean_box(0);
lean_inc(v___y_1832_);
lean_inc_ref(v___y_1831_);
lean_inc(v___y_1830_);
lean_inc_ref(v___y_1829_);
v___x_2131_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__3(v_val_1844_, v___x_1849_, v_x_1827_, v_mvarId_1825_, v___x_2123_, v_declName_1840_, v___x_2130_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec_ref(v_x_1827_);
v___y_1892_ = v___x_2131_;
goto v___jp_1891_;
}
else
{
lean_object* v___x_2132_; lean_object* v___x_2134_; 
v___x_2132_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3);
lean_inc(v_mvarId_1825_);
if (v_isShared_2128_ == 0)
{
lean_ctor_set_tag(v___x_2127_, 1);
lean_ctor_set(v___x_2127_, 0, v_mvarId_1825_);
v___x_2134_ = v___x_2127_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_mvarId_1825_);
v___x_2134_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2132_);
lean_ctor_set(v___x_2135_, 1, v___x_2134_);
v___x_2136_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1850_, v___x_2135_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v___x_2138_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
lean_dec_ref(v___x_2136_);
lean_inc(v___y_1832_);
lean_inc_ref(v___y_1831_);
lean_inc(v___y_1830_);
lean_inc_ref(v___y_1829_);
v___x_2138_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__3(v_val_1844_, v___x_1849_, v_x_1827_, v_mvarId_1825_, v___x_2123_, v_declName_1840_, v_a_2137_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec_ref(v_x_1827_);
v___y_1892_ = v___x_2138_;
goto v___jp_1891_;
}
else
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2146_; 
lean_dec(v_val_1844_);
lean_dec(v_declName_1840_);
lean_dec_ref(v_x_1827_);
lean_dec(v_mvarId_1825_);
v_a_2139_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2141_ = v___x_2136_;
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___x_2136_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2144_; 
lean_inc(v_a_2139_);
if (v_isShared_2142_ == 0)
{
v___x_2144_ = v___x_2141_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2139_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
v___y_1887_ = v___x_2144_;
v_a_1888_ = v_a_2139_;
goto v___jp_1886_;
}
}
}
}
}
}
}
else
{
lean_inc_ref(v_options_1843_);
goto v___jp_2078_;
}
}
else
{
lean_inc_ref(v_options_1843_);
goto v___jp_2078_;
}
v___jp_1969_:
{
lean_object* v___x_1973_; double v___x_1974_; double v___x_1975_; double v___x_1976_; double v___x_1977_; double v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; uint8_t v___x_1983_; lean_object* v___x_1984_; 
v___x_1973_ = lean_io_mono_nanos_now();
v___x_1974_ = lean_float_of_nat(v___y_1971_);
v___x_1975_ = lean_float_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__7);
v___x_1976_ = lean_float_div(v___x_1974_, v___x_1975_);
v___x_1977_ = lean_float_of_nat(v___x_1973_);
v___x_1978_ = lean_float_div(v___x_1977_, v___x_1975_);
v___x_1979_ = lean_box_float(v___x_1976_);
v___x_1980_ = lean_box_float(v___x_1978_);
v___x_1981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1979_);
lean_ctor_set(v___x_1981_, 1, v___x_1980_);
v___x_1982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1982_, 0, v_a_1972_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
v___x_1983_ = lean_unbox(v_a_1963_);
lean_dec(v_a_1963_);
v___x_1984_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7(v___x_1850_, v_hasTrace_1848_, v___x_1968_, v_options_1843_, v___x_1983_, v___y_1970_, v___f_1967_, v___x_1982_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec_ref(v_options_1843_);
return v___x_1984_;
}
v___jp_1985_:
{
lean_object* v___x_1990_; 
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 0, v_a_1988_);
v___x_1990_ = v___x_1965_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_a_1988_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
v___y_1970_ = v___y_1986_;
v___y_1971_ = v___y_1987_;
v_a_1972_ = v___x_1990_;
goto v___jp_1969_;
}
}
v___jp_1992_:
{
if (v___y_1996_ == 0)
{
lean_object* v___x_1997_; lean_object* v_a_1998_; uint8_t v___x_1999_; 
v___x_1997_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___x_1850_, v___y_1831_);
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_a_1998_);
lean_dec_ref(v___x_1997_);
v___x_1999_ = lean_unbox(v_a_1998_);
lean_dec(v_a_1998_);
if (v___x_1999_ == 0)
{
v___y_1986_ = v___y_1993_;
v___y_1987_ = v___y_1994_;
v_a_1988_ = v___y_1995_;
goto v___jp_1985_;
}
else
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2000_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1);
lean_inc_ref(v___y_1995_);
v___x_2001_ = l_Lean_Exception_toMessageData(v___y_1995_);
v___x_2002_ = l_Lean_indentD(v___x_2001_);
v___x_2003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2000_);
lean_ctor_set(v___x_2003_, 1, v___x_2002_);
v___x_2004_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1850_, v___x_2003_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_dec_ref(v___x_2004_);
v___y_1986_ = v___y_1993_;
v___y_1987_ = v___y_1994_;
v_a_1988_ = v___y_1995_;
goto v___jp_1985_;
}
else
{
lean_object* v_a_2005_; 
lean_dec_ref(v___y_1995_);
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_a_2005_);
lean_dec_ref(v___x_2004_);
v___y_1986_ = v___y_1993_;
v___y_1987_ = v___y_1994_;
v_a_1988_ = v_a_2005_;
goto v___jp_1985_;
}
}
}
else
{
v___y_1986_ = v___y_1993_;
v___y_1987_ = v___y_1994_;
v_a_1988_ = v___y_1995_;
goto v___jp_1985_;
}
}
v___jp_2006_:
{
uint8_t v___x_2010_; 
v___x_2010_ = l_Lean_Exception_isInterrupt(v_a_2009_);
if (v___x_2010_ == 0)
{
uint8_t v___x_2011_; 
lean_inc_ref(v_a_2009_);
v___x_2011_ = l_Lean_Exception_isRuntime(v_a_2009_);
v___y_1993_ = v___y_2007_;
v___y_1994_ = v___y_2008_;
v___y_1995_ = v_a_2009_;
v___y_1996_ = v___x_2011_;
goto v___jp_1992_;
}
else
{
v___y_1993_ = v___y_2007_;
v___y_1994_ = v___y_2008_;
v___y_1995_ = v_a_2009_;
v___y_1996_ = v___x_2010_;
goto v___jp_1992_;
}
}
v___jp_2012_:
{
if (lean_obj_tag(v___y_2015_) == 0)
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
lean_del_object(v___x_1965_);
v_a_2016_ = lean_ctor_get(v___y_2015_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___y_2015_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___y_2015_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___y_2015_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
lean_ctor_set_tag(v___x_2018_, 1);
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
v___y_1970_ = v___y_2013_;
v___y_1971_ = v___y_2014_;
v_a_1972_ = v___x_2021_;
goto v___jp_1969_;
}
}
}
else
{
lean_object* v_a_2024_; 
v_a_2024_ = lean_ctor_get(v___y_2015_, 0);
lean_inc(v_a_2024_);
lean_dec_ref(v___y_2015_);
v___y_2007_ = v___y_2013_;
v___y_2008_ = v___y_2014_;
v_a_2009_ = v_a_2024_;
goto v___jp_2006_;
}
}
v___jp_2025_:
{
lean_object* v___x_2029_; double v___x_2030_; double v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; uint8_t v___x_2036_; lean_object* v___x_2037_; 
v___x_2029_ = lean_io_get_num_heartbeats();
v___x_2030_ = lean_float_of_nat(v___y_2027_);
v___x_2031_ = lean_float_of_nat(v___x_2029_);
v___x_2032_ = lean_box_float(v___x_2030_);
v___x_2033_ = lean_box_float(v___x_2031_);
v___x_2034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2032_);
lean_ctor_set(v___x_2034_, 1, v___x_2033_);
v___x_2035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2035_, 0, v_a_2028_);
lean_ctor_set(v___x_2035_, 1, v___x_2034_);
v___x_2036_ = lean_unbox(v_a_1963_);
lean_dec(v_a_1963_);
v___x_2037_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__7(v___x_1850_, v_hasTrace_1848_, v___x_1968_, v_options_1843_, v___x_2036_, v___y_2026_, v___f_1967_, v___x_2035_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec_ref(v_options_1843_);
return v___x_2037_;
}
v___jp_2038_:
{
lean_object* v___x_2043_; 
if (v_isShared_1847_ == 0)
{
lean_ctor_set_tag(v___x_1846_, 0);
lean_ctor_set(v___x_1846_, 0, v_a_2041_);
v___x_2043_ = v___x_1846_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2041_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
v___y_2026_ = v___y_2039_;
v___y_2027_ = v___y_2040_;
v_a_2028_ = v___x_2043_;
goto v___jp_2025_;
}
}
v___jp_2045_:
{
if (v___y_2049_ == 0)
{
lean_object* v___x_2050_; lean_object* v_a_2051_; uint8_t v___x_2052_; 
v___x_2050_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___x_1850_, v___y_1831_);
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2051_);
lean_dec_ref(v___x_2050_);
v___x_2052_ = lean_unbox(v_a_2051_);
lean_dec(v_a_2051_);
if (v___x_2052_ == 0)
{
v___y_2039_ = v___y_2047_;
v___y_2040_ = v___y_2048_;
v_a_2041_ = v___y_2046_;
goto v___jp_2038_;
}
else
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2053_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1);
lean_inc_ref(v___y_2046_);
v___x_2054_ = l_Lean_Exception_toMessageData(v___y_2046_);
v___x_2055_ = l_Lean_indentD(v___x_2054_);
v___x_2056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2053_);
lean_ctor_set(v___x_2056_, 1, v___x_2055_);
v___x_2057_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1850_, v___x_2056_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_dec_ref(v___x_2057_);
v___y_2039_ = v___y_2047_;
v___y_2040_ = v___y_2048_;
v_a_2041_ = v___y_2046_;
goto v___jp_2038_;
}
else
{
lean_object* v_a_2058_; 
lean_dec_ref(v___y_2046_);
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
lean_inc(v_a_2058_);
lean_dec_ref(v___x_2057_);
v___y_2039_ = v___y_2047_;
v___y_2040_ = v___y_2048_;
v_a_2041_ = v_a_2058_;
goto v___jp_2038_;
}
}
}
else
{
v___y_2039_ = v___y_2047_;
v___y_2040_ = v___y_2048_;
v_a_2041_ = v___y_2046_;
goto v___jp_2038_;
}
}
v___jp_2059_:
{
uint8_t v___x_2063_; 
v___x_2063_ = l_Lean_Exception_isInterrupt(v_a_2062_);
if (v___x_2063_ == 0)
{
uint8_t v___x_2064_; 
lean_inc_ref(v_a_2062_);
v___x_2064_ = l_Lean_Exception_isRuntime(v_a_2062_);
v___y_2046_ = v_a_2062_;
v___y_2047_ = v___y_2060_;
v___y_2048_ = v___y_2061_;
v___y_2049_ = v___x_2064_;
goto v___jp_2045_;
}
else
{
v___y_2046_ = v_a_2062_;
v___y_2047_ = v___y_2060_;
v___y_2048_ = v___y_2061_;
v___y_2049_ = v___x_2063_;
goto v___jp_2045_;
}
}
v___jp_2065_:
{
if (lean_obj_tag(v___y_2068_) == 0)
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
lean_del_object(v___x_1846_);
v_a_2069_ = lean_ctor_get(v___y_2068_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___y_2068_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___y_2068_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___y_2068_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
lean_ctor_set_tag(v___x_2071_, 1);
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
v___y_2026_ = v___y_2066_;
v___y_2027_ = v___y_2067_;
v_a_2028_ = v___x_2074_;
goto v___jp_2025_;
}
}
}
else
{
lean_object* v_a_2077_; 
v_a_2077_ = lean_ctor_get(v___y_2068_, 0);
lean_inc(v_a_2077_);
lean_dec_ref(v___y_2068_);
v___y_2060_ = v___y_2066_;
v___y_2061_ = v___y_2067_;
v_a_2062_ = v_a_2077_;
goto v___jp_2059_;
}
}
v___jp_2078_:
{
lean_object* v___x_2079_; lean_object* v_a_2080_; lean_object* v___x_2081_; uint8_t v___x_2082_; 
v___x_2079_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__5___redArg(v___y_1832_);
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
lean_inc(v_a_2080_);
lean_dec_ref(v___x_2079_);
v___x_2081_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2082_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v_options_1843_, v___x_2081_);
if (v___x_2082_ == 0)
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2101_; 
lean_del_object(v___x_1846_);
v___x_2083_ = lean_io_mono_nanos_now();
v___x_2084_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___x_1850_, v___y_1831_);
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2087_ = v___x_2084_;
v_isShared_2088_ = v_isSharedCheck_2101_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2084_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2101_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
uint8_t v___x_2089_; 
v___x_2089_ = lean_unbox(v_a_2085_);
lean_dec(v_a_2085_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; lean_object* v___x_2091_; 
lean_del_object(v___x_2087_);
v___x_2090_ = lean_box(0);
lean_inc(v___y_1832_);
lean_inc_ref(v___y_1831_);
lean_inc(v___y_1830_);
lean_inc_ref(v___y_1829_);
v___x_2091_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__2(v_val_1844_, v___x_1849_, v_x_1827_, v_mvarId_1825_, v___x_2082_, v_declName_1840_, v___x_2090_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec_ref(v_x_1827_);
v___y_2013_ = v_a_2080_;
v___y_2014_ = v___x_2083_;
v___y_2015_ = v___x_2091_;
goto v___jp_2012_;
}
else
{
lean_object* v___x_2092_; lean_object* v___x_2094_; 
v___x_2092_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3);
lean_inc(v_mvarId_1825_);
if (v_isShared_2088_ == 0)
{
lean_ctor_set_tag(v___x_2087_, 1);
lean_ctor_set(v___x_2087_, 0, v_mvarId_1825_);
v___x_2094_ = v___x_2087_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_mvarId_1825_);
v___x_2094_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2092_);
lean_ctor_set(v___x_2095_, 1, v___x_2094_);
v___x_2096_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1850_, v___x_2095_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; lean_object* v___x_2098_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2097_);
lean_dec_ref(v___x_2096_);
lean_inc(v___y_1832_);
lean_inc_ref(v___y_1831_);
lean_inc(v___y_1830_);
lean_inc_ref(v___y_1829_);
v___x_2098_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__2(v_val_1844_, v___x_1849_, v_x_1827_, v_mvarId_1825_, v___x_2082_, v_declName_1840_, v_a_2097_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec_ref(v_x_1827_);
v___y_2013_ = v_a_2080_;
v___y_2014_ = v___x_2083_;
v___y_2015_ = v___x_2098_;
goto v___jp_2012_;
}
else
{
lean_object* v_a_2099_; 
lean_dec(v_val_1844_);
lean_dec(v_declName_1840_);
lean_dec_ref(v_x_1827_);
lean_dec(v_mvarId_1825_);
v_a_2099_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2099_);
lean_dec_ref(v___x_2096_);
v___y_2007_ = v_a_2080_;
v___y_2008_ = v___x_2083_;
v_a_2009_ = v_a_2099_;
goto v___jp_2006_;
}
}
}
}
}
else
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2120_; 
lean_del_object(v___x_1965_);
v___x_2102_ = lean_io_get_num_heartbeats();
v___x_2103_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___x_1850_, v___y_1831_);
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2106_ = v___x_2103_;
v_isShared_2107_ = v_isSharedCheck_2120_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2103_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2120_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
uint8_t v___x_2108_; 
v___x_2108_ = lean_unbox(v_a_2104_);
lean_dec(v_a_2104_);
if (v___x_2108_ == 0)
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
lean_del_object(v___x_2106_);
v___x_2109_ = lean_box(0);
lean_inc(v___y_1832_);
lean_inc_ref(v___y_1831_);
lean_inc(v___y_1830_);
lean_inc_ref(v___y_1829_);
v___x_2110_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1(v_val_1844_, v___x_1849_, v_x_1827_, v_mvarId_1825_, v_declName_1840_, v___x_2082_, v___x_2109_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec_ref(v_x_1827_);
v___y_2066_ = v_a_2080_;
v___y_2067_ = v___x_2102_;
v___y_2068_ = v___x_2110_;
goto v___jp_2065_;
}
else
{
lean_object* v___x_2111_; lean_object* v___x_2113_; 
v___x_2111_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3);
lean_inc(v_mvarId_1825_);
if (v_isShared_2107_ == 0)
{
lean_ctor_set_tag(v___x_2106_, 1);
lean_ctor_set(v___x_2106_, 0, v_mvarId_1825_);
v___x_2113_ = v___x_2106_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_mvarId_1825_);
v___x_2113_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2111_);
lean_ctor_set(v___x_2114_, 1, v___x_2113_);
v___x_2115_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1850_, v___x_2114_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; lean_object* v___x_2117_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_a_2116_);
lean_dec_ref(v___x_2115_);
lean_inc(v___y_1832_);
lean_inc_ref(v___y_1831_);
lean_inc(v___y_1830_);
lean_inc_ref(v___y_1829_);
v___x_2117_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1(v_val_1844_, v___x_1849_, v_x_1827_, v_mvarId_1825_, v_declName_1840_, v___x_2082_, v_a_2116_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec_ref(v_x_1827_);
v___y_2066_ = v_a_2080_;
v___y_2067_ = v___x_2102_;
v___y_2068_ = v___x_2117_;
goto v___jp_2065_;
}
else
{
lean_object* v_a_2118_; 
lean_dec(v_val_1844_);
lean_dec(v_declName_1840_);
lean_dec_ref(v_x_1827_);
lean_dec(v_mvarId_1825_);
v_a_2118_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_a_2118_);
lean_dec_ref(v___x_2115_);
v___y_2060_ = v_a_2080_;
v___y_2061_ = v___x_2102_;
v_a_2062_ = v_a_2118_;
goto v___jp_2059_;
}
}
}
}
}
}
}
}
v___jp_1851_:
{
if (v___y_1854_ == 0)
{
lean_object* v___x_1855_; lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1885_; 
lean_dec_ref(v___y_1853_);
v___x_1855_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___x_1850_, v___y_1831_);
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1858_ = v___x_1855_;
v_isShared_1859_ = v_isSharedCheck_1885_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1855_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1885_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
uint8_t v___x_1860_; 
v___x_1860_ = lean_unbox(v_a_1856_);
lean_dec(v_a_1856_);
if (v___x_1860_ == 0)
{
lean_object* v___x_1862_; 
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
if (v_isShared_1859_ == 0)
{
lean_ctor_set_tag(v___x_1858_, 1);
lean_ctor_set(v___x_1858_, 0, v___y_1852_);
v___x_1862_ = v___x_1858_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v___y_1852_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
else
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
lean_del_object(v___x_1858_);
v___x_1864_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1);
lean_inc_ref(v___y_1852_);
v___x_1865_ = l_Lean_Exception_toMessageData(v___y_1852_);
v___x_1866_ = l_Lean_indentD(v___x_1865_);
v___x_1867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1864_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
v___x_1868_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1850_, v___x_1867_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1875_ == 0)
{
lean_object* v_unused_1876_; 
v_unused_1876_ = lean_ctor_get(v___x_1868_, 0);
lean_dec(v_unused_1876_);
v___x_1870_ = v___x_1868_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_dec(v___x_1868_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
lean_ctor_set_tag(v___x_1870_, 1);
lean_ctor_set(v___x_1870_, 0, v___y_1852_);
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v___y_1852_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
lean_dec_ref(v___y_1852_);
v_a_1877_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1868_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1868_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_1852_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
return v___y_1853_;
}
}
v___jp_1886_:
{
uint8_t v___x_1889_; 
v___x_1889_ = l_Lean_Exception_isInterrupt(v_a_1888_);
if (v___x_1889_ == 0)
{
uint8_t v___x_1890_; 
lean_inc_ref(v_a_1888_);
v___x_1890_ = l_Lean_Exception_isRuntime(v_a_1888_);
v___y_1852_ = v_a_1888_;
v___y_1853_ = v___y_1887_;
v___y_1854_ = v___x_1890_;
goto v___jp_1851_;
}
else
{
v___y_1852_ = v_a_1888_;
v___y_1853_ = v___y_1887_;
v___y_1854_ = v___x_1889_;
goto v___jp_1851_;
}
}
v___jp_1891_:
{
if (lean_obj_tag(v___y_1892_) == 0)
{
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
return v___y_1892_;
}
else
{
lean_object* v_a_1893_; 
v_a_1893_ = lean_ctor_get(v___y_1892_, 0);
lean_inc(v_a_1893_);
v___y_1887_ = v___y_1892_;
v_a_1888_ = v_a_1893_;
goto v___jp_1886_;
}
}
v___jp_1894_:
{
if (v___y_1897_ == 0)
{
lean_object* v___x_1898_; lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1928_; 
lean_dec_ref(v___y_1895_);
v___x_1898_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___x_1850_, v___y_1831_);
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1901_ = v___x_1898_;
v_isShared_1902_ = v_isSharedCheck_1928_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1898_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1928_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
uint8_t v___x_1903_; 
v___x_1903_ = lean_unbox(v_a_1899_);
lean_dec(v_a_1899_);
if (v___x_1903_ == 0)
{
lean_object* v___x_1905_; 
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
if (v_isShared_1902_ == 0)
{
lean_ctor_set_tag(v___x_1901_, 1);
lean_ctor_set(v___x_1901_, 0, v___y_1896_);
v___x_1905_ = v___x_1901_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___y_1896_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
else
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
lean_del_object(v___x_1901_);
v___x_1907_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1);
lean_inc_ref(v___y_1896_);
v___x_1908_ = l_Lean_Exception_toMessageData(v___y_1896_);
v___x_1909_ = l_Lean_indentD(v___x_1908_);
v___x_1910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1907_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
v___x_1911_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1850_, v___x_1910_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1918_ == 0)
{
lean_object* v_unused_1919_; 
v_unused_1919_ = lean_ctor_get(v___x_1911_, 0);
lean_dec(v_unused_1919_);
v___x_1913_ = v___x_1911_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_dec(v___x_1911_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
lean_ctor_set_tag(v___x_1913_, 1);
lean_ctor_set(v___x_1913_, 0, v___y_1896_);
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___y_1896_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
lean_dec_ref(v___y_1896_);
v_a_1920_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1911_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1911_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
return v___y_1895_;
}
}
v___jp_1929_:
{
uint8_t v___x_1932_; 
v___x_1932_ = l_Lean_Exception_isInterrupt(v_a_1931_);
if (v___x_1932_ == 0)
{
uint8_t v___x_1933_; 
lean_inc_ref(v_a_1931_);
v___x_1933_ = l_Lean_Exception_isRuntime(v_a_1931_);
v___y_1895_ = v___y_1930_;
v___y_1896_ = v_a_1931_;
v___y_1897_ = v___x_1933_;
goto v___jp_1894_;
}
else
{
v___y_1895_ = v___y_1930_;
v___y_1896_ = v_a_1931_;
v___y_1897_ = v___x_1932_;
goto v___jp_1894_;
}
}
v___jp_1934_:
{
if (lean_obj_tag(v___y_1935_) == 0)
{
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
return v___y_1935_;
}
else
{
lean_object* v_a_1936_; 
v_a_1936_ = lean_ctor_get(v___y_1935_, 0);
lean_inc(v_a_1936_);
v___y_1930_ = v___y_1935_;
v_a_1931_ = v_a_1936_;
goto v___jp_1929_;
}
}
}
}
else
{
lean_object* v___x_2151_; lean_object* v___x_2152_; 
lean_dec(v_a_1842_);
lean_dec(v_declName_1840_);
lean_dec_ref(v_x_1827_);
lean_dec(v_mvarId_1825_);
v___x_2151_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__9, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__9_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__9);
v___x_2152_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_2151_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
return v___x_2152_;
}
}
else
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
lean_dec(v_declName_1840_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec_ref(v_x_1827_);
lean_dec(v_mvarId_1825_);
v_a_2153_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_1841_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_1841_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
else
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
lean_dec_ref(v_x_1827_);
lean_dec_ref(v_x_1826_);
lean_dec(v_mvarId_1825_);
v___x_2161_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__11, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__11_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___closed__11);
v___x_2162_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_2161_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
return v___x_2162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___boxed(lean_object* v_mvarId_2163_, lean_object* v_x_2164_, lean_object* v_x_2165_, lean_object* v_x_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5(v_mvarId_2163_, v_x_2164_, v_x_2165_, v_x_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitSparseCasesOn(lean_object* v_mvarId_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_){
_start:
{
lean_object* v___x_2179_; 
lean_inc(v_mvarId_2173_);
v___x_2179_ = l_Lean_MVarId_getType(v_mvarId_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; lean_object* v___x_2181_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_a_2180_);
lean_dec_ref(v___x_2179_);
lean_inc(v_a_2177_);
lean_inc_ref(v_a_2176_);
lean_inc(v_a_2175_);
lean_inc_ref(v_a_2174_);
v___x_2181_ = l_Lean_Meta_matchEqHEqLHS_x3f(v_a_2180_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; 
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_a_2182_);
lean_dec_ref(v___x_2181_);
if (lean_obj_tag(v_a_2182_) == 1)
{
lean_object* v_val_2183_; lean_object* v_snd_2184_; lean_object* v_dummy_2185_; lean_object* v_nargs_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v_val_2183_ = lean_ctor_get(v_a_2182_, 0);
lean_inc(v_val_2183_);
lean_dec_ref(v_a_2182_);
v_snd_2184_ = lean_ctor_get(v_val_2183_, 1);
lean_inc(v_snd_2184_);
lean_dec(v_val_2183_);
v_dummy_2185_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__8___lam__0___closed__0);
v_nargs_2186_ = l_Lean_Expr_getAppNumArgs(v_snd_2184_);
lean_inc(v_nargs_2186_);
v___x_2187_ = lean_mk_array(v_nargs_2186_, v_dummy_2185_);
v___x_2188_ = lean_unsigned_to_nat(1u);
v___x_2189_ = lean_nat_sub(v_nargs_2186_, v___x_2188_);
lean_dec(v_nargs_2186_);
v___x_2190_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5(v_mvarId_2173_, v_snd_2184_, v___x_2187_, v___x_2189_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_);
return v___x_2190_;
}
else
{
lean_object* v___x_2191_; lean_object* v___x_2192_; 
lean_dec(v_a_2182_);
lean_dec(v_mvarId_2173_);
v___x_2191_ = lean_obj_once(&l_Lean_Meta_reduceSparseCasesOn___closed__1, &l_Lean_Meta_reduceSparseCasesOn___closed__1_once, _init_l_Lean_Meta_reduceSparseCasesOn___closed__1);
v___x_2192_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_2191_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_);
lean_dec(v_a_2177_);
lean_dec_ref(v_a_2176_);
lean_dec(v_a_2175_);
lean_dec_ref(v_a_2174_);
return v___x_2192_;
}
}
else
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2200_; 
lean_dec(v_a_2177_);
lean_dec_ref(v_a_2176_);
lean_dec(v_a_2175_);
lean_dec_ref(v_a_2174_);
lean_dec(v_mvarId_2173_);
v_a_2193_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2195_ = v___x_2181_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2181_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2198_; 
if (v_isShared_2196_ == 0)
{
v___x_2198_ = v___x_2195_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2193_);
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
lean_dec(v_a_2177_);
lean_dec_ref(v_a_2176_);
lean_dec(v_a_2175_);
lean_dec_ref(v_a_2174_);
lean_dec(v_mvarId_2173_);
v_a_2201_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___x_2179_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2179_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitSparseCasesOn___boxed(lean_object* v_mvarId_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Lean_Meta_splitSparseCasesOn(v_mvarId_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_);
return v_res_2215_;
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
