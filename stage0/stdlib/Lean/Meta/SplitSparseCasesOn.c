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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
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
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSparseCasesOnInfo___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
double lean_float_of_nat(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_div(double, double);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_Meta_isConstructorApp_x27_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_mkHasNotBitProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(2, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq___closed__0 = (const lean_object*)&l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Major premise is not a constructor application:"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "Not enough arguments for sparse casesOn application"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "splitSparseCasesOn"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10_spec__11(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9___boxed(lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__3_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__4;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_unfoldDefinition___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0_value;
static const lean_closure_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__2_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Match"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__3 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__3_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchEqs"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__4 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__4_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__2_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__3_value),LEAN_SCALAR_PTR_LITERAL(250, 1, 225, 180, 135, 246, 184, 244)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5_value_aux_1),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__4_value),LEAN_SCALAR_PTR_LITERAL(142, 18, 82, 91, 15, 164, 75, 57)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__6 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__6_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__7 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__7_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__7_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__8 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__8_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Not a sparse casesOn application"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__11 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__11_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Not a const application"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__13 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__13_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_reduceSparseCasesOn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Target not an equality"};
static const lean_object* l_Lean_Meta_reduceSparseCasesOn___closed__0 = (const lean_object*)&l_Lean_Meta_reduceSparseCasesOn___closed__0_value;
static lean_once_cell_t l_Lean_Meta_reduceSparseCasesOn___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_reduceSparseCasesOn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_reduceSparseCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceSparseCasesOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(lean_object*, lean_object*, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_48_ = lean_unsigned_to_nat(32u);
v___x_49_ = lean_mk_empty_array_with_capacity(v___x_48_);
v___x_50_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
return v___x_50_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_51_ = ((size_t)5ULL);
v___x_52_ = lean_unsigned_to_nat(0u);
v___x_53_ = lean_unsigned_to_nat(32u);
v___x_54_ = lean_mk_empty_array_with_capacity(v___x_53_);
v___x_55_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__0);
v___x_56_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_56_, 0, v___x_55_);
lean_ctor_set(v___x_56_, 1, v___x_54_);
lean_ctor_set(v___x_56_, 2, v___x_52_);
lean_ctor_set(v___x_56_, 3, v___x_52_);
lean_ctor_set_usize(v___x_56_, 4, v___x_51_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(lean_object* v___y_57_){
_start:
{
lean_object* v___x_59_; lean_object* v_traceState_60_; lean_object* v_traces_61_; lean_object* v___x_62_; lean_object* v_traceState_63_; lean_object* v_env_64_; lean_object* v_nextMacroScope_65_; lean_object* v_ngen_66_; lean_object* v_auxDeclNGen_67_; lean_object* v_cache_68_; lean_object* v_messages_69_; lean_object* v_infoState_70_; lean_object* v_snapshotTasks_71_; lean_object* v_newDecls_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_91_; 
v___x_59_ = lean_st_ref_get(v___y_57_);
v_traceState_60_ = lean_ctor_get(v___x_59_, 4);
lean_inc_ref(v_traceState_60_);
lean_dec(v___x_59_);
v_traces_61_ = lean_ctor_get(v_traceState_60_, 0);
lean_inc_ref(v_traces_61_);
lean_dec_ref(v_traceState_60_);
v___x_62_ = lean_st_ref_take(v___y_57_);
v_traceState_63_ = lean_ctor_get(v___x_62_, 4);
v_env_64_ = lean_ctor_get(v___x_62_, 0);
v_nextMacroScope_65_ = lean_ctor_get(v___x_62_, 1);
v_ngen_66_ = lean_ctor_get(v___x_62_, 2);
v_auxDeclNGen_67_ = lean_ctor_get(v___x_62_, 3);
v_cache_68_ = lean_ctor_get(v___x_62_, 5);
v_messages_69_ = lean_ctor_get(v___x_62_, 6);
v_infoState_70_ = lean_ctor_get(v___x_62_, 7);
v_snapshotTasks_71_ = lean_ctor_get(v___x_62_, 8);
v_newDecls_72_ = lean_ctor_get(v___x_62_, 9);
v_isSharedCheck_91_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_91_ == 0)
{
v___x_74_ = v___x_62_;
v_isShared_75_ = v_isSharedCheck_91_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_newDecls_72_);
lean_inc(v_snapshotTasks_71_);
lean_inc(v_infoState_70_);
lean_inc(v_messages_69_);
lean_inc(v_cache_68_);
lean_inc(v_traceState_63_);
lean_inc(v_auxDeclNGen_67_);
lean_inc(v_ngen_66_);
lean_inc(v_nextMacroScope_65_);
lean_inc(v_env_64_);
lean_dec(v___x_62_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_91_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
uint64_t v_tid_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_89_; 
v_tid_76_ = lean_ctor_get_uint64(v_traceState_63_, sizeof(void*)*1);
v_isSharedCheck_89_ = !lean_is_exclusive(v_traceState_63_);
if (v_isSharedCheck_89_ == 0)
{
lean_object* v_unused_90_; 
v_unused_90_ = lean_ctor_get(v_traceState_63_, 0);
lean_dec(v_unused_90_);
v___x_78_ = v_traceState_63_;
v_isShared_79_ = v_isSharedCheck_89_;
goto v_resetjp_77_;
}
else
{
lean_dec(v_traceState_63_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_89_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_80_; lean_object* v___x_82_; 
v___x_80_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__1);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 0, v___x_80_);
v___x_82_ = v___x_78_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_80_);
lean_ctor_set_uint64(v_reuseFailAlloc_88_, sizeof(void*)*1, v_tid_76_);
v___x_82_ = v_reuseFailAlloc_88_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
lean_object* v___x_84_; 
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 4, v___x_82_);
v___x_84_ = v___x_74_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_env_64_);
lean_ctor_set(v_reuseFailAlloc_87_, 1, v_nextMacroScope_65_);
lean_ctor_set(v_reuseFailAlloc_87_, 2, v_ngen_66_);
lean_ctor_set(v_reuseFailAlloc_87_, 3, v_auxDeclNGen_67_);
lean_ctor_set(v_reuseFailAlloc_87_, 4, v___x_82_);
lean_ctor_set(v_reuseFailAlloc_87_, 5, v_cache_68_);
lean_ctor_set(v_reuseFailAlloc_87_, 6, v_messages_69_);
lean_ctor_set(v_reuseFailAlloc_87_, 7, v_infoState_70_);
lean_ctor_set(v_reuseFailAlloc_87_, 8, v_snapshotTasks_71_);
lean_ctor_set(v_reuseFailAlloc_87_, 9, v_newDecls_72_);
v___x_84_ = v_reuseFailAlloc_87_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_st_ref_set(v___y_57_, v___x_84_);
v___x_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_86_, 0, v_traces_61_);
return v___x_86_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___boxed(lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___y_92_);
lean_dec(v___y_92_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4(lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___y_98_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___boxed(lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4(v___y_101_, v___y_102_, v___y_103_, v___y_104_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
return v_res_106_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(lean_object* v_opts_107_, lean_object* v_opt_108_){
_start:
{
lean_object* v_name_109_; lean_object* v_defValue_110_; lean_object* v_map_111_; lean_object* v___x_112_; 
v_name_109_ = lean_ctor_get(v_opt_108_, 0);
v_defValue_110_ = lean_ctor_get(v_opt_108_, 1);
v_map_111_ = lean_ctor_get(v_opts_107_, 0);
v___x_112_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_111_, v_name_109_);
if (lean_obj_tag(v___x_112_) == 0)
{
uint8_t v___x_113_; 
v___x_113_ = lean_unbox(v_defValue_110_);
return v___x_113_;
}
else
{
lean_object* v_val_114_; 
v_val_114_ = lean_ctor_get(v___x_112_, 0);
lean_inc(v_val_114_);
lean_dec_ref(v___x_112_);
if (lean_obj_tag(v_val_114_) == 1)
{
uint8_t v_v_115_; 
v_v_115_ = lean_ctor_get_uint8(v_val_114_, 0);
lean_dec_ref(v_val_114_);
return v_v_115_;
}
else
{
uint8_t v___x_116_; 
lean_dec(v_val_114_);
v___x_116_ = lean_unbox(v_defValue_110_);
return v___x_116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5___boxed(lean_object* v_opts_117_, lean_object* v_opt_118_){
_start:
{
uint8_t v_res_119_; lean_object* v_r_120_; 
v_res_119_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_opts_117_, v_opt_118_);
lean_dec_ref(v_opt_118_);
lean_dec_ref(v_opts_117_);
v_r_120_ = lean_box(v_res_119_);
return v_r_120_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1_spec__2(lean_object* v_a_121_, lean_object* v_as_122_, size_t v_i_123_, size_t v_stop_124_){
_start:
{
uint8_t v___x_125_; 
v___x_125_ = lean_usize_dec_eq(v_i_123_, v_stop_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = lean_array_uget_borrowed(v_as_122_, v_i_123_);
v___x_127_ = lean_name_eq(v_a_121_, v___x_126_);
if (v___x_127_ == 0)
{
size_t v___x_128_; size_t v___x_129_; 
v___x_128_ = ((size_t)1ULL);
v___x_129_ = lean_usize_add(v_i_123_, v___x_128_);
v_i_123_ = v___x_129_;
goto _start;
}
else
{
return v___x_127_;
}
}
else
{
uint8_t v___x_131_; 
v___x_131_ = 0;
return v___x_131_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1_spec__2___boxed(lean_object* v_a_132_, lean_object* v_as_133_, lean_object* v_i_134_, lean_object* v_stop_135_){
_start:
{
size_t v_i_boxed_136_; size_t v_stop_boxed_137_; uint8_t v_res_138_; lean_object* v_r_139_; 
v_i_boxed_136_ = lean_unbox_usize(v_i_134_);
lean_dec(v_i_134_);
v_stop_boxed_137_ = lean_unbox_usize(v_stop_135_);
lean_dec(v_stop_135_);
v_res_138_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1_spec__2(v_a_132_, v_as_133_, v_i_boxed_136_, v_stop_boxed_137_);
lean_dec_ref(v_as_133_);
lean_dec(v_a_132_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1(lean_object* v_as_140_, lean_object* v_a_141_){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; uint8_t v___x_144_; 
v___x_142_ = lean_unsigned_to_nat(0u);
v___x_143_ = lean_array_get_size(v_as_140_);
v___x_144_ = lean_nat_dec_lt(v___x_142_, v___x_143_);
if (v___x_144_ == 0)
{
return v___x_144_;
}
else
{
if (v___x_144_ == 0)
{
return v___x_144_;
}
else
{
size_t v___x_145_; size_t v___x_146_; uint8_t v___x_147_; 
v___x_145_ = ((size_t)0ULL);
v___x_146_ = lean_usize_of_nat(v___x_143_);
v___x_147_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1_spec__2(v_a_141_, v_as_140_, v___x_145_, v___x_146_);
return v___x_147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1___boxed(lean_object* v_as_148_, lean_object* v_a_149_){
_start:
{
uint8_t v_res_150_; lean_object* v_r_151_; 
v_res_150_ = l_Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1(v_as_148_, v_a_149_);
lean_dec(v_a_149_);
lean_dec_ref(v_as_148_);
v_r_151_ = lean_box(v_res_150_);
return v_r_151_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_instMonadEIO(lean_box(0));
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0(lean_object* v_msg_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v_toApplicative_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_226_; 
v___x_163_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__0);
v___x_164_ = l_StateRefT_x27_instMonad___redArg(v___x_163_);
v_toApplicative_165_ = lean_ctor_get(v___x_164_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_226_ == 0)
{
lean_object* v_unused_227_; 
v_unused_227_ = lean_ctor_get(v___x_164_, 1);
lean_dec(v_unused_227_);
v___x_167_ = v___x_164_;
v_isShared_168_ = v_isSharedCheck_226_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_toApplicative_165_);
lean_dec(v___x_164_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_226_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v_toFunctor_169_; lean_object* v_toSeq_170_; lean_object* v_toSeqLeft_171_; lean_object* v_toSeqRight_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_224_; 
v_toFunctor_169_ = lean_ctor_get(v_toApplicative_165_, 0);
v_toSeq_170_ = lean_ctor_get(v_toApplicative_165_, 2);
v_toSeqLeft_171_ = lean_ctor_get(v_toApplicative_165_, 3);
v_toSeqRight_172_ = lean_ctor_get(v_toApplicative_165_, 4);
v_isSharedCheck_224_ = !lean_is_exclusive(v_toApplicative_165_);
if (v_isSharedCheck_224_ == 0)
{
lean_object* v_unused_225_; 
v_unused_225_ = lean_ctor_get(v_toApplicative_165_, 1);
lean_dec(v_unused_225_);
v___x_174_ = v_toApplicative_165_;
v_isShared_175_ = v_isSharedCheck_224_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_toSeqRight_172_);
lean_inc(v_toSeqLeft_171_);
lean_inc(v_toSeq_170_);
lean_inc(v_toFunctor_169_);
lean_dec(v_toApplicative_165_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_224_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___f_176_; lean_object* v___f_177_; lean_object* v___f_178_; lean_object* v___f_179_; lean_object* v___x_180_; lean_object* v___f_181_; lean_object* v___f_182_; lean_object* v___f_183_; lean_object* v___x_185_; 
v___f_176_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__1));
v___f_177_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_169_);
v___f_178_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_178_, 0, v_toFunctor_169_);
v___f_179_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_179_, 0, v_toFunctor_169_);
v___x_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_180_, 0, v___f_178_);
lean_ctor_set(v___x_180_, 1, v___f_179_);
v___f_181_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_181_, 0, v_toSeqRight_172_);
v___f_182_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_182_, 0, v_toSeqLeft_171_);
v___f_183_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_183_, 0, v_toSeq_170_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 4, v___f_181_);
lean_ctor_set(v___x_174_, 3, v___f_182_);
lean_ctor_set(v___x_174_, 2, v___f_183_);
lean_ctor_set(v___x_174_, 1, v___f_176_);
lean_ctor_set(v___x_174_, 0, v___x_180_);
v___x_185_ = v___x_174_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_180_);
lean_ctor_set(v_reuseFailAlloc_223_, 1, v___f_176_);
lean_ctor_set(v_reuseFailAlloc_223_, 2, v___f_183_);
lean_ctor_set(v_reuseFailAlloc_223_, 3, v___f_182_);
lean_ctor_set(v_reuseFailAlloc_223_, 4, v___f_181_);
v___x_185_ = v_reuseFailAlloc_223_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
lean_object* v___x_187_; 
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 1, v___f_177_);
lean_ctor_set(v___x_167_, 0, v___x_185_);
v___x_187_ = v___x_167_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_185_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v___f_177_);
v___x_187_ = v_reuseFailAlloc_222_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v___x_188_; lean_object* v_toApplicative_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_220_; 
v___x_188_ = l_StateRefT_x27_instMonad___redArg(v___x_187_);
v_toApplicative_189_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_220_ == 0)
{
lean_object* v_unused_221_; 
v_unused_221_ = lean_ctor_get(v___x_188_, 1);
lean_dec(v_unused_221_);
v___x_191_ = v___x_188_;
v_isShared_192_ = v_isSharedCheck_220_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_toApplicative_189_);
lean_dec(v___x_188_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_220_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v_toFunctor_193_; lean_object* v_toSeq_194_; lean_object* v_toSeqLeft_195_; lean_object* v_toSeqRight_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_218_; 
v_toFunctor_193_ = lean_ctor_get(v_toApplicative_189_, 0);
v_toSeq_194_ = lean_ctor_get(v_toApplicative_189_, 2);
v_toSeqLeft_195_ = lean_ctor_get(v_toApplicative_189_, 3);
v_toSeqRight_196_ = lean_ctor_get(v_toApplicative_189_, 4);
v_isSharedCheck_218_ = !lean_is_exclusive(v_toApplicative_189_);
if (v_isSharedCheck_218_ == 0)
{
lean_object* v_unused_219_; 
v_unused_219_ = lean_ctor_get(v_toApplicative_189_, 1);
lean_dec(v_unused_219_);
v___x_198_ = v_toApplicative_189_;
v_isShared_199_ = v_isSharedCheck_218_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_toSeqRight_196_);
lean_inc(v_toSeqLeft_195_);
lean_inc(v_toSeq_194_);
lean_inc(v_toFunctor_193_);
lean_dec(v_toApplicative_189_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_218_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___f_200_; lean_object* v___f_201_; lean_object* v___f_202_; lean_object* v___f_203_; lean_object* v___x_204_; lean_object* v___f_205_; lean_object* v___f_206_; lean_object* v___f_207_; lean_object* v___x_209_; 
v___f_200_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__3));
v___f_201_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__4));
lean_inc_ref(v_toFunctor_193_);
v___f_202_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_202_, 0, v_toFunctor_193_);
v___f_203_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_203_, 0, v_toFunctor_193_);
v___x_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_204_, 0, v___f_202_);
lean_ctor_set(v___x_204_, 1, v___f_203_);
v___f_205_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_205_, 0, v_toSeqRight_196_);
v___f_206_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_206_, 0, v_toSeqLeft_195_);
v___f_207_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_207_, 0, v_toSeq_194_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 4, v___f_205_);
lean_ctor_set(v___x_198_, 3, v___f_206_);
lean_ctor_set(v___x_198_, 2, v___f_207_);
lean_ctor_set(v___x_198_, 1, v___f_200_);
lean_ctor_set(v___x_198_, 0, v___x_204_);
v___x_209_ = v___x_198_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_204_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v___f_200_);
lean_ctor_set(v_reuseFailAlloc_217_, 2, v___f_207_);
lean_ctor_set(v_reuseFailAlloc_217_, 3, v___f_206_);
lean_ctor_set(v_reuseFailAlloc_217_, 4, v___f_205_);
v___x_209_ = v_reuseFailAlloc_217_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
lean_object* v___x_211_; 
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 1, v___f_201_);
lean_ctor_set(v___x_191_, 0, v___x_209_);
v___x_211_ = v___x_191_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_209_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v___f_201_);
v___x_211_ = v_reuseFailAlloc_216_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_10995__overap_214_; lean_object* v___x_215_; 
v___x_212_ = lean_box(0);
v___x_213_ = l_instInhabitedOfMonad___redArg(v___x_211_, v___x_212_);
v___x_10995__overap_214_ = lean_panic_fn_borrowed(v___x_213_, v_msg_157_);
lean_dec(v___x_213_);
lean_inc(v___y_161_);
lean_inc_ref(v___y_160_);
lean_inc(v___y_159_);
lean_inc_ref(v___y_158_);
v___x_215_ = lean_apply_5(v___x_10995__overap_214_, v___y_158_, v___y_159_, v___y_160_, v___y_161_, lean_box(0));
return v___x_215_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___boxed(lean_object* v_msg_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0(v_msg_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(lean_object* v_msgData_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v___x_241_; lean_object* v_env_242_; lean_object* v___x_243_; lean_object* v_mctx_244_; lean_object* v_lctx_245_; lean_object* v_options_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_241_ = lean_st_ref_get(v___y_239_);
v_env_242_ = lean_ctor_get(v___x_241_, 0);
lean_inc_ref(v_env_242_);
lean_dec(v___x_241_);
v___x_243_ = lean_st_ref_get(v___y_237_);
v_mctx_244_ = lean_ctor_get(v___x_243_, 0);
lean_inc_ref(v_mctx_244_);
lean_dec(v___x_243_);
v_lctx_245_ = lean_ctor_get(v___y_236_, 2);
v_options_246_ = lean_ctor_get(v___y_238_, 2);
lean_inc_ref(v_options_246_);
lean_inc_ref(v_lctx_245_);
v___x_247_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_247_, 0, v_env_242_);
lean_ctor_set(v___x_247_, 1, v_mctx_244_);
lean_ctor_set(v___x_247_, 2, v_lctx_245_);
lean_ctor_set(v___x_247_, 3, v_options_246_);
v___x_248_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
lean_ctor_set(v___x_248_, 1, v_msgData_235_);
v___x_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5___boxed(lean_object* v_msgData_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msgData_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(lean_object* v_msg_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
lean_object* v_ref_263_; lean_object* v___x_264_; lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_273_; 
v_ref_263_ = lean_ctor_get(v___y_260_, 5);
v___x_264_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msg_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_);
v_a_265_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_273_ == 0)
{
v___x_267_ = v___x_264_;
v_isShared_268_ = v_isSharedCheck_273_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_264_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_273_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; lean_object* v___x_271_; 
lean_inc(v_ref_263_);
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v_ref_263_);
lean_ctor_set(v___x_269_, 1, v_a_265_);
if (v_isShared_268_ == 0)
{
lean_ctor_set_tag(v___x_267_, 1);
lean_ctor_set(v___x_267_, 0, v___x_269_);
v___x_271_ = v___x_267_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_269_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg___boxed(lean_object* v_msg_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v_msg_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
return v_res_280_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__1(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__0));
v___x_283_ = l_Lean_stringToMessageData(v___x_282_);
return v___x_283_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__3(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__2));
v___x_286_ = l_Lean_stringToMessageData(v___x_285_);
return v___x_286_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__7(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_290_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__6));
v___x_291_ = lean_unsigned_to_nat(11u);
v___x_292_ = lean_unsigned_to_nat(122u);
v___x_293_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__5));
v___x_294_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__4));
v___x_295_ = l_mkPanicMessageWithDecl(v___x_294_, v___x_293_, v___x_292_, v___x_291_, v___x_290_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0(lean_object* v_constName_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v___x_310_; lean_object* v_env_311_; uint8_t v___x_312_; lean_object* v___x_313_; 
v___x_310_ = lean_st_ref_get(v___y_300_);
v_env_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc_ref(v_env_311_);
lean_dec(v___x_310_);
v___x_312_ = 0;
lean_inc(v_constName_296_);
v___x_313_ = l_Lean_Environment_findAsync_x3f(v_env_311_, v_constName_296_, v___x_312_);
if (lean_obj_tag(v___x_313_) == 1)
{
lean_object* v_val_314_; uint8_t v_kind_315_; 
v_val_314_ = lean_ctor_get(v___x_313_, 0);
lean_inc(v_val_314_);
lean_dec_ref(v___x_313_);
v_kind_315_ = lean_ctor_get_uint8(v_val_314_, sizeof(void*)*3);
if (v_kind_315_ == 6)
{
lean_object* v___x_316_; 
v___x_316_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_314_);
if (lean_obj_tag(v___x_316_) == 6)
{
lean_object* v_val_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
lean_dec(v_constName_296_);
v_val_317_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_324_ == 0)
{
v___x_319_ = v___x_316_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_val_317_);
lean_dec(v___x_316_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
lean_ctor_set_tag(v___x_319_, 0);
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_val_317_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
else
{
lean_object* v___x_325_; lean_object* v___x_326_; 
lean_dec_ref(v___x_316_);
v___x_325_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__7);
v___x_326_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0(v___x_325_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_335_; 
v_a_327_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_335_ == 0)
{
v___x_329_ = v___x_326_;
v_isShared_330_ = v_isSharedCheck_335_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_326_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_335_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
if (lean_obj_tag(v_a_327_) == 0)
{
lean_del_object(v___x_329_);
goto v___jp_302_;
}
else
{
lean_object* v_val_331_; lean_object* v___x_333_; 
lean_dec(v_constName_296_);
v_val_331_ = lean_ctor_get(v_a_327_, 0);
lean_inc(v_val_331_);
lean_dec_ref(v_a_327_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 0, v_val_331_);
v___x_333_ = v___x_329_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_val_331_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
else
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_343_; 
lean_dec(v_constName_296_);
v_a_336_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_343_ == 0)
{
v___x_338_ = v___x_326_;
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_326_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_a_336_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
}
else
{
lean_dec(v_val_314_);
goto v___jp_302_;
}
}
else
{
lean_dec(v___x_313_);
goto v___jp_302_;
}
v___jp_302_:
{
lean_object* v___x_303_; uint8_t v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_303_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__1);
v___x_304_ = 0;
v___x_305_ = l_Lean_MessageData_ofConstName(v_constName_296_, v___x_304_);
v___x_306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_303_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
v___x_307_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__3);
v___x_308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_306_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
v___x_309_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_308_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
return v___x_309_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___boxed(lean_object* v_constName_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0(v_constName_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_reduceSparseCasesOn_spec__2(size_t v_sz_351_, size_t v_i_352_, lean_object* v_bs_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
uint8_t v___x_359_; 
v___x_359_ = lean_usize_dec_lt(v_i_352_, v_sz_351_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; 
v___x_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_360_, 0, v_bs_353_);
return v___x_360_;
}
else
{
lean_object* v_v_361_; lean_object* v___x_362_; 
v_v_361_ = lean_array_uget_borrowed(v_bs_353_, v_i_352_);
lean_inc(v_v_361_);
v___x_362_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0(v_v_361_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; lean_object* v_cidx_364_; lean_object* v___x_365_; lean_object* v_bs_x27_366_; size_t v___x_367_; size_t v___x_368_; lean_object* v___x_369_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_a_363_);
lean_dec_ref(v___x_362_);
v_cidx_364_ = lean_ctor_get(v_a_363_, 2);
lean_inc(v_cidx_364_);
lean_dec(v_a_363_);
v___x_365_ = lean_unsigned_to_nat(0u);
v_bs_x27_366_ = lean_array_uset(v_bs_353_, v_i_352_, v___x_365_);
v___x_367_ = ((size_t)1ULL);
v___x_368_ = lean_usize_add(v_i_352_, v___x_367_);
v___x_369_ = lean_array_uset(v_bs_x27_366_, v_i_352_, v_cidx_364_);
v_i_352_ = v___x_368_;
v_bs_353_ = v___x_369_;
goto _start;
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
lean_dec_ref(v_bs_353_);
v_a_371_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_362_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_362_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_reduceSparseCasesOn_spec__2___boxed(lean_object* v_sz_379_, lean_object* v_i_380_, lean_object* v_bs_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
size_t v_sz_boxed_387_; size_t v_i_boxed_388_; lean_object* v_res_389_; 
v_sz_boxed_387_ = lean_unbox_usize(v_sz_379_);
lean_dec(v_sz_379_);
v_i_boxed_388_ = lean_unbox_usize(v_i_380_);
lean_dec(v_i_380_);
v_res_389_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_reduceSparseCasesOn_spec__2(v_sz_boxed_387_, v_i_boxed_388_, v_bs_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
return v_res_389_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0(void){
_start:
{
lean_object* v___x_390_; lean_object* v_dummy_391_; 
v___x_390_ = lean_box(0);
v_dummy_391_ = l_Lean_Expr_sort___override(v___x_390_);
return v_dummy_391_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__2(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__1));
v___x_394_ = l_Lean_stringToMessageData(v___x_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0(lean_object* v___x_395_, lean_object* v_x_396_, lean_object* v_majorPos_397_, lean_object* v_insterestingCtors_398_, lean_object* v_declName_399_, lean_object* v_snd_400_, lean_object* v_arity_401_, lean_object* v_mvarId_402_, lean_object* v___f_403_, lean_object* v_____r_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = lean_array_get_borrowed(v___x_395_, v_x_396_, v_majorPos_397_);
lean_inc(v___x_410_);
v___x_411_ = l_Lean_Meta_isConstructorApp_x27_x3f(v___x_410_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_a_412_);
lean_dec_ref(v___x_411_);
if (lean_obj_tag(v_a_412_) == 1)
{
lean_object* v_val_413_; lean_object* v_toConstantVal_414_; lean_object* v_cidx_415_; lean_object* v_name_416_; uint8_t v___x_417_; 
v_val_413_ = lean_ctor_get(v_a_412_, 0);
lean_inc(v_val_413_);
lean_dec_ref(v_a_412_);
v_toConstantVal_414_ = lean_ctor_get(v_val_413_, 0);
lean_inc_ref(v_toConstantVal_414_);
v_cidx_415_ = lean_ctor_get(v_val_413_, 2);
lean_inc(v_cidx_415_);
lean_dec(v_val_413_);
v_name_416_ = lean_ctor_get(v_toConstantVal_414_, 0);
lean_inc(v_name_416_);
lean_dec_ref(v_toConstantVal_414_);
v___x_417_ = l_Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1(v_insterestingCtors_398_, v_name_416_);
lean_dec(v_name_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; 
lean_dec_ref(v___f_403_);
v___x_418_ = l_Lean_Meta_getSparseCasesOnEq(v_declName_399_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; size_t v_sz_420_; size_t v___x_421_; lean_object* v___x_422_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_a_419_);
lean_dec_ref(v___x_418_);
v_sz_420_ = lean_array_size(v_insterestingCtors_398_);
v___x_421_ = ((size_t)0ULL);
v___x_422_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_reduceSparseCasesOn_spec__2(v_sz_420_, v___x_421_, v_insterestingCtors_398_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_a_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v_a_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_a_423_);
lean_dec_ref(v___x_422_);
v___x_424_ = l_Lean_mkRawNatLit(v_cidx_415_);
v___x_425_ = l_mkHasNotBitProof(v___x_424_, v_a_423_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
lean_dec(v_a_423_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_a_426_; lean_object* v___x_427_; lean_object* v_nargs_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v_dummy_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_a_426_);
lean_dec_ref(v___x_425_);
v___x_427_ = l_Lean_Expr_getAppFn(v_snd_400_);
v_nargs_428_ = l_Lean_Expr_getAppNumArgs(v_snd_400_);
v___x_429_ = l_Lean_Expr_constLevels_x21(v___x_427_);
lean_dec_ref(v___x_427_);
v___x_430_ = l_Lean_mkConst(v_a_419_, v___x_429_);
v_dummy_431_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0);
lean_inc(v_nargs_428_);
v___x_432_ = lean_mk_array(v_nargs_428_, v_dummy_431_);
v___x_433_ = lean_unsigned_to_nat(1u);
v___x_434_ = lean_nat_sub(v_nargs_428_, v___x_433_);
lean_dec(v_nargs_428_);
v___x_435_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_snd_400_, v___x_432_, v___x_434_);
v___x_436_ = lean_unsigned_to_nat(0u);
v___x_437_ = l_Array_toSubarray___redArg(v___x_435_, v___x_436_, v_arity_401_);
v___x_438_ = l_Subarray_copy___redArg(v___x_437_);
v___x_439_ = l_Lean_mkAppN(v___x_430_, v___x_438_);
lean_dec_ref(v___x_438_);
v___x_440_ = l_Lean_Expr_app___override(v___x_439_, v_a_426_);
v___x_441_ = l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq(v_mvarId_402_, v___x_440_, v___x_417_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_451_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_451_ == 0)
{
v___x_444_ = v___x_441_;
v_isShared_445_ = v_isSharedCheck_451_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_441_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_451_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_449_; 
v___x_446_ = lean_mk_empty_array_with_capacity(v___x_433_);
v___x_447_ = lean_array_push(v___x_446_, v_a_442_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_447_);
v___x_449_ = v___x_444_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_447_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
else
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
v_a_452_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_459_ == 0)
{
v___x_454_ = v___x_441_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_441_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_452_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
else
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_467_; 
lean_dec(v_a_419_);
lean_dec(v_mvarId_402_);
lean_dec(v_arity_401_);
lean_dec_ref(v_snd_400_);
v_a_460_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_467_ == 0)
{
v___x_462_ = v___x_425_;
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_425_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_465_; 
if (v_isShared_463_ == 0)
{
v___x_465_ = v___x_462_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_a_460_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
else
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
lean_dec(v_a_419_);
lean_dec(v_cidx_415_);
lean_dec(v_mvarId_402_);
lean_dec(v_arity_401_);
lean_dec_ref(v_snd_400_);
v_a_468_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v___x_422_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_422_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_a_468_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
else
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
lean_dec(v_cidx_415_);
lean_dec(v_mvarId_402_);
lean_dec(v_arity_401_);
lean_dec_ref(v_snd_400_);
lean_dec_ref(v_insterestingCtors_398_);
v_a_476_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_483_ == 0)
{
v___x_478_ = v___x_418_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_418_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_476_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
else
{
lean_object* v___x_484_; 
lean_dec(v_cidx_415_);
lean_dec(v_arity_401_);
lean_dec_ref(v_snd_400_);
lean_dec(v_declName_399_);
lean_dec_ref(v_insterestingCtors_398_);
v___x_484_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_402_, v___f_403_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_495_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_495_ == 0)
{
v___x_487_ = v___x_484_;
v_isShared_488_ = v_isSharedCheck_495_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_484_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_495_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_493_; 
v___x_489_ = lean_unsigned_to_nat(1u);
v___x_490_ = lean_mk_empty_array_with_capacity(v___x_489_);
v___x_491_ = lean_array_push(v___x_490_, v_a_485_);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 0, v___x_491_);
v___x_493_ = v___x_487_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_491_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
else
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
v_a_496_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_484_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_484_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
}
else
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
lean_dec(v_a_412_);
lean_dec_ref(v___f_403_);
lean_dec(v_mvarId_402_);
lean_dec(v_arity_401_);
lean_dec_ref(v_snd_400_);
lean_dec(v_declName_399_);
lean_dec_ref(v_insterestingCtors_398_);
v___x_504_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__2);
lean_inc(v___x_410_);
v___x_505_ = l_Lean_indentExpr(v___x_410_);
v___x_506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_504_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
v___x_507_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_506_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
return v___x_507_;
}
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
lean_dec_ref(v___f_403_);
lean_dec(v_mvarId_402_);
lean_dec(v_arity_401_);
lean_dec_ref(v_snd_400_);
lean_dec(v_declName_399_);
lean_dec_ref(v_insterestingCtors_398_);
v_a_508_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_411_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_411_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_508_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___boxed(lean_object* v___x_516_, lean_object* v_x_517_, lean_object* v_majorPos_518_, lean_object* v_insterestingCtors_519_, lean_object* v_declName_520_, lean_object* v_snd_521_, lean_object* v_arity_522_, lean_object* v_mvarId_523_, lean_object* v___f_524_, lean_object* v_____r_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0(v___x_516_, v_x_517_, v_majorPos_518_, v_insterestingCtors_519_, v_declName_520_, v_snd_521_, v_arity_522_, v_mvarId_523_, v___f_524_, v_____r_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v_majorPos_518_);
lean_dec_ref(v_x_517_);
lean_dec_ref(v___x_516_);
return v_res_531_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0));
v___x_534_ = l_Lean_stringToMessageData(v___x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(uint8_t v___x_535_, lean_object* v___f_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
if (v___x_535_ == 0)
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = lean_box(0);
lean_inc(v___y_540_);
lean_inc_ref(v___y_539_);
lean_inc(v___y_538_);
lean_inc_ref(v___y_537_);
v___x_543_ = lean_apply_6(v___f_536_, v___x_542_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, lean_box(0));
return v___x_543_;
}
else
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_553_; 
lean_dec_ref(v___f_536_);
v___x_544_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1);
v___x_545_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_544_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
v_a_546_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_553_ == 0)
{
v___x_548_ = v___x_545_;
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_545_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_551_; 
if (v_isShared_549_ == 0)
{
v___x_551_ = v___x_548_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_a_546_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___boxed(lean_object* v___x_554_, lean_object* v___f_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
uint8_t v___x_14830__boxed_561_; lean_object* v_res_562_; 
v___x_14830__boxed_561_ = lean_unbox(v___x_554_);
v_res_562_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(v___x_14830__boxed_561_, v___f_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
return v_res_562_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1(void){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__0));
v___x_565_ = l_Lean_stringToMessageData(v___x_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2(lean_object* v_x_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1);
v___x_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___boxed(lean_object* v_x_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2(v_x_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec_ref(v_x_574_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10_spec__11(size_t v_sz_581_, size_t v_i_582_, lean_object* v_bs_583_){
_start:
{
uint8_t v___x_584_; 
v___x_584_ = lean_usize_dec_lt(v_i_582_, v_sz_581_);
if (v___x_584_ == 0)
{
return v_bs_583_;
}
else
{
lean_object* v_v_585_; lean_object* v_msg_586_; lean_object* v___x_587_; lean_object* v_bs_x27_588_; size_t v___x_589_; size_t v___x_590_; lean_object* v___x_591_; 
v_v_585_ = lean_array_uget_borrowed(v_bs_583_, v_i_582_);
v_msg_586_ = lean_ctor_get(v_v_585_, 1);
lean_inc_ref(v_msg_586_);
v___x_587_ = lean_unsigned_to_nat(0u);
v_bs_x27_588_ = lean_array_uset(v_bs_583_, v_i_582_, v___x_587_);
v___x_589_ = ((size_t)1ULL);
v___x_590_ = lean_usize_add(v_i_582_, v___x_589_);
v___x_591_ = lean_array_uset(v_bs_x27_588_, v_i_582_, v_msg_586_);
v_i_582_ = v___x_590_;
v_bs_583_ = v___x_591_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10_spec__11___boxed(lean_object* v_sz_593_, lean_object* v_i_594_, lean_object* v_bs_595_){
_start:
{
size_t v_sz_boxed_596_; size_t v_i_boxed_597_; lean_object* v_res_598_; 
v_sz_boxed_596_ = lean_unbox_usize(v_sz_593_);
lean_dec(v_sz_593_);
v_i_boxed_597_ = lean_unbox_usize(v_i_594_);
lean_dec(v_i_594_);
v_res_598_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10_spec__11(v_sz_boxed_596_, v_i_boxed_597_, v_bs_595_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10(lean_object* v_oldTraces_599_, lean_object* v_data_600_, lean_object* v_ref_601_, lean_object* v_msg_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v_fileName_608_; lean_object* v_fileMap_609_; lean_object* v_options_610_; lean_object* v_currRecDepth_611_; lean_object* v_maxRecDepth_612_; lean_object* v_ref_613_; lean_object* v_currNamespace_614_; lean_object* v_openDecls_615_; lean_object* v_initHeartbeats_616_; lean_object* v_maxHeartbeats_617_; lean_object* v_quotContext_618_; lean_object* v_currMacroScope_619_; uint8_t v_diag_620_; lean_object* v_cancelTk_x3f_621_; uint8_t v_suppressElabErrors_622_; lean_object* v_inheritedTraceOptions_623_; lean_object* v___x_624_; lean_object* v_traceState_625_; lean_object* v_traces_626_; lean_object* v_ref_627_; lean_object* v___x_628_; lean_object* v___x_629_; size_t v_sz_630_; size_t v___x_631_; lean_object* v___x_632_; lean_object* v_msg_633_; lean_object* v___x_634_; lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_673_; 
v_fileName_608_ = lean_ctor_get(v___y_605_, 0);
v_fileMap_609_ = lean_ctor_get(v___y_605_, 1);
v_options_610_ = lean_ctor_get(v___y_605_, 2);
v_currRecDepth_611_ = lean_ctor_get(v___y_605_, 3);
v_maxRecDepth_612_ = lean_ctor_get(v___y_605_, 4);
v_ref_613_ = lean_ctor_get(v___y_605_, 5);
v_currNamespace_614_ = lean_ctor_get(v___y_605_, 6);
v_openDecls_615_ = lean_ctor_get(v___y_605_, 7);
v_initHeartbeats_616_ = lean_ctor_get(v___y_605_, 8);
v_maxHeartbeats_617_ = lean_ctor_get(v___y_605_, 9);
v_quotContext_618_ = lean_ctor_get(v___y_605_, 10);
v_currMacroScope_619_ = lean_ctor_get(v___y_605_, 11);
v_diag_620_ = lean_ctor_get_uint8(v___y_605_, sizeof(void*)*14);
v_cancelTk_x3f_621_ = lean_ctor_get(v___y_605_, 12);
v_suppressElabErrors_622_ = lean_ctor_get_uint8(v___y_605_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_623_ = lean_ctor_get(v___y_605_, 13);
v___x_624_ = lean_st_ref_get(v___y_606_);
v_traceState_625_ = lean_ctor_get(v___x_624_, 4);
lean_inc_ref(v_traceState_625_);
lean_dec(v___x_624_);
v_traces_626_ = lean_ctor_get(v_traceState_625_, 0);
lean_inc_ref(v_traces_626_);
lean_dec_ref(v_traceState_625_);
v_ref_627_ = l_Lean_replaceRef(v_ref_601_, v_ref_613_);
lean_inc_ref(v_inheritedTraceOptions_623_);
lean_inc(v_cancelTk_x3f_621_);
lean_inc(v_currMacroScope_619_);
lean_inc(v_quotContext_618_);
lean_inc(v_maxHeartbeats_617_);
lean_inc(v_initHeartbeats_616_);
lean_inc(v_openDecls_615_);
lean_inc(v_currNamespace_614_);
lean_inc(v_maxRecDepth_612_);
lean_inc(v_currRecDepth_611_);
lean_inc_ref(v_options_610_);
lean_inc_ref(v_fileMap_609_);
lean_inc_ref(v_fileName_608_);
v___x_628_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_628_, 0, v_fileName_608_);
lean_ctor_set(v___x_628_, 1, v_fileMap_609_);
lean_ctor_set(v___x_628_, 2, v_options_610_);
lean_ctor_set(v___x_628_, 3, v_currRecDepth_611_);
lean_ctor_set(v___x_628_, 4, v_maxRecDepth_612_);
lean_ctor_set(v___x_628_, 5, v_ref_627_);
lean_ctor_set(v___x_628_, 6, v_currNamespace_614_);
lean_ctor_set(v___x_628_, 7, v_openDecls_615_);
lean_ctor_set(v___x_628_, 8, v_initHeartbeats_616_);
lean_ctor_set(v___x_628_, 9, v_maxHeartbeats_617_);
lean_ctor_set(v___x_628_, 10, v_quotContext_618_);
lean_ctor_set(v___x_628_, 11, v_currMacroScope_619_);
lean_ctor_set(v___x_628_, 12, v_cancelTk_x3f_621_);
lean_ctor_set(v___x_628_, 13, v_inheritedTraceOptions_623_);
lean_ctor_set_uint8(v___x_628_, sizeof(void*)*14, v_diag_620_);
lean_ctor_set_uint8(v___x_628_, sizeof(void*)*14 + 1, v_suppressElabErrors_622_);
v___x_629_ = l_Lean_PersistentArray_toArray___redArg(v_traces_626_);
lean_dec_ref(v_traces_626_);
v_sz_630_ = lean_array_size(v___x_629_);
v___x_631_ = ((size_t)0ULL);
v___x_632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10_spec__11(v_sz_630_, v___x_631_, v___x_629_);
v_msg_633_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_633_, 0, v_data_600_);
lean_ctor_set(v_msg_633_, 1, v_msg_602_);
lean_ctor_set(v_msg_633_, 2, v___x_632_);
v___x_634_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msg_633_, v___y_603_, v___y_604_, v___x_628_, v___y_606_);
lean_dec_ref(v___x_628_);
v_a_635_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_673_ == 0)
{
v___x_637_ = v___x_634_;
v_isShared_638_ = v_isSharedCheck_673_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_634_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_673_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_639_; lean_object* v_traceState_640_; lean_object* v_env_641_; lean_object* v_nextMacroScope_642_; lean_object* v_ngen_643_; lean_object* v_auxDeclNGen_644_; lean_object* v_cache_645_; lean_object* v_messages_646_; lean_object* v_infoState_647_; lean_object* v_snapshotTasks_648_; lean_object* v_newDecls_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_672_; 
v___x_639_ = lean_st_ref_take(v___y_606_);
v_traceState_640_ = lean_ctor_get(v___x_639_, 4);
v_env_641_ = lean_ctor_get(v___x_639_, 0);
v_nextMacroScope_642_ = lean_ctor_get(v___x_639_, 1);
v_ngen_643_ = lean_ctor_get(v___x_639_, 2);
v_auxDeclNGen_644_ = lean_ctor_get(v___x_639_, 3);
v_cache_645_ = lean_ctor_get(v___x_639_, 5);
v_messages_646_ = lean_ctor_get(v___x_639_, 6);
v_infoState_647_ = lean_ctor_get(v___x_639_, 7);
v_snapshotTasks_648_ = lean_ctor_get(v___x_639_, 8);
v_newDecls_649_ = lean_ctor_get(v___x_639_, 9);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_672_ == 0)
{
v___x_651_ = v___x_639_;
v_isShared_652_ = v_isSharedCheck_672_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_newDecls_649_);
lean_inc(v_snapshotTasks_648_);
lean_inc(v_infoState_647_);
lean_inc(v_messages_646_);
lean_inc(v_cache_645_);
lean_inc(v_traceState_640_);
lean_inc(v_auxDeclNGen_644_);
lean_inc(v_ngen_643_);
lean_inc(v_nextMacroScope_642_);
lean_inc(v_env_641_);
lean_dec(v___x_639_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_672_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
uint64_t v_tid_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_670_; 
v_tid_653_ = lean_ctor_get_uint64(v_traceState_640_, sizeof(void*)*1);
v_isSharedCheck_670_ = !lean_is_exclusive(v_traceState_640_);
if (v_isSharedCheck_670_ == 0)
{
lean_object* v_unused_671_; 
v_unused_671_ = lean_ctor_get(v_traceState_640_, 0);
lean_dec(v_unused_671_);
v___x_655_ = v_traceState_640_;
v_isShared_656_ = v_isSharedCheck_670_;
goto v_resetjp_654_;
}
else
{
lean_dec(v_traceState_640_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_670_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_660_; 
v___x_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_657_, 0, v_ref_601_);
lean_ctor_set(v___x_657_, 1, v_a_635_);
v___x_658_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_599_, v___x_657_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_658_);
v___x_660_ = v___x_655_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_658_);
lean_ctor_set_uint64(v_reuseFailAlloc_669_, sizeof(void*)*1, v_tid_653_);
v___x_660_ = v_reuseFailAlloc_669_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
lean_object* v___x_662_; 
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 4, v___x_660_);
v___x_662_ = v___x_651_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_env_641_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_nextMacroScope_642_);
lean_ctor_set(v_reuseFailAlloc_668_, 2, v_ngen_643_);
lean_ctor_set(v_reuseFailAlloc_668_, 3, v_auxDeclNGen_644_);
lean_ctor_set(v_reuseFailAlloc_668_, 4, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_668_, 5, v_cache_645_);
lean_ctor_set(v_reuseFailAlloc_668_, 6, v_messages_646_);
lean_ctor_set(v_reuseFailAlloc_668_, 7, v_infoState_647_);
lean_ctor_set(v_reuseFailAlloc_668_, 8, v_snapshotTasks_648_);
lean_ctor_set(v_reuseFailAlloc_668_, 9, v_newDecls_649_);
v___x_662_ = v_reuseFailAlloc_668_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_666_; 
v___x_663_ = lean_st_ref_set(v___y_606_, v___x_662_);
v___x_664_ = lean_box(0);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 0, v___x_664_);
v___x_666_ = v___x_637_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___boxed(lean_object* v_oldTraces_674_, lean_object* v_data_675_, lean_object* v_ref_676_, lean_object* v_msg_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10(v_oldTraces_674_, v_data_675_, v_ref_676_, v_msg_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11___redArg(lean_object* v_x_684_){
_start:
{
if (lean_obj_tag(v_x_684_) == 0)
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_693_; 
v_a_686_ = lean_ctor_get(v_x_684_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v_x_684_);
if (v_isSharedCheck_693_ == 0)
{
v___x_688_ = v_x_684_;
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v_x_684_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_689_ == 0)
{
lean_ctor_set_tag(v___x_688_, 1);
v___x_691_ = v___x_688_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_686_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
else
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_701_; 
v_a_694_ = lean_ctor_get(v_x_684_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v_x_684_);
if (v_isSharedCheck_701_ == 0)
{
v___x_696_ = v_x_684_;
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v_x_684_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
lean_ctor_set_tag(v___x_696_, 0);
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
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11___redArg___boxed(lean_object* v_x_702_, lean_object* v___y_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11___redArg(v_x_702_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12(lean_object* v_opts_705_, lean_object* v_opt_706_){
_start:
{
lean_object* v_name_707_; lean_object* v_defValue_708_; lean_object* v_map_709_; lean_object* v___x_710_; 
v_name_707_ = lean_ctor_get(v_opt_706_, 0);
v_defValue_708_ = lean_ctor_get(v_opt_706_, 1);
v_map_709_ = lean_ctor_get(v_opts_705_, 0);
v___x_710_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_709_, v_name_707_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_inc(v_defValue_708_);
return v_defValue_708_;
}
else
{
lean_object* v_val_711_; 
v_val_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_val_711_);
lean_dec_ref(v___x_710_);
if (lean_obj_tag(v_val_711_) == 3)
{
lean_object* v_v_712_; 
v_v_712_ = lean_ctor_get(v_val_711_, 0);
lean_inc(v_v_712_);
lean_dec_ref(v_val_711_);
return v_v_712_;
}
else
{
lean_dec(v_val_711_);
lean_inc(v_defValue_708_);
return v_defValue_708_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12___boxed(lean_object* v_opts_713_, lean_object* v_opt_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12(v_opts_713_, v_opt_714_);
lean_dec_ref(v_opt_714_);
lean_dec_ref(v_opts_713_);
return v_res_715_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9(lean_object* v_e_716_){
_start:
{
if (lean_obj_tag(v_e_716_) == 0)
{
uint8_t v___x_717_; 
v___x_717_ = 2;
return v___x_717_;
}
else
{
uint8_t v___x_718_; 
v___x_718_ = 0;
return v___x_718_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9___boxed(lean_object* v_e_719_){
_start:
{
uint8_t v_res_720_; lean_object* v_r_721_; 
v_res_720_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9(v_e_719_);
lean_dec_ref(v_e_719_);
v_r_721_ = lean_box(v_res_720_);
return v_r_721_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__1(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0));
v___x_724_ = l_Lean_stringToMessageData(v___x_723_);
return v___x_724_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2(void){
_start:
{
lean_object* v___x_725_; double v___x_726_; 
v___x_725_ = lean_unsigned_to_nat(0u);
v___x_726_ = lean_float_of_nat(v___x_725_);
return v___x_726_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__4(void){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__3));
v___x_729_ = l_Lean_stringToMessageData(v___x_728_);
return v___x_729_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__5(void){
_start:
{
lean_object* v___x_730_; double v___x_731_; 
v___x_730_ = lean_unsigned_to_nat(1000u);
v___x_731_ = lean_float_of_nat(v___x_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(lean_object* v_cls_732_, uint8_t v_collapsed_733_, lean_object* v_tag_734_, lean_object* v_opts_735_, uint8_t v_clsEnabled_736_, lean_object* v_oldTraces_737_, lean_object* v_msg_738_, lean_object* v_resStartStop_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v_fst_745_; lean_object* v_snd_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_845_; 
v_fst_745_ = lean_ctor_get(v_resStartStop_739_, 0);
v_snd_746_ = lean_ctor_get(v_resStartStop_739_, 1);
v_isSharedCheck_845_ = !lean_is_exclusive(v_resStartStop_739_);
if (v_isSharedCheck_845_ == 0)
{
v___x_748_ = v_resStartStop_739_;
v_isShared_749_ = v_isSharedCheck_845_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_snd_746_);
lean_inc(v_fst_745_);
lean_dec(v_resStartStop_739_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_845_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v_data_753_; lean_object* v_fst_764_; lean_object* v_snd_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_844_; 
v_fst_764_ = lean_ctor_get(v_snd_746_, 0);
v_snd_765_ = lean_ctor_get(v_snd_746_, 1);
v_isSharedCheck_844_ = !lean_is_exclusive(v_snd_746_);
if (v_isSharedCheck_844_ == 0)
{
v___x_767_ = v_snd_746_;
v_isShared_768_ = v_isSharedCheck_844_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_snd_765_);
lean_inc(v_fst_764_);
lean_dec(v_snd_746_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_844_;
goto v_resetjp_766_;
}
v___jp_750_:
{
lean_object* v___x_754_; 
lean_inc(v___y_752_);
v___x_754_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10(v_oldTraces_737_, v_data_753_, v___y_752_, v___y_751_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v___x_755_; 
lean_dec_ref(v___x_754_);
v___x_755_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11___redArg(v_fst_745_);
return v___x_755_;
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec(v_fst_745_);
v_a_756_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_754_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_754_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
v_resetjp_766_:
{
lean_object* v___x_769_; uint8_t v___x_770_; lean_object* v___y_772_; lean_object* v_a_773_; uint8_t v___y_797_; double v___y_829_; 
v___x_769_ = l_Lean_trace_profiler;
v___x_770_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_opts_735_, v___x_769_);
if (v___x_770_ == 0)
{
v___y_797_ = v___x_770_;
goto v___jp_796_;
}
else
{
lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_834_ = l_Lean_trace_profiler_useHeartbeats;
v___x_835_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_opts_735_, v___x_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; lean_object* v___x_837_; double v___x_838_; double v___x_839_; double v___x_840_; 
v___x_836_ = l_Lean_trace_profiler_threshold;
v___x_837_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12(v_opts_735_, v___x_836_);
v___x_838_ = lean_float_of_nat(v___x_837_);
v___x_839_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__5);
v___x_840_ = lean_float_div(v___x_838_, v___x_839_);
v___y_829_ = v___x_840_;
goto v___jp_828_;
}
else
{
lean_object* v___x_841_; lean_object* v___x_842_; double v___x_843_; 
v___x_841_ = l_Lean_trace_profiler_threshold;
v___x_842_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12(v_opts_735_, v___x_841_);
v___x_843_ = lean_float_of_nat(v___x_842_);
v___y_829_ = v___x_843_;
goto v___jp_828_;
}
}
v___jp_771_:
{
uint8_t v_result_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_779_; 
v_result_774_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9(v_fst_745_);
v___x_775_ = l_Lean_TraceResult_toEmoji(v_result_774_);
v___x_776_ = l_Lean_stringToMessageData(v___x_775_);
v___x_777_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__1);
if (v_isShared_768_ == 0)
{
lean_ctor_set_tag(v___x_767_, 7);
lean_ctor_set(v___x_767_, 1, v___x_777_);
lean_ctor_set(v___x_767_, 0, v___x_776_);
v___x_779_ = v___x_767_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v___x_777_);
v___x_779_ = v_reuseFailAlloc_790_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
lean_object* v_m_781_; 
if (v_isShared_749_ == 0)
{
lean_ctor_set_tag(v___x_748_, 7);
lean_ctor_set(v___x_748_, 1, v_a_773_);
lean_ctor_set(v___x_748_, 0, v___x_779_);
v_m_781_ = v___x_748_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_779_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_a_773_);
v_m_781_ = v_reuseFailAlloc_789_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_782_; lean_object* v___x_783_; double v___x_784_; lean_object* v_data_785_; 
v___x_782_ = lean_box(v_result_774_);
v___x_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
v___x_784_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2);
lean_inc_ref(v_tag_734_);
lean_inc_ref(v___x_783_);
lean_inc(v_cls_732_);
v_data_785_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_785_, 0, v_cls_732_);
lean_ctor_set(v_data_785_, 1, v___x_783_);
lean_ctor_set(v_data_785_, 2, v_tag_734_);
lean_ctor_set_float(v_data_785_, sizeof(void*)*3, v___x_784_);
lean_ctor_set_float(v_data_785_, sizeof(void*)*3 + 8, v___x_784_);
lean_ctor_set_uint8(v_data_785_, sizeof(void*)*3 + 16, v_collapsed_733_);
if (v___x_770_ == 0)
{
lean_dec_ref(v___x_783_);
lean_dec(v_snd_765_);
lean_dec(v_fst_764_);
lean_dec_ref(v_tag_734_);
lean_dec(v_cls_732_);
v___y_751_ = v_m_781_;
v___y_752_ = v___y_772_;
v_data_753_ = v_data_785_;
goto v___jp_750_;
}
else
{
lean_object* v_data_786_; double v___x_787_; double v___x_788_; 
lean_dec_ref(v_data_785_);
v_data_786_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_786_, 0, v_cls_732_);
lean_ctor_set(v_data_786_, 1, v___x_783_);
lean_ctor_set(v_data_786_, 2, v_tag_734_);
v___x_787_ = lean_unbox_float(v_fst_764_);
lean_dec(v_fst_764_);
lean_ctor_set_float(v_data_786_, sizeof(void*)*3, v___x_787_);
v___x_788_ = lean_unbox_float(v_snd_765_);
lean_dec(v_snd_765_);
lean_ctor_set_float(v_data_786_, sizeof(void*)*3 + 8, v___x_788_);
lean_ctor_set_uint8(v_data_786_, sizeof(void*)*3 + 16, v_collapsed_733_);
v___y_751_ = v_m_781_;
v___y_752_ = v___y_772_;
v_data_753_ = v_data_786_;
goto v___jp_750_;
}
}
}
}
v___jp_791_:
{
lean_object* v_ref_792_; lean_object* v___x_793_; 
v_ref_792_ = lean_ctor_get(v___y_742_, 5);
lean_inc(v___y_743_);
lean_inc_ref(v___y_742_);
lean_inc(v___y_741_);
lean_inc_ref(v___y_740_);
lean_inc(v_fst_745_);
v___x_793_ = lean_apply_6(v_msg_738_, v_fst_745_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, lean_box(0));
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v_a_794_; 
v_a_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_a_794_);
lean_dec_ref(v___x_793_);
v___y_772_ = v_ref_792_;
v_a_773_ = v_a_794_;
goto v___jp_771_;
}
else
{
lean_object* v___x_795_; 
lean_dec_ref(v___x_793_);
v___x_795_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__4);
v___y_772_ = v_ref_792_;
v_a_773_ = v___x_795_;
goto v___jp_771_;
}
}
v___jp_796_:
{
if (v_clsEnabled_736_ == 0)
{
if (v___y_797_ == 0)
{
lean_object* v___x_798_; lean_object* v_traceState_799_; lean_object* v_env_800_; lean_object* v_nextMacroScope_801_; lean_object* v_ngen_802_; lean_object* v_auxDeclNGen_803_; lean_object* v_cache_804_; lean_object* v_messages_805_; lean_object* v_infoState_806_; lean_object* v_snapshotTasks_807_; lean_object* v_newDecls_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_827_; 
lean_del_object(v___x_767_);
lean_dec(v_snd_765_);
lean_dec(v_fst_764_);
lean_del_object(v___x_748_);
lean_dec_ref(v_msg_738_);
lean_dec_ref(v_tag_734_);
lean_dec(v_cls_732_);
v___x_798_ = lean_st_ref_take(v___y_743_);
v_traceState_799_ = lean_ctor_get(v___x_798_, 4);
v_env_800_ = lean_ctor_get(v___x_798_, 0);
v_nextMacroScope_801_ = lean_ctor_get(v___x_798_, 1);
v_ngen_802_ = lean_ctor_get(v___x_798_, 2);
v_auxDeclNGen_803_ = lean_ctor_get(v___x_798_, 3);
v_cache_804_ = lean_ctor_get(v___x_798_, 5);
v_messages_805_ = lean_ctor_get(v___x_798_, 6);
v_infoState_806_ = lean_ctor_get(v___x_798_, 7);
v_snapshotTasks_807_ = lean_ctor_get(v___x_798_, 8);
v_newDecls_808_ = lean_ctor_get(v___x_798_, 9);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_827_ == 0)
{
v___x_810_ = v___x_798_;
v_isShared_811_ = v_isSharedCheck_827_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_newDecls_808_);
lean_inc(v_snapshotTasks_807_);
lean_inc(v_infoState_806_);
lean_inc(v_messages_805_);
lean_inc(v_cache_804_);
lean_inc(v_traceState_799_);
lean_inc(v_auxDeclNGen_803_);
lean_inc(v_ngen_802_);
lean_inc(v_nextMacroScope_801_);
lean_inc(v_env_800_);
lean_dec(v___x_798_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_827_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
uint64_t v_tid_812_; lean_object* v_traces_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_826_; 
v_tid_812_ = lean_ctor_get_uint64(v_traceState_799_, sizeof(void*)*1);
v_traces_813_ = lean_ctor_get(v_traceState_799_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v_traceState_799_);
if (v_isSharedCheck_826_ == 0)
{
v___x_815_ = v_traceState_799_;
v_isShared_816_ = v_isSharedCheck_826_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_traces_813_);
lean_dec(v_traceState_799_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_826_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_817_; lean_object* v___x_819_; 
v___x_817_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_737_, v_traces_813_);
lean_dec_ref(v_traces_813_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_817_);
v___x_819_ = v___x_815_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_817_);
lean_ctor_set_uint64(v_reuseFailAlloc_825_, sizeof(void*)*1, v_tid_812_);
v___x_819_ = v_reuseFailAlloc_825_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
lean_object* v___x_821_; 
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 4, v___x_819_);
v___x_821_ = v___x_810_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_env_800_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v_nextMacroScope_801_);
lean_ctor_set(v_reuseFailAlloc_824_, 2, v_ngen_802_);
lean_ctor_set(v_reuseFailAlloc_824_, 3, v_auxDeclNGen_803_);
lean_ctor_set(v_reuseFailAlloc_824_, 4, v___x_819_);
lean_ctor_set(v_reuseFailAlloc_824_, 5, v_cache_804_);
lean_ctor_set(v_reuseFailAlloc_824_, 6, v_messages_805_);
lean_ctor_set(v_reuseFailAlloc_824_, 7, v_infoState_806_);
lean_ctor_set(v_reuseFailAlloc_824_, 8, v_snapshotTasks_807_);
lean_ctor_set(v_reuseFailAlloc_824_, 9, v_newDecls_808_);
v___x_821_ = v_reuseFailAlloc_824_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = lean_st_ref_set(v___y_743_, v___x_821_);
v___x_823_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11___redArg(v_fst_745_);
return v___x_823_;
}
}
}
}
}
else
{
goto v___jp_791_;
}
}
else
{
goto v___jp_791_;
}
}
v___jp_828_:
{
double v___x_830_; double v___x_831_; double v___x_832_; uint8_t v___x_833_; 
v___x_830_ = lean_unbox_float(v_snd_765_);
v___x_831_ = lean_unbox_float(v_fst_764_);
v___x_832_ = lean_float_sub(v___x_830_, v___x_831_);
v___x_833_ = lean_float_decLt(v___y_829_, v___x_832_);
v___y_797_ = v___x_833_;
goto v___jp_796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___boxed(lean_object* v_cls_846_, lean_object* v_collapsed_847_, lean_object* v_tag_848_, lean_object* v_opts_849_, lean_object* v_clsEnabled_850_, lean_object* v_oldTraces_851_, lean_object* v_msg_852_, lean_object* v_resStartStop_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
uint8_t v_collapsed_boxed_859_; uint8_t v_clsEnabled_boxed_860_; lean_object* v_res_861_; 
v_collapsed_boxed_859_ = lean_unbox(v_collapsed_847_);
v_clsEnabled_boxed_860_ = lean_unbox(v_clsEnabled_850_);
v_res_861_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v_cls_846_, v_collapsed_boxed_859_, v_tag_848_, v_opts_849_, v_clsEnabled_boxed_860_, v_oldTraces_851_, v_msg_852_, v_resStartStop_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec_ref(v_opts_849_);
return v_res_861_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_875_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5));
v___x_876_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__8));
v___x_877_ = l_Lean_Name_append(v___x_876_, v___x_875_);
return v___x_877_;
}
}
static double _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10(void){
_start:
{
lean_object* v___x_878_; double v___x_879_; 
v___x_878_ = lean_unsigned_to_nat(1000000000u);
v___x_879_ = lean_float_of_nat(v___x_878_);
return v___x_879_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12(void){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__11));
v___x_882_ = l_Lean_stringToMessageData(v___x_881_);
return v___x_882_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14(void){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__13));
v___x_885_ = l_Lean_stringToMessageData(v___x_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7(lean_object* v_snd_886_, lean_object* v_mvarId_887_, lean_object* v_x_888_, lean_object* v_x_889_, lean_object* v_x_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
if (lean_obj_tag(v_x_888_) == 5)
{
lean_object* v_fn_896_; lean_object* v_arg_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v_fn_896_ = lean_ctor_get(v_x_888_, 0);
lean_inc_ref(v_fn_896_);
v_arg_897_ = lean_ctor_get(v_x_888_, 1);
lean_inc_ref(v_arg_897_);
lean_dec_ref(v_x_888_);
v___x_898_ = lean_array_set(v_x_889_, v_x_890_, v_arg_897_);
v___x_899_ = lean_unsigned_to_nat(1u);
v___x_900_ = lean_nat_sub(v_x_890_, v___x_899_);
lean_dec(v_x_890_);
v_x_888_ = v_fn_896_;
v_x_889_ = v___x_898_;
v_x_890_ = v___x_900_;
goto _start;
}
else
{
lean_dec(v_x_890_);
if (lean_obj_tag(v_x_888_) == 4)
{
lean_object* v_declName_902_; lean_object* v___x_903_; 
v_declName_902_ = lean_ctor_get(v_x_888_, 0);
lean_inc_n(v_declName_902_, 2);
lean_dec_ref(v_x_888_);
v___x_903_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_declName_902_, v___y_894_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_a_904_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_a_904_);
lean_dec_ref(v___x_903_);
if (lean_obj_tag(v_a_904_) == 1)
{
lean_object* v_val_905_; lean_object* v_options_906_; lean_object* v_majorPos_907_; lean_object* v_arity_908_; lean_object* v_insterestingCtors_909_; lean_object* v_inheritedTraceOptions_910_; uint8_t v_hasTrace_911_; lean_object* v___f_912_; lean_object* v___x_913_; lean_object* v___f_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v_val_905_ = lean_ctor_get(v_a_904_, 0);
lean_inc(v_val_905_);
lean_dec_ref(v_a_904_);
v_options_906_ = lean_ctor_get(v___y_893_, 2);
v_majorPos_907_ = lean_ctor_get(v_val_905_, 1);
lean_inc(v_majorPos_907_);
v_arity_908_ = lean_ctor_get(v_val_905_, 2);
lean_inc_n(v_arity_908_, 2);
v_insterestingCtors_909_ = lean_ctor_get(v_val_905_, 3);
lean_inc_ref(v_insterestingCtors_909_);
lean_dec(v_val_905_);
v_inheritedTraceOptions_910_ = lean_ctor_get(v___y_893_, 13);
v_hasTrace_911_ = lean_ctor_get_uint8(v_options_906_, sizeof(void*)*1);
v___f_912_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0));
v___x_913_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_x_889_);
v___f_914_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___boxed), 15, 9);
lean_closure_set(v___f_914_, 0, v___x_913_);
lean_closure_set(v___f_914_, 1, v_x_889_);
lean_closure_set(v___f_914_, 2, v_majorPos_907_);
lean_closure_set(v___f_914_, 3, v_insterestingCtors_909_);
lean_closure_set(v___f_914_, 4, v_declName_902_);
lean_closure_set(v___f_914_, 5, v_snd_886_);
lean_closure_set(v___f_914_, 6, v_arity_908_);
lean_closure_set(v___f_914_, 7, v_mvarId_887_);
lean_closure_set(v___f_914_, 8, v___f_912_);
v___x_915_ = lean_array_get_size(v_x_889_);
lean_dec_ref(v_x_889_);
v___x_916_ = lean_nat_dec_lt(v___x_915_, v_arity_908_);
lean_dec(v_arity_908_);
if (v_hasTrace_911_ == 0)
{
lean_object* v___x_917_; 
v___x_917_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(v___x_916_, v___f_914_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
return v___x_917_;
}
else
{
lean_object* v___f_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; uint8_t v___x_922_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v_a_926_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v_a_941_; 
v___f_918_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1));
v___x_919_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5));
v___x_920_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__6));
v___x_921_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9);
v___x_922_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_910_, v_options_906_, v___x_921_);
if (v___x_922_ == 0)
{
lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_991_ = l_Lean_trace_profiler;
v___x_992_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_options_906_, v___x_991_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; 
v___x_993_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(v___x_916_, v___f_914_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
return v___x_993_;
}
else
{
goto v___jp_950_;
}
}
else
{
goto v___jp_950_;
}
v___jp_923_:
{
lean_object* v___x_927_; double v___x_928_; double v___x_929_; double v___x_930_; double v___x_931_; double v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_927_ = lean_io_mono_nanos_now();
v___x_928_ = lean_float_of_nat(v___y_924_);
v___x_929_ = lean_float_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10);
v___x_930_ = lean_float_div(v___x_928_, v___x_929_);
v___x_931_ = lean_float_of_nat(v___x_927_);
v___x_932_ = lean_float_div(v___x_931_, v___x_929_);
v___x_933_ = lean_box_float(v___x_930_);
v___x_934_ = lean_box_float(v___x_932_);
v___x_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_933_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_936_, 0, v_a_926_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_919_, v_hasTrace_911_, v___x_920_, v_options_906_, v___x_922_, v___y_925_, v___f_918_, v___x_936_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
return v___x_937_;
}
v___jp_938_:
{
lean_object* v___x_942_; double v___x_943_; double v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_942_ = lean_io_get_num_heartbeats();
v___x_943_ = lean_float_of_nat(v___y_939_);
v___x_944_ = lean_float_of_nat(v___x_942_);
v___x_945_ = lean_box_float(v___x_943_);
v___x_946_ = lean_box_float(v___x_944_);
v___x_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_945_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
v___x_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_948_, 0, v_a_941_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_919_, v_hasTrace_911_, v___x_920_, v_options_906_, v___x_922_, v___y_940_, v___f_918_, v___x_948_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
return v___x_949_;
}
v___jp_950_:
{
lean_object* v___x_951_; lean_object* v_a_952_; lean_object* v___x_953_; uint8_t v___x_954_; 
v___x_951_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___y_894_);
v_a_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_952_);
lean_dec_ref(v___x_951_);
v___x_953_ = l_Lean_trace_profiler_useHeartbeats;
v___x_954_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_options_906_, v___x_953_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = lean_io_mono_nanos_now();
v___x_956_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(v___x_916_, v___f_914_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
lean_ctor_set_tag(v___x_959_, 1);
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
v___y_924_ = v___x_955_;
v___y_925_ = v_a_952_;
v_a_926_ = v___x_962_;
goto v___jp_923_;
}
}
}
else
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_972_; 
v_a_965_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_972_ == 0)
{
v___x_967_ = v___x_956_;
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_956_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
lean_ctor_set_tag(v___x_967_, 0);
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_965_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
v___y_924_ = v___x_955_;
v___y_925_ = v_a_952_;
v_a_926_ = v___x_970_;
goto v___jp_923_;
}
}
}
}
else
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = lean_io_get_num_heartbeats();
v___x_974_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(v___x_916_, v___f_914_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_974_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_974_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
lean_ctor_set_tag(v___x_977_, 1);
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
v___y_939_ = v___x_973_;
v___y_940_ = v_a_952_;
v_a_941_ = v___x_980_;
goto v___jp_938_;
}
}
}
else
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
v_a_983_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_974_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_974_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
lean_ctor_set_tag(v___x_985_, 0);
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
v___y_939_ = v___x_973_;
v___y_940_ = v_a_952_;
v_a_941_ = v___x_988_;
goto v___jp_938_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_994_; lean_object* v___x_995_; 
lean_dec(v_a_904_);
lean_dec(v_declName_902_);
lean_dec_ref(v_x_889_);
lean_dec(v_mvarId_887_);
lean_dec_ref(v_snd_886_);
v___x_994_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12);
v___x_995_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_994_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
return v___x_995_;
}
}
else
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
lean_dec(v_declName_902_);
lean_dec_ref(v_x_889_);
lean_dec(v_mvarId_887_);
lean_dec_ref(v_snd_886_);
v_a_996_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_903_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_903_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_999_ == 0)
{
v___x_1001_ = v___x_998_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_996_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
else
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
lean_dec_ref(v_x_889_);
lean_dec_ref(v_x_888_);
lean_dec(v_mvarId_887_);
lean_dec_ref(v_snd_886_);
v___x_1004_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14);
v___x_1005_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1004_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
return v___x_1005_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___boxed(lean_object* v_snd_1006_, lean_object* v_mvarId_1007_, lean_object* v_x_1008_, lean_object* v_x_1009_, lean_object* v_x_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7(v_snd_1006_, v_mvarId_1007_, v_x_1008_, v_x_1009_, v_x_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
return v_res_1016_;
}
}
static lean_object* _init_l_Lean_Meta_reduceSparseCasesOn___closed__1(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = ((lean_object*)(l_Lean_Meta_reduceSparseCasesOn___closed__0));
v___x_1019_ = l_Lean_stringToMessageData(v___x_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceSparseCasesOn(lean_object* v_mvarId_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v___x_1026_; 
lean_inc(v_mvarId_1020_);
v___x_1026_ = l_Lean_MVarId_getType(v_mvarId_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v___x_1028_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1027_);
lean_dec_ref(v___x_1026_);
v___x_1028_ = l_Lean_Meta_matchEqHEqLHS_x3f(v_a_1027_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_a_1029_);
lean_dec_ref(v___x_1028_);
if (lean_obj_tag(v_a_1029_) == 1)
{
lean_object* v_val_1030_; lean_object* v_snd_1031_; lean_object* v_dummy_1032_; lean_object* v_nargs_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v_val_1030_ = lean_ctor_get(v_a_1029_, 0);
lean_inc(v_val_1030_);
lean_dec_ref(v_a_1029_);
v_snd_1031_ = lean_ctor_get(v_val_1030_, 1);
lean_inc_n(v_snd_1031_, 2);
lean_dec(v_val_1030_);
v_dummy_1032_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0);
v_nargs_1033_ = l_Lean_Expr_getAppNumArgs(v_snd_1031_);
lean_inc(v_nargs_1033_);
v___x_1034_ = lean_mk_array(v_nargs_1033_, v_dummy_1032_);
v___x_1035_ = lean_unsigned_to_nat(1u);
v___x_1036_ = lean_nat_sub(v_nargs_1033_, v___x_1035_);
lean_dec(v_nargs_1033_);
v___x_1037_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7(v_snd_1031_, v_mvarId_1020_, v_snd_1031_, v___x_1034_, v___x_1036_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_);
return v___x_1037_;
}
else
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
lean_dec(v_a_1029_);
lean_dec(v_mvarId_1020_);
v___x_1038_ = lean_obj_once(&l_Lean_Meta_reduceSparseCasesOn___closed__1, &l_Lean_Meta_reduceSparseCasesOn___closed__1_once, _init_l_Lean_Meta_reduceSparseCasesOn___closed__1);
v___x_1039_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1038_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_);
return v___x_1039_;
}
}
else
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
lean_dec(v_mvarId_1020_);
v_a_1040_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v___x_1028_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1028_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_a_1040_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
lean_dec(v_mvarId_1020_);
v_a_1048_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_1026_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1026_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceSparseCasesOn___boxed(lean_object* v_mvarId_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lean_Meta_reduceSparseCasesOn(v_mvarId_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_);
lean_dec(v_a_1060_);
lean_dec_ref(v_a_1059_);
lean_dec(v_a_1058_);
lean_dec_ref(v_a_1057_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3(lean_object* v_00_u03b1_1063_, lean_object* v_msg_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v_msg_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___boxed(lean_object* v_00_u03b1_1071_, lean_object* v_msg_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3(v_00_u03b1_1071_, v_msg_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11(lean_object* v_00_u03b1_1079_, lean_object* v_x_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11___redArg(v_x_1080_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11___boxed(lean_object* v_00_u03b1_1087_, lean_object* v_x_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11(v_00_u03b1_1087_, v_x_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(lean_object* v_mvarId_1095_, lean_object* v_x_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v___x_1102_; 
v___x_1102_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1095_, v_x_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1102_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1102_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
v_a_1111_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1102_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1102_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg___boxed(lean_object* v_mvarId_1119_, lean_object* v_x_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1119_, v_x_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2(lean_object* v_00_u03b1_1127_, lean_object* v_mvarId_1128_, lean_object* v_x_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1128_, v_x_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___boxed(lean_object* v_00_u03b1_1136_, lean_object* v_mvarId_1137_, lean_object* v_x_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2(v_00_u03b1_1136_, v_mvarId_1137_, v_x_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_splitSparseCasesOn_spec__1(lean_object* v_a_1145_, lean_object* v_a_1146_){
_start:
{
if (lean_obj_tag(v_a_1145_) == 0)
{
lean_object* v___x_1147_; 
v___x_1147_ = l_List_reverse___redArg(v_a_1146_);
return v___x_1147_;
}
else
{
lean_object* v_head_1148_; lean_object* v_tail_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1158_; 
v_head_1148_ = lean_ctor_get(v_a_1145_, 0);
v_tail_1149_ = lean_ctor_get(v_a_1145_, 1);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_a_1145_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1151_ = v_a_1145_;
v_isShared_1152_ = v_isSharedCheck_1158_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_tail_1149_);
lean_inc(v_head_1148_);
lean_dec(v_a_1145_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1158_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1153_ = l_Lean_MessageData_ofExpr(v_head_1148_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 1, v_a_1146_);
lean_ctor_set(v___x_1151_, 0, v___x_1153_);
v___x_1155_ = v___x_1151_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1153_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v_a_1146_);
v___x_1155_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
v_a_1145_ = v_tail_1149_;
v_a_1146_ = v___x_1155_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__0));
v___x_1161_ = l_Lean_stringToMessageData(v___x_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0(uint8_t v___y_1162_, lean_object* v_mvarId_1163_, lean_object* v___f_1164_, lean_object* v_declName_1165_, lean_object* v_val_1166_, lean_object* v___x_1167_, lean_object* v_fields_1168_, uint8_t v___x_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v___y_1176_; lean_object* v___y_1177_; lean_object* v___y_1178_; lean_object* v___y_1179_; 
if (v___y_1162_ == 0)
{
lean_object* v___x_1231_; 
lean_dec_ref(v_fields_1168_);
lean_dec_ref(v_val_1166_);
lean_dec(v_declName_1165_);
v___x_1231_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_1163_, v___f_1164_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
return v___x_1231_;
}
else
{
lean_object* v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
lean_dec_ref(v___f_1164_);
v___x_1232_ = lean_array_get_size(v_fields_1168_);
v___x_1233_ = lean_unsigned_to_nat(1u);
v___x_1234_ = lean_nat_dec_eq(v___x_1232_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1235_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1);
lean_inc_ref(v_fields_1168_);
v___x_1236_ = lean_array_to_list(v_fields_1168_);
v___x_1237_ = lean_box(0);
v___x_1238_ = l_List_mapTR_loop___at___00Lean_Meta_splitSparseCasesOn_spec__1(v___x_1236_, v___x_1237_);
v___x_1239_ = l_Lean_MessageData_ofList(v___x_1238_);
v___x_1240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1235_);
lean_ctor_set(v___x_1240_, 1, v___x_1239_);
v___x_1241_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1240_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_dec_ref(v___x_1241_);
v___y_1176_ = v___y_1170_;
v___y_1177_ = v___y_1171_;
v___y_1178_ = v___y_1172_;
v___y_1179_ = v___y_1173_;
goto v___jp_1175_;
}
else
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
lean_dec_ref(v_fields_1168_);
lean_dec_ref(v_val_1166_);
lean_dec(v_declName_1165_);
lean_dec(v_mvarId_1163_);
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1244_ = v___x_1241_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1241_);
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
v___y_1176_ = v___y_1170_;
v___y_1177_ = v___y_1171_;
v___y_1178_ = v___y_1172_;
v___y_1179_ = v___y_1173_;
goto v___jp_1175_;
}
}
v___jp_1175_:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_Lean_Meta_getSparseCasesOnEq(v_declName_1165_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; lean_object* v___x_1182_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_a_1181_);
lean_dec_ref(v___x_1180_);
lean_inc(v_mvarId_1163_);
v___x_1182_ = l_Lean_MVarId_getType(v_mvarId_1163_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1184_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_a_1183_);
lean_dec_ref(v___x_1182_);
v___x_1184_ = l_Lean_Meta_matchEqHEqLHS_x3f(v_a_1183_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_a_1185_; 
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
lean_inc(v_a_1185_);
lean_dec_ref(v___x_1184_);
if (lean_obj_tag(v_a_1185_) == 1)
{
lean_object* v_val_1186_; lean_object* v_snd_1187_; lean_object* v_arity_1188_; lean_object* v___x_1189_; lean_object* v_nargs_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v_dummy_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v_val_1186_ = lean_ctor_get(v_a_1185_, 0);
lean_inc(v_val_1186_);
lean_dec_ref(v_a_1185_);
v_snd_1187_ = lean_ctor_get(v_val_1186_, 1);
lean_inc(v_snd_1187_);
lean_dec(v_val_1186_);
v_arity_1188_ = lean_ctor_get(v_val_1166_, 2);
lean_inc(v_arity_1188_);
lean_dec_ref(v_val_1166_);
v___x_1189_ = l_Lean_Expr_getAppFn(v_snd_1187_);
v_nargs_1190_ = l_Lean_Expr_getAppNumArgs(v_snd_1187_);
v___x_1191_ = l_Lean_Expr_constLevels_x21(v___x_1189_);
lean_dec_ref(v___x_1189_);
v___x_1192_ = l_Lean_mkConst(v_a_1181_, v___x_1191_);
v_dummy_1193_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0);
lean_inc(v_nargs_1190_);
v___x_1194_ = lean_mk_array(v_nargs_1190_, v_dummy_1193_);
v___x_1195_ = lean_unsigned_to_nat(1u);
v___x_1196_ = lean_nat_sub(v_nargs_1190_, v___x_1195_);
lean_dec(v_nargs_1190_);
v___x_1197_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_snd_1187_, v___x_1194_, v___x_1196_);
v___x_1198_ = lean_unsigned_to_nat(0u);
v___x_1199_ = l_Array_toSubarray___redArg(v___x_1197_, v___x_1198_, v_arity_1188_);
v___x_1200_ = l_Subarray_copy___redArg(v___x_1199_);
v___x_1201_ = l_Lean_mkAppN(v___x_1192_, v___x_1200_);
lean_dec_ref(v___x_1200_);
v___x_1202_ = lean_array_get(v___x_1167_, v_fields_1168_, v___x_1198_);
lean_dec_ref(v_fields_1168_);
v___x_1203_ = l_Lean_Expr_app___override(v___x_1201_, v___x_1202_);
v___x_1204_ = l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq(v_mvarId_1163_, v___x_1203_, v___x_1169_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
return v___x_1204_;
}
else
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_dec(v_a_1185_);
lean_dec(v_a_1181_);
lean_dec_ref(v_fields_1168_);
lean_dec_ref(v_val_1166_);
lean_dec(v_mvarId_1163_);
v___x_1205_ = lean_obj_once(&l_Lean_Meta_reduceSparseCasesOn___closed__1, &l_Lean_Meta_reduceSparseCasesOn___closed__1_once, _init_l_Lean_Meta_reduceSparseCasesOn___closed__1);
v___x_1206_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1205_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
return v___x_1206_;
}
}
else
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
lean_dec(v_a_1181_);
lean_dec_ref(v_fields_1168_);
lean_dec_ref(v_val_1166_);
lean_dec(v_mvarId_1163_);
v_a_1207_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_1184_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1184_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
lean_dec(v_a_1181_);
lean_dec_ref(v_fields_1168_);
lean_dec_ref(v_val_1166_);
lean_dec(v_mvarId_1163_);
v_a_1215_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1182_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1182_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
lean_dec_ref(v_fields_1168_);
lean_dec_ref(v_val_1166_);
lean_dec(v_mvarId_1163_);
v_a_1223_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1180_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1180_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed(lean_object* v___y_1250_, lean_object* v_mvarId_1251_, lean_object* v___f_1252_, lean_object* v_declName_1253_, lean_object* v_val_1254_, lean_object* v___x_1255_, lean_object* v_fields_1256_, lean_object* v___x_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
uint8_t v___y_33614__boxed_1263_; uint8_t v___x_33619__boxed_1264_; lean_object* v_res_1265_; 
v___y_33614__boxed_1263_ = lean_unbox(v___y_1250_);
v___x_33619__boxed_1264_ = lean_unbox(v___x_1257_);
v_res_1265_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0(v___y_33614__boxed_1263_, v_mvarId_1251_, v___f_1252_, v_declName_1253_, v_val_1254_, v___x_1255_, v_fields_1256_, v___x_33619__boxed_1264_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec_ref(v___x_1255_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(lean_object* v_declName_1266_, lean_object* v_val_1267_, uint8_t v___x_1268_, size_t v_sz_1269_, size_t v_i_1270_, lean_object* v_bs_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
uint8_t v___x_1277_; 
v___x_1277_ = lean_usize_dec_lt(v_i_1270_, v_sz_1269_);
if (v___x_1277_ == 0)
{
lean_object* v___x_1278_; 
lean_dec_ref(v_val_1267_);
lean_dec(v_declName_1266_);
v___x_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1278_, 0, v_bs_1271_);
return v___x_1278_;
}
else
{
lean_object* v_v_1279_; lean_object* v_toInductionSubgoal_1280_; lean_object* v_ctorName_1281_; lean_object* v_mvarId_1282_; lean_object* v_fields_1283_; lean_object* v___f_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v_bs_x27_1287_; uint8_t v___y_1289_; 
v_v_1279_ = lean_array_uget_borrowed(v_bs_1271_, v_i_1270_);
v_toInductionSubgoal_1280_ = lean_ctor_get(v_v_1279_, 0);
v_ctorName_1281_ = lean_ctor_get(v_v_1279_, 1);
lean_inc(v_ctorName_1281_);
v_mvarId_1282_ = lean_ctor_get(v_toInductionSubgoal_1280_, 0);
lean_inc(v_mvarId_1282_);
v_fields_1283_ = lean_ctor_get(v_toInductionSubgoal_1280_, 1);
lean_inc_ref(v_fields_1283_);
v___f_1284_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0));
v___x_1285_ = l_Lean_instInhabitedExpr;
v___x_1286_ = lean_unsigned_to_nat(0u);
v_bs_x27_1287_ = lean_array_uset(v_bs_1271_, v_i_1270_, v___x_1286_);
if (lean_obj_tag(v_ctorName_1281_) == 0)
{
v___y_1289_ = v___x_1277_;
goto v___jp_1288_;
}
else
{
lean_dec_ref(v_ctorName_1281_);
if (v___x_1268_ == 0)
{
v___y_1289_ = v___x_1268_;
goto v___jp_1288_;
}
else
{
v___y_1289_ = v___x_1277_;
goto v___jp_1288_;
}
}
v___jp_1288_:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___y_1292_; lean_object* v___x_1293_; 
v___x_1290_ = lean_box(v___y_1289_);
v___x_1291_ = lean_box(v___x_1268_);
lean_inc_ref(v_val_1267_);
lean_inc(v_declName_1266_);
lean_inc(v_mvarId_1282_);
v___y_1292_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed), 13, 8);
lean_closure_set(v___y_1292_, 0, v___x_1290_);
lean_closure_set(v___y_1292_, 1, v_mvarId_1282_);
lean_closure_set(v___y_1292_, 2, v___f_1284_);
lean_closure_set(v___y_1292_, 3, v_declName_1266_);
lean_closure_set(v___y_1292_, 4, v_val_1267_);
lean_closure_set(v___y_1292_, 5, v___x_1285_);
lean_closure_set(v___y_1292_, 6, v_fields_1283_);
lean_closure_set(v___y_1292_, 7, v___x_1291_);
v___x_1293_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1282_, v___y_1292_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; size_t v___x_1295_; size_t v___x_1296_; lean_object* v___x_1297_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1294_);
lean_dec_ref(v___x_1293_);
v___x_1295_ = ((size_t)1ULL);
v___x_1296_ = lean_usize_add(v_i_1270_, v___x_1295_);
v___x_1297_ = lean_array_uset(v_bs_x27_1287_, v_i_1270_, v_a_1294_);
v_i_1270_ = v___x_1296_;
v_bs_1271_ = v___x_1297_;
goto _start;
}
else
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1306_; 
lean_dec_ref(v_bs_x27_1287_);
lean_dec_ref(v_val_1267_);
lean_dec(v_declName_1266_);
v_a_1299_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1301_ = v___x_1293_;
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1293_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_a_1299_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___boxed(lean_object* v_declName_1307_, lean_object* v_val_1308_, lean_object* v___x_1309_, lean_object* v_sz_1310_, lean_object* v_i_1311_, lean_object* v_bs_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
uint8_t v___x_33798__boxed_1318_; size_t v_sz_boxed_1319_; size_t v_i_boxed_1320_; lean_object* v_res_1321_; 
v___x_33798__boxed_1318_ = lean_unbox(v___x_1309_);
v_sz_boxed_1319_ = lean_unbox_usize(v_sz_1310_);
lean_dec(v_sz_1310_);
v_i_boxed_1320_ = lean_unbox_usize(v_i_1311_);
lean_dec(v_i_1311_);
v_res_1321_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(v_declName_1307_, v_val_1308_, v___x_33798__boxed_1318_, v_sz_boxed_1319_, v_i_boxed_1320_, v_bs_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(lean_object* v_declName_1322_, lean_object* v_val_1323_, uint8_t v___x_1324_, size_t v_sz_1325_, size_t v_i_1326_, lean_object* v_bs_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
uint8_t v___x_1333_; 
v___x_1333_ = lean_usize_dec_lt(v_i_1326_, v_sz_1325_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; 
lean_dec_ref(v_val_1323_);
lean_dec(v_declName_1322_);
v___x_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1334_, 0, v_bs_1327_);
return v___x_1334_;
}
else
{
lean_object* v_v_1335_; lean_object* v_toInductionSubgoal_1336_; lean_object* v_ctorName_1337_; lean_object* v_mvarId_1338_; lean_object* v_fields_1339_; lean_object* v___f_1340_; lean_object* v___x_1341_; uint8_t v___x_1342_; lean_object* v___x_1343_; lean_object* v_bs_x27_1344_; uint8_t v___y_1346_; 
v_v_1335_ = lean_array_uget_borrowed(v_bs_1327_, v_i_1326_);
v_toInductionSubgoal_1336_ = lean_ctor_get(v_v_1335_, 0);
v_ctorName_1337_ = lean_ctor_get(v_v_1335_, 1);
lean_inc(v_ctorName_1337_);
v_mvarId_1338_ = lean_ctor_get(v_toInductionSubgoal_1336_, 0);
lean_inc(v_mvarId_1338_);
v_fields_1339_ = lean_ctor_get(v_toInductionSubgoal_1336_, 1);
lean_inc_ref(v_fields_1339_);
v___f_1340_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0));
v___x_1341_ = l_Lean_instInhabitedExpr;
v___x_1342_ = 0;
v___x_1343_ = lean_unsigned_to_nat(0u);
v_bs_x27_1344_ = lean_array_uset(v_bs_1327_, v_i_1326_, v___x_1343_);
if (lean_obj_tag(v_ctorName_1337_) == 0)
{
if (v___x_1324_ == 0)
{
goto v___jp_1364_;
}
else
{
v___y_1346_ = v___x_1324_;
goto v___jp_1345_;
}
}
else
{
lean_dec_ref(v_ctorName_1337_);
goto v___jp_1364_;
}
v___jp_1345_:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___y_1349_; lean_object* v___x_1350_; 
v___x_1347_ = lean_box(v___y_1346_);
v___x_1348_ = lean_box(v___x_1342_);
lean_inc_ref(v_val_1323_);
lean_inc(v_declName_1322_);
lean_inc(v_mvarId_1338_);
v___y_1349_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed), 13, 8);
lean_closure_set(v___y_1349_, 0, v___x_1347_);
lean_closure_set(v___y_1349_, 1, v_mvarId_1338_);
lean_closure_set(v___y_1349_, 2, v___f_1340_);
lean_closure_set(v___y_1349_, 3, v_declName_1322_);
lean_closure_set(v___y_1349_, 4, v_val_1323_);
lean_closure_set(v___y_1349_, 5, v___x_1341_);
lean_closure_set(v___y_1349_, 6, v_fields_1339_);
lean_closure_set(v___y_1349_, 7, v___x_1348_);
v___x_1350_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1338_, v___y_1349_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; size_t v___x_1352_; size_t v___x_1353_; lean_object* v___x_1354_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_a_1351_);
lean_dec_ref(v___x_1350_);
v___x_1352_ = ((size_t)1ULL);
v___x_1353_ = lean_usize_add(v_i_1326_, v___x_1352_);
v___x_1354_ = lean_array_uset(v_bs_x27_1344_, v_i_1326_, v_a_1351_);
v_i_1326_ = v___x_1353_;
v_bs_1327_ = v___x_1354_;
goto _start;
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
lean_dec_ref(v_bs_x27_1344_);
lean_dec_ref(v_val_1323_);
lean_dec(v_declName_1322_);
v_a_1356_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___x_1350_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1350_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
v___jp_1364_:
{
v___y_1346_ = v___x_1342_;
goto v___jp_1345_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4___boxed(lean_object* v_declName_1365_, lean_object* v_val_1366_, lean_object* v___x_1367_, lean_object* v_sz_1368_, lean_object* v_i_1369_, lean_object* v_bs_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
uint8_t v___x_33871__boxed_1376_; size_t v_sz_boxed_1377_; size_t v_i_boxed_1378_; lean_object* v_res_1379_; 
v___x_33871__boxed_1376_ = lean_unbox(v___x_1367_);
v_sz_boxed_1377_ = lean_unbox_usize(v_sz_1368_);
lean_dec(v_sz_1368_);
v_i_boxed_1378_ = lean_unbox_usize(v_i_1369_);
lean_dec(v_i_1369_);
v_res_1379_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(v_declName_1365_, v_val_1366_, v___x_33871__boxed_1376_, v_sz_boxed_1377_, v_i_boxed_1378_, v_bs_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
return v_res_1379_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1383_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__1));
v___x_1384_ = l_Lean_stringToMessageData(v___x_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1(lean_object* v_val_1385_, lean_object* v___x_1386_, lean_object* v_x_1387_, lean_object* v_mvarId_1388_, lean_object* v_declName_1389_, uint8_t v___x_1390_, lean_object* v_____r_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v_majorPos_1422_; lean_object* v_arity_1423_; lean_object* v_insterestingCtors_1424_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___x_1444_; uint8_t v___x_1445_; 
v_majorPos_1422_ = lean_ctor_get(v_val_1385_, 1);
v_arity_1423_ = lean_ctor_get(v_val_1385_, 2);
v_insterestingCtors_1424_ = lean_ctor_get(v_val_1385_, 3);
v___x_1444_ = lean_array_get_size(v_x_1387_);
v___x_1445_ = lean_nat_dec_lt(v___x_1444_, v_arity_1423_);
if (v___x_1445_ == 0)
{
v___y_1426_ = v___y_1392_;
v___y_1427_ = v___y_1393_;
v___y_1428_ = v___y_1394_;
v___y_1429_ = v___y_1395_;
goto v___jp_1425_;
}
else
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
lean_dec(v_declName_1389_);
lean_dec(v_mvarId_1388_);
lean_dec_ref(v_val_1385_);
v___x_1446_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1);
v___x_1447_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1446_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1447_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1447_);
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
v___jp_1397_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1404_ = lean_array_get_borrowed(v___x_1386_, v_x_1387_, v___y_1399_);
lean_dec(v___y_1399_);
v___x_1405_ = l_Lean_Expr_fvarId_x21(v___x_1404_);
v___x_1406_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__0));
v___x_1407_ = 0;
v___x_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1408_, 0, v___y_1398_);
v___x_1409_ = l_Lean_MVarId_cases(v_mvarId_1388_, v___x_1405_, v___x_1406_, v___x_1407_, v___x_1408_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v_a_1410_; size_t v_sz_1411_; size_t v___x_1412_; lean_object* v___x_1413_; 
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_a_1410_);
lean_dec_ref(v___x_1409_);
v_sz_1411_ = lean_array_size(v_a_1410_);
v___x_1412_ = ((size_t)0ULL);
v___x_1413_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(v_declName_1389_, v_val_1385_, v___x_1390_, v_sz_1411_, v___x_1412_, v_a_1410_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
return v___x_1413_;
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
lean_dec(v_declName_1389_);
lean_dec_ref(v_val_1385_);
v_a_1414_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1409_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1409_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
v___jp_1425_:
{
lean_object* v___x_1430_; uint8_t v___x_1431_; 
v___x_1430_ = lean_array_get_borrowed(v___x_1386_, v_x_1387_, v_majorPos_1422_);
v___x_1431_ = l_Lean_Expr_isFVar(v___x_1430_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
lean_dec(v_declName_1389_);
lean_dec(v_mvarId_1388_);
lean_dec_ref(v_val_1385_);
v___x_1432_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2);
lean_inc(v___x_1430_);
v___x_1433_ = l_Lean_indentExpr(v___x_1430_);
v___x_1434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1432_);
lean_ctor_set(v___x_1434_, 1, v___x_1433_);
v___x_1435_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1434_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1435_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1435_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
else
{
lean_inc(v_majorPos_1422_);
lean_inc_ref(v_insterestingCtors_1424_);
v___y_1398_ = v_insterestingCtors_1424_;
v___y_1399_ = v_majorPos_1422_;
v___y_1400_ = v___y_1426_;
v___y_1401_ = v___y_1427_;
v___y_1402_ = v___y_1428_;
v___y_1403_ = v___y_1429_;
goto v___jp_1397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___boxed(lean_object* v_val_1456_, lean_object* v___x_1457_, lean_object* v_x_1458_, lean_object* v_mvarId_1459_, lean_object* v_declName_1460_, lean_object* v___x_1461_, lean_object* v_____r_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
uint8_t v___x_33963__boxed_1468_; lean_object* v_res_1469_; 
v___x_33963__boxed_1468_ = lean_unbox(v___x_1461_);
v_res_1469_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1(v_val_1456_, v___x_1457_, v_x_1458_, v_mvarId_1459_, v_declName_1460_, v___x_33963__boxed_1468_, v_____r_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec_ref(v_x_1458_);
lean_dec_ref(v___x_1457_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(lean_object* v_cls_1472_, lean_object* v_msg_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v_ref_1479_; lean_object* v___x_1480_; lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1526_; 
v_ref_1479_ = lean_ctor_get(v___y_1476_, 5);
v___x_1480_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msg_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1483_ = v___x_1480_;
v_isShared_1484_ = v_isSharedCheck_1526_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1480_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1526_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1485_; lean_object* v_traceState_1486_; lean_object* v_env_1487_; lean_object* v_nextMacroScope_1488_; lean_object* v_ngen_1489_; lean_object* v_auxDeclNGen_1490_; lean_object* v_cache_1491_; lean_object* v_messages_1492_; lean_object* v_infoState_1493_; lean_object* v_snapshotTasks_1494_; lean_object* v_newDecls_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1525_; 
v___x_1485_ = lean_st_ref_take(v___y_1477_);
v_traceState_1486_ = lean_ctor_get(v___x_1485_, 4);
v_env_1487_ = lean_ctor_get(v___x_1485_, 0);
v_nextMacroScope_1488_ = lean_ctor_get(v___x_1485_, 1);
v_ngen_1489_ = lean_ctor_get(v___x_1485_, 2);
v_auxDeclNGen_1490_ = lean_ctor_get(v___x_1485_, 3);
v_cache_1491_ = lean_ctor_get(v___x_1485_, 5);
v_messages_1492_ = lean_ctor_get(v___x_1485_, 6);
v_infoState_1493_ = lean_ctor_get(v___x_1485_, 7);
v_snapshotTasks_1494_ = lean_ctor_get(v___x_1485_, 8);
v_newDecls_1495_ = lean_ctor_get(v___x_1485_, 9);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1497_ = v___x_1485_;
v_isShared_1498_ = v_isSharedCheck_1525_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_newDecls_1495_);
lean_inc(v_snapshotTasks_1494_);
lean_inc(v_infoState_1493_);
lean_inc(v_messages_1492_);
lean_inc(v_cache_1491_);
lean_inc(v_traceState_1486_);
lean_inc(v_auxDeclNGen_1490_);
lean_inc(v_ngen_1489_);
lean_inc(v_nextMacroScope_1488_);
lean_inc(v_env_1487_);
lean_dec(v___x_1485_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1525_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
uint64_t v_tid_1499_; lean_object* v_traces_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1524_; 
v_tid_1499_ = lean_ctor_get_uint64(v_traceState_1486_, sizeof(void*)*1);
v_traces_1500_ = lean_ctor_get(v_traceState_1486_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v_traceState_1486_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1502_ = v_traceState_1486_;
v_isShared_1503_ = v_isSharedCheck_1524_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_traces_1500_);
lean_dec(v_traceState_1486_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1524_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1504_; double v___x_1505_; uint8_t v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1514_; 
v___x_1504_ = lean_box(0);
v___x_1505_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2);
v___x_1506_ = 0;
v___x_1507_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__6));
v___x_1508_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1508_, 0, v_cls_1472_);
lean_ctor_set(v___x_1508_, 1, v___x_1504_);
lean_ctor_set(v___x_1508_, 2, v___x_1507_);
lean_ctor_set_float(v___x_1508_, sizeof(void*)*3, v___x_1505_);
lean_ctor_set_float(v___x_1508_, sizeof(void*)*3 + 8, v___x_1505_);
lean_ctor_set_uint8(v___x_1508_, sizeof(void*)*3 + 16, v___x_1506_);
v___x_1509_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___closed__0));
v___x_1510_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1508_);
lean_ctor_set(v___x_1510_, 1, v_a_1481_);
lean_ctor_set(v___x_1510_, 2, v___x_1509_);
lean_inc(v_ref_1479_);
v___x_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1511_, 0, v_ref_1479_);
lean_ctor_set(v___x_1511_, 1, v___x_1510_);
v___x_1512_ = l_Lean_PersistentArray_push___redArg(v_traces_1500_, v___x_1511_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 0, v___x_1512_);
v___x_1514_ = v___x_1502_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1512_);
lean_ctor_set_uint64(v_reuseFailAlloc_1523_, sizeof(void*)*1, v_tid_1499_);
v___x_1514_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1516_; 
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 4, v___x_1514_);
v___x_1516_ = v___x_1497_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_env_1487_);
lean_ctor_set(v_reuseFailAlloc_1522_, 1, v_nextMacroScope_1488_);
lean_ctor_set(v_reuseFailAlloc_1522_, 2, v_ngen_1489_);
lean_ctor_set(v_reuseFailAlloc_1522_, 3, v_auxDeclNGen_1490_);
lean_ctor_set(v_reuseFailAlloc_1522_, 4, v___x_1514_);
lean_ctor_set(v_reuseFailAlloc_1522_, 5, v_cache_1491_);
lean_ctor_set(v_reuseFailAlloc_1522_, 6, v_messages_1492_);
lean_ctor_set(v_reuseFailAlloc_1522_, 7, v_infoState_1493_);
lean_ctor_set(v_reuseFailAlloc_1522_, 8, v_snapshotTasks_1494_);
lean_ctor_set(v_reuseFailAlloc_1522_, 9, v_newDecls_1495_);
v___x_1516_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1520_; 
v___x_1517_ = lean_st_ref_set(v___y_1477_, v___x_1516_);
v___x_1518_ = lean_box(0);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v___x_1518_);
v___x_1520_ = v___x_1483_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1518_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___boxed(lean_object* v_cls_1527_, lean_object* v_msg_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v_cls_1527_, v_msg_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__2(lean_object* v_val_1535_, lean_object* v___x_1536_, lean_object* v_x_1537_, lean_object* v_mvarId_1538_, uint8_t v___x_1539_, lean_object* v_declName_1540_, lean_object* v_____r_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v_majorPos_1571_; lean_object* v_arity_1572_; lean_object* v_insterestingCtors_1573_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___x_1593_; uint8_t v___x_1594_; 
v_majorPos_1571_ = lean_ctor_get(v_val_1535_, 1);
v_arity_1572_ = lean_ctor_get(v_val_1535_, 2);
v_insterestingCtors_1573_ = lean_ctor_get(v_val_1535_, 3);
v___x_1593_ = lean_array_get_size(v_x_1537_);
v___x_1594_ = lean_nat_dec_lt(v___x_1593_, v_arity_1572_);
if (v___x_1594_ == 0)
{
v___y_1575_ = v___y_1542_;
v___y_1576_ = v___y_1543_;
v___y_1577_ = v___y_1544_;
v___y_1578_ = v___y_1545_;
goto v___jp_1574_;
}
else
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
lean_dec(v_declName_1540_);
lean_dec(v_mvarId_1538_);
lean_dec_ref(v_val_1535_);
v___x_1595_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1);
v___x_1596_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1595_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v___x_1596_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1596_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1597_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
v___jp_1547_:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1554_ = lean_array_get_borrowed(v___x_1536_, v_x_1537_, v___y_1548_);
lean_dec(v___y_1548_);
v___x_1555_ = l_Lean_Expr_fvarId_x21(v___x_1554_);
v___x_1556_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__0));
v___x_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1557_, 0, v___y_1549_);
v___x_1558_ = l_Lean_MVarId_cases(v_mvarId_1538_, v___x_1555_, v___x_1556_, v___x_1539_, v___x_1557_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; size_t v_sz_1560_; size_t v___x_1561_; lean_object* v___x_1562_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_a_1559_);
lean_dec_ref(v___x_1558_);
v_sz_1560_ = lean_array_size(v_a_1559_);
v___x_1561_ = ((size_t)0ULL);
v___x_1562_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(v_declName_1540_, v_val_1535_, v___x_1539_, v_sz_1560_, v___x_1561_, v_a_1559_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
return v___x_1562_;
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_dec(v_declName_1540_);
lean_dec_ref(v_val_1535_);
v_a_1563_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1558_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1558_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
v___jp_1574_:
{
lean_object* v___x_1579_; uint8_t v___x_1580_; 
v___x_1579_ = lean_array_get_borrowed(v___x_1536_, v_x_1537_, v_majorPos_1571_);
v___x_1580_ = l_Lean_Expr_isFVar(v___x_1579_);
if (v___x_1580_ == 0)
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
lean_dec(v_declName_1540_);
lean_dec(v_mvarId_1538_);
lean_dec_ref(v_val_1535_);
v___x_1581_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2);
lean_inc(v___x_1579_);
v___x_1582_ = l_Lean_indentExpr(v___x_1579_);
v___x_1583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1581_);
lean_ctor_set(v___x_1583_, 1, v___x_1582_);
v___x_1584_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1583_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1584_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1584_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
else
{
lean_inc_ref(v_insterestingCtors_1573_);
lean_inc(v_majorPos_1571_);
v___y_1548_ = v_majorPos_1571_;
v___y_1549_ = v_insterestingCtors_1573_;
v___y_1550_ = v___y_1575_;
v___y_1551_ = v___y_1576_;
v___y_1552_ = v___y_1577_;
v___y_1553_ = v___y_1578_;
goto v___jp_1547_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__2___boxed(lean_object* v_val_1605_, lean_object* v___x_1606_, lean_object* v_x_1607_, lean_object* v_mvarId_1608_, lean_object* v___x_1609_, lean_object* v_declName_1610_, lean_object* v_____r_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
uint8_t v___x_34215__boxed_1617_; lean_object* v_res_1618_; 
v___x_34215__boxed_1617_ = lean_unbox(v___x_1609_);
v_res_1618_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__2(v_val_1605_, v___x_1606_, v_x_1607_, v_mvarId_1608_, v___x_34215__boxed_1617_, v_declName_1610_, v_____r_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
lean_dec_ref(v_x_1607_);
lean_dec_ref(v___x_1606_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__3(lean_object* v_val_1619_, lean_object* v___x_1620_, lean_object* v_x_1621_, lean_object* v_mvarId_1622_, uint8_t v___x_1623_, lean_object* v_declName_1624_, lean_object* v_____r_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v_majorPos_1655_; lean_object* v_arity_1656_; lean_object* v_insterestingCtors_1657_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___x_1677_; uint8_t v___x_1678_; 
v_majorPos_1655_ = lean_ctor_get(v_val_1619_, 1);
v_arity_1656_ = lean_ctor_get(v_val_1619_, 2);
v_insterestingCtors_1657_ = lean_ctor_get(v_val_1619_, 3);
v___x_1677_ = lean_array_get_size(v_x_1621_);
v___x_1678_ = lean_nat_dec_lt(v___x_1677_, v_arity_1656_);
if (v___x_1678_ == 0)
{
v___y_1659_ = v___y_1626_;
v___y_1660_ = v___y_1627_;
v___y_1661_ = v___y_1628_;
v___y_1662_ = v___y_1629_;
goto v___jp_1658_;
}
else
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
lean_dec(v_declName_1624_);
lean_dec(v_mvarId_1622_);
lean_dec_ref(v_val_1619_);
v___x_1679_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1);
v___x_1680_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1679_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1680_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1680_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
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
v___jp_1631_:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1638_ = lean_array_get_borrowed(v___x_1620_, v_x_1621_, v___y_1633_);
lean_dec(v___y_1633_);
v___x_1639_ = l_Lean_Expr_fvarId_x21(v___x_1638_);
v___x_1640_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__0));
v___x_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1641_, 0, v___y_1632_);
v___x_1642_ = l_Lean_MVarId_cases(v_mvarId_1622_, v___x_1639_, v___x_1640_, v___x_1623_, v___x_1641_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; size_t v_sz_1644_; size_t v___x_1645_; lean_object* v___x_1646_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
lean_inc(v_a_1643_);
lean_dec_ref(v___x_1642_);
v_sz_1644_ = lean_array_size(v_a_1643_);
v___x_1645_ = ((size_t)0ULL);
v___x_1646_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(v_declName_1624_, v_val_1619_, v___x_1623_, v_sz_1644_, v___x_1645_, v_a_1643_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
return v___x_1646_;
}
else
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1654_; 
lean_dec(v_declName_1624_);
lean_dec_ref(v_val_1619_);
v_a_1647_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1649_ = v___x_1642_;
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1642_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1652_; 
if (v_isShared_1650_ == 0)
{
v___x_1652_ = v___x_1649_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_a_1647_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
v___jp_1658_:
{
lean_object* v___x_1663_; uint8_t v___x_1664_; 
v___x_1663_ = lean_array_get_borrowed(v___x_1620_, v_x_1621_, v_majorPos_1655_);
v___x_1664_ = l_Lean_Expr_isFVar(v___x_1663_);
if (v___x_1664_ == 0)
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
lean_dec(v_declName_1624_);
lean_dec(v_mvarId_1622_);
lean_dec_ref(v_val_1619_);
v___x_1665_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2);
lean_inc(v___x_1663_);
v___x_1666_ = l_Lean_indentExpr(v___x_1663_);
v___x_1667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1665_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
v___x_1668_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1667_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___x_1668_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1668_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
else
{
lean_inc(v_majorPos_1655_);
lean_inc_ref(v_insterestingCtors_1657_);
v___y_1632_ = v_insterestingCtors_1657_;
v___y_1633_ = v_majorPos_1655_;
v___y_1634_ = v___y_1659_;
v___y_1635_ = v___y_1660_;
v___y_1636_ = v___y_1661_;
v___y_1637_ = v___y_1662_;
goto v___jp_1631_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__3___boxed(lean_object* v_val_1689_, lean_object* v___x_1690_, lean_object* v_x_1691_, lean_object* v_mvarId_1692_, lean_object* v___x_1693_, lean_object* v_declName_1694_, lean_object* v_____r_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
uint8_t v___x_34369__boxed_1701_; lean_object* v_res_1702_; 
v___x_34369__boxed_1701_ = lean_unbox(v___x_1693_);
v_res_1702_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__3(v_val_1689_, v___x_1690_, v_x_1691_, v_mvarId_1692_, v___x_34369__boxed_1701_, v_declName_1694_, v_____r_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec_ref(v_x_1691_);
lean_dec_ref(v___x_1690_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__0(lean_object* v___x_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v_options_1709_; uint8_t v_hasTrace_1710_; 
v_options_1709_ = lean_ctor_get(v___y_1706_, 2);
v_hasTrace_1710_ = lean_ctor_get_uint8(v_options_1709_, sizeof(void*)*1);
if (v_hasTrace_1710_ == 0)
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
lean_dec(v___x_1703_);
v___x_1711_ = lean_box(v_hasTrace_1710_);
v___x_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1711_);
return v___x_1712_;
}
else
{
lean_object* v_inheritedTraceOptions_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; uint8_t v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v_inheritedTraceOptions_1713_ = lean_ctor_get(v___y_1706_, 13);
v___x_1714_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__8));
v___x_1715_ = l_Lean_Name_append(v___x_1714_, v___x_1703_);
v___x_1716_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1713_, v_options_1709_, v___x_1715_);
lean_dec(v___x_1715_);
v___x_1717_ = lean_box(v___x_1716_);
v___x_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1717_);
return v___x_1718_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__0___boxed(lean_object* v___x_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__0(v___x_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
return v_res_1725_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1(void){
_start:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1727_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__0));
v___x_1728_ = l_Lean_stringToMessageData(v___x_1727_);
return v___x_1728_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1730_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__2));
v___x_1731_ = l_Lean_stringToMessageData(v___x_1730_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5(lean_object* v_mvarId_1732_, lean_object* v_x_1733_, lean_object* v_x_1734_, lean_object* v_x_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
if (lean_obj_tag(v_x_1733_) == 5)
{
lean_object* v_fn_1741_; lean_object* v_arg_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v_fn_1741_ = lean_ctor_get(v_x_1733_, 0);
lean_inc_ref(v_fn_1741_);
v_arg_1742_ = lean_ctor_get(v_x_1733_, 1);
lean_inc_ref(v_arg_1742_);
lean_dec_ref(v_x_1733_);
v___x_1743_ = lean_array_set(v_x_1734_, v_x_1735_, v_arg_1742_);
v___x_1744_ = lean_unsigned_to_nat(1u);
v___x_1745_ = lean_nat_sub(v_x_1735_, v___x_1744_);
lean_dec(v_x_1735_);
v_x_1733_ = v_fn_1741_;
v_x_1734_ = v___x_1743_;
v_x_1735_ = v___x_1745_;
goto _start;
}
else
{
lean_dec(v_x_1735_);
if (lean_obj_tag(v_x_1733_) == 4)
{
lean_object* v_declName_1747_; lean_object* v___x_1748_; 
v_declName_1747_ = lean_ctor_get(v_x_1733_, 0);
lean_inc_n(v_declName_1747_, 2);
lean_dec_ref(v_x_1733_);
v___x_1748_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_declName_1747_, v___y_1739_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_a_1749_);
lean_dec_ref(v___x_1748_);
if (lean_obj_tag(v_a_1749_) == 1)
{
lean_object* v_options_1750_; lean_object* v_val_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_2061_; 
v_options_1750_ = lean_ctor_get(v___y_1738_, 2);
v_val_1751_ = lean_ctor_get(v_a_1749_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v_a_1749_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_1753_ = v_a_1749_;
v_isShared_1754_ = v_isSharedCheck_2061_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_val_1751_);
lean_dec(v_a_1749_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_2061_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v_inheritedTraceOptions_1755_; uint8_t v_hasTrace_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___y_1760_; lean_object* v___y_1761_; uint8_t v___y_1762_; lean_object* v___y_1795_; lean_object* v_a_1796_; lean_object* v___y_1800_; lean_object* v___y_1803_; lean_object* v___y_1804_; uint8_t v___y_1805_; lean_object* v___y_1838_; lean_object* v_a_1839_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; 
v_inheritedTraceOptions_1755_ = lean_ctor_get(v___y_1738_, 13);
v_hasTrace_1756_ = lean_ctor_get_uint8(v_options_1750_, sizeof(void*)*1);
v___x_1757_ = l_Lean_instInhabitedExpr;
v___x_1758_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5));
if (v_hasTrace_1756_ == 0)
{
lean_object* v_majorPos_1869_; lean_object* v_arity_1870_; lean_object* v_insterestingCtors_1871_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___x_1891_; uint8_t v___x_1892_; 
v_majorPos_1869_ = lean_ctor_get(v_val_1751_, 1);
v_arity_1870_ = lean_ctor_get(v_val_1751_, 2);
v_insterestingCtors_1871_ = lean_ctor_get(v_val_1751_, 3);
v___x_1891_ = lean_array_get_size(v_x_1734_);
v___x_1892_ = lean_nat_dec_lt(v___x_1891_, v_arity_1870_);
if (v___x_1892_ == 0)
{
v___y_1873_ = v___y_1736_;
v___y_1874_ = v___y_1737_;
v___y_1875_ = v___y_1738_;
v___y_1876_ = v___y_1739_;
goto v___jp_1872_;
}
else
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
lean_del_object(v___x_1753_);
lean_dec(v_val_1751_);
lean_dec(v_declName_1747_);
lean_dec_ref(v_x_1734_);
lean_dec(v_mvarId_1732_);
v___x_1893_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1);
v___x_1894_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1893_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v___x_1894_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1894_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
lean_inc(v_a_1895_);
if (v_isShared_1898_ == 0)
{
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1895_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
v___y_1838_ = v___x_1900_;
v_a_1839_ = v_a_1895_;
goto v___jp_1837_;
}
}
}
v___jp_1872_:
{
lean_object* v___x_1877_; uint8_t v___x_1878_; 
v___x_1877_ = lean_array_get_borrowed(v___x_1757_, v_x_1734_, v_majorPos_1869_);
v___x_1878_ = l_Lean_Expr_isFVar(v___x_1877_);
if (v___x_1878_ == 0)
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
lean_inc(v___x_1877_);
lean_del_object(v___x_1753_);
lean_dec(v_val_1751_);
lean_dec(v_declName_1747_);
lean_dec_ref(v_x_1734_);
lean_dec(v_mvarId_1732_);
v___x_1879_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__2);
v___x_1880_ = l_Lean_indentExpr(v___x_1877_);
v___x_1881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1879_);
lean_ctor_set(v___x_1881_, 1, v___x_1880_);
v___x_1882_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1881_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___x_1882_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1882_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
lean_inc(v_a_1883_);
if (v_isShared_1886_ == 0)
{
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1883_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
v___y_1838_ = v___x_1888_;
v_a_1839_ = v_a_1883_;
goto v___jp_1837_;
}
}
}
else
{
lean_inc(v_majorPos_1869_);
lean_inc_ref(v_insterestingCtors_1871_);
v___y_1843_ = v_insterestingCtors_1871_;
v___y_1844_ = v_majorPos_1869_;
v___y_1845_ = v___y_1873_;
v___y_1846_ = v___y_1874_;
v___y_1847_ = v___y_1875_;
v___y_1848_ = v___y_1876_;
goto v___jp_1842_;
}
}
}
else
{
lean_object* v___f_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; uint8_t v___x_1906_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v_a_1910_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v_a_1925_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; uint8_t v___y_1931_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v_a_1944_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v_a_1963_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v_a_1975_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; uint8_t v___y_1981_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v_a_1994_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; 
lean_del_object(v___x_1753_);
v___f_1903_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1));
v___x_1904_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__6));
v___x_1905_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9);
v___x_1906_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1755_, v_options_1750_, v___x_1905_);
if (v___x_1906_ == 0)
{
lean_object* v___x_2043_; uint8_t v___x_2044_; 
v___x_2043_ = l_Lean_trace_profiler;
v___x_2044_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_options_1750_, v___x_2043_);
if (v___x_2044_ == 0)
{
if (v___x_1906_ == 0)
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2045_ = lean_box(0);
v___x_2046_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__3(v_val_1751_, v___x_1757_, v_x_1734_, v_mvarId_1732_, v___x_2044_, v_declName_1747_, v___x_2045_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
lean_dec_ref(v_x_1734_);
v___y_1800_ = v___x_2046_;
goto v___jp_1799_;
}
else
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2047_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3);
lean_inc(v_mvarId_1732_);
v___x_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2048_, 0, v_mvarId_1732_);
v___x_2049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2047_);
lean_ctor_set(v___x_2049_, 1, v___x_2048_);
v___x_2050_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1758_, v___x_2049_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; lean_object* v___x_2052_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2051_);
lean_dec_ref(v___x_2050_);
v___x_2052_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__3(v_val_1751_, v___x_1757_, v_x_1734_, v_mvarId_1732_, v___x_2044_, v_declName_1747_, v_a_2051_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
lean_dec_ref(v_x_1734_);
v___y_1800_ = v___x_2052_;
goto v___jp_1799_;
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec(v_val_1751_);
lean_dec(v_declName_1747_);
lean_dec_ref(v_x_1734_);
lean_dec(v_mvarId_1732_);
v_a_2053_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2050_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2050_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
lean_inc(v_a_2053_);
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
v___y_1795_ = v___x_2058_;
v_a_1796_ = v_a_2053_;
goto v___jp_1794_;
}
}
}
}
}
else
{
goto v___jp_2010_;
}
}
else
{
goto v___jp_2010_;
}
v___jp_1907_:
{
lean_object* v___x_1911_; double v___x_1912_; double v___x_1913_; double v___x_1914_; double v___x_1915_; double v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1911_ = lean_io_mono_nanos_now();
v___x_1912_ = lean_float_of_nat(v___y_1908_);
v___x_1913_ = lean_float_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10);
v___x_1914_ = lean_float_div(v___x_1912_, v___x_1913_);
v___x_1915_ = lean_float_of_nat(v___x_1911_);
v___x_1916_ = lean_float_div(v___x_1915_, v___x_1913_);
v___x_1917_ = lean_box_float(v___x_1914_);
v___x_1918_ = lean_box_float(v___x_1916_);
v___x_1919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1917_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v___x_1920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1920_, 0, v_a_1910_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_1758_, v_hasTrace_1756_, v___x_1904_, v_options_1750_, v___x_1906_, v___y_1909_, v___f_1903_, v___x_1920_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
return v___x_1921_;
}
v___jp_1922_:
{
lean_object* v___x_1926_; 
v___x_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1926_, 0, v_a_1925_);
v___y_1908_ = v___y_1923_;
v___y_1909_ = v___y_1924_;
v_a_1910_ = v___x_1926_;
goto v___jp_1907_;
}
v___jp_1927_:
{
if (v___y_1931_ == 0)
{
lean_object* v___x_1932_; lean_object* v_a_1933_; uint8_t v___x_1934_; 
v___x_1932_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__0(v___x_1758_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref(v___x_1932_);
v___x_1934_ = lean_unbox(v_a_1933_);
lean_dec(v_a_1933_);
if (v___x_1934_ == 0)
{
v___y_1923_ = v___y_1929_;
v___y_1924_ = v___y_1930_;
v_a_1925_ = v___y_1928_;
goto v___jp_1922_;
}
else
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1935_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1);
lean_inc_ref(v___y_1928_);
v___x_1936_ = l_Lean_Exception_toMessageData(v___y_1928_);
v___x_1937_ = l_Lean_indentD(v___x_1936_);
v___x_1938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1935_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1758_, v___x_1938_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_dec_ref(v___x_1939_);
v___y_1923_ = v___y_1929_;
v___y_1924_ = v___y_1930_;
v_a_1925_ = v___y_1928_;
goto v___jp_1922_;
}
else
{
lean_object* v_a_1940_; 
lean_dec_ref(v___y_1928_);
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_a_1940_);
lean_dec_ref(v___x_1939_);
v___y_1923_ = v___y_1929_;
v___y_1924_ = v___y_1930_;
v_a_1925_ = v_a_1940_;
goto v___jp_1922_;
}
}
}
else
{
v___y_1923_ = v___y_1929_;
v___y_1924_ = v___y_1930_;
v_a_1925_ = v___y_1928_;
goto v___jp_1922_;
}
}
v___jp_1941_:
{
uint8_t v___x_1945_; 
v___x_1945_ = l_Lean_Exception_isInterrupt(v_a_1944_);
if (v___x_1945_ == 0)
{
uint8_t v___x_1946_; 
lean_inc_ref(v_a_1944_);
v___x_1946_ = l_Lean_Exception_isRuntime(v_a_1944_);
v___y_1928_ = v_a_1944_;
v___y_1929_ = v___y_1942_;
v___y_1930_ = v___y_1943_;
v___y_1931_ = v___x_1946_;
goto v___jp_1927_;
}
else
{
v___y_1928_ = v_a_1944_;
v___y_1929_ = v___y_1942_;
v___y_1930_ = v___y_1943_;
v___y_1931_ = v___x_1945_;
goto v___jp_1927_;
}
}
v___jp_1947_:
{
if (lean_obj_tag(v___y_1950_) == 0)
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1958_; 
v_a_1951_ = lean_ctor_get(v___y_1950_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___y_1950_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1953_ = v___y_1950_;
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___y_1950_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
lean_ctor_set_tag(v___x_1953_, 1);
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1951_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
v___y_1908_ = v___y_1948_;
v___y_1909_ = v___y_1949_;
v_a_1910_ = v___x_1956_;
goto v___jp_1907_;
}
}
}
else
{
lean_object* v_a_1959_; 
v_a_1959_ = lean_ctor_get(v___y_1950_, 0);
lean_inc(v_a_1959_);
lean_dec_ref(v___y_1950_);
v___y_1942_ = v___y_1948_;
v___y_1943_ = v___y_1949_;
v_a_1944_ = v_a_1959_;
goto v___jp_1941_;
}
}
v___jp_1960_:
{
lean_object* v___x_1964_; double v___x_1965_; double v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1964_ = lean_io_get_num_heartbeats();
v___x_1965_ = lean_float_of_nat(v___y_1962_);
v___x_1966_ = lean_float_of_nat(v___x_1964_);
v___x_1967_ = lean_box_float(v___x_1965_);
v___x_1968_ = lean_box_float(v___x_1966_);
v___x_1969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1967_);
lean_ctor_set(v___x_1969_, 1, v___x_1968_);
v___x_1970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1970_, 0, v_a_1963_);
lean_ctor_set(v___x_1970_, 1, v___x_1969_);
v___x_1971_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_1758_, v_hasTrace_1756_, v___x_1904_, v_options_1750_, v___x_1906_, v___y_1961_, v___f_1903_, v___x_1970_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
return v___x_1971_;
}
v___jp_1972_:
{
lean_object* v___x_1976_; 
v___x_1976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1976_, 0, v_a_1975_);
v___y_1961_ = v___y_1973_;
v___y_1962_ = v___y_1974_;
v_a_1963_ = v___x_1976_;
goto v___jp_1960_;
}
v___jp_1977_:
{
if (v___y_1981_ == 0)
{
lean_object* v___x_1982_; lean_object* v_a_1983_; uint8_t v___x_1984_; 
v___x_1982_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__0(v___x_1758_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
lean_inc(v_a_1983_);
lean_dec_ref(v___x_1982_);
v___x_1984_ = lean_unbox(v_a_1983_);
lean_dec(v_a_1983_);
if (v___x_1984_ == 0)
{
v___y_1973_ = v___y_1979_;
v___y_1974_ = v___y_1980_;
v_a_1975_ = v___y_1978_;
goto v___jp_1972_;
}
else
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1985_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1);
lean_inc_ref(v___y_1978_);
v___x_1986_ = l_Lean_Exception_toMessageData(v___y_1978_);
v___x_1987_ = l_Lean_indentD(v___x_1986_);
v___x_1988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1985_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
v___x_1989_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1758_, v___x_1988_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_dec_ref(v___x_1989_);
v___y_1973_ = v___y_1979_;
v___y_1974_ = v___y_1980_;
v_a_1975_ = v___y_1978_;
goto v___jp_1972_;
}
else
{
lean_object* v_a_1990_; 
lean_dec_ref(v___y_1978_);
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
lean_inc(v_a_1990_);
lean_dec_ref(v___x_1989_);
v___y_1973_ = v___y_1979_;
v___y_1974_ = v___y_1980_;
v_a_1975_ = v_a_1990_;
goto v___jp_1972_;
}
}
}
else
{
v___y_1973_ = v___y_1979_;
v___y_1974_ = v___y_1980_;
v_a_1975_ = v___y_1978_;
goto v___jp_1972_;
}
}
v___jp_1991_:
{
uint8_t v___x_1995_; 
v___x_1995_ = l_Lean_Exception_isInterrupt(v_a_1994_);
if (v___x_1995_ == 0)
{
uint8_t v___x_1996_; 
lean_inc_ref(v_a_1994_);
v___x_1996_ = l_Lean_Exception_isRuntime(v_a_1994_);
v___y_1978_ = v_a_1994_;
v___y_1979_ = v___y_1992_;
v___y_1980_ = v___y_1993_;
v___y_1981_ = v___x_1996_;
goto v___jp_1977_;
}
else
{
v___y_1978_ = v_a_1994_;
v___y_1979_ = v___y_1992_;
v___y_1980_ = v___y_1993_;
v___y_1981_ = v___x_1995_;
goto v___jp_1977_;
}
}
v___jp_1997_:
{
if (lean_obj_tag(v___y_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
v_a_2001_ = lean_ctor_get(v___y_2000_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___y_2000_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___y_2000_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___y_2000_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
lean_ctor_set_tag(v___x_2003_, 1);
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
v___y_1961_ = v___y_1998_;
v___y_1962_ = v___y_1999_;
v_a_1963_ = v___x_2006_;
goto v___jp_1960_;
}
}
}
else
{
lean_object* v_a_2009_; 
v_a_2009_ = lean_ctor_get(v___y_2000_, 0);
lean_inc(v_a_2009_);
lean_dec_ref(v___y_2000_);
v___y_1992_ = v___y_1998_;
v___y_1993_ = v___y_1999_;
v_a_1994_ = v_a_2009_;
goto v___jp_1991_;
}
}
v___jp_2010_:
{
lean_object* v___x_2011_; lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2042_; 
v___x_2011_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___y_1739_);
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2014_ = v___x_2011_;
v_isShared_2015_ = v_isSharedCheck_2042_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_2011_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2042_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2016_; uint8_t v___x_2017_; 
v___x_2016_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2017_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_options_1750_, v___x_2016_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; 
v___x_2018_ = lean_io_mono_nanos_now();
if (v___x_1906_ == 0)
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
lean_del_object(v___x_2014_);
v___x_2019_ = lean_box(0);
v___x_2020_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__2(v_val_1751_, v___x_1757_, v_x_1734_, v_mvarId_1732_, v___x_2017_, v_declName_1747_, v___x_2019_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
lean_dec_ref(v_x_1734_);
v___y_1948_ = v___x_2018_;
v___y_1949_ = v_a_2012_;
v___y_1950_ = v___x_2020_;
goto v___jp_1947_;
}
else
{
lean_object* v___x_2021_; lean_object* v___x_2023_; 
v___x_2021_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3);
lean_inc(v_mvarId_1732_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set_tag(v___x_2014_, 1);
lean_ctor_set(v___x_2014_, 0, v_mvarId_1732_);
v___x_2023_ = v___x_2014_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_mvarId_1732_);
v___x_2023_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2021_);
lean_ctor_set(v___x_2024_, 1, v___x_2023_);
v___x_2025_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1758_, v___x_2024_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; lean_object* v___x_2027_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_a_2026_);
lean_dec_ref(v___x_2025_);
v___x_2027_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__2(v_val_1751_, v___x_1757_, v_x_1734_, v_mvarId_1732_, v___x_2017_, v_declName_1747_, v_a_2026_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
lean_dec_ref(v_x_1734_);
v___y_1948_ = v___x_2018_;
v___y_1949_ = v_a_2012_;
v___y_1950_ = v___x_2027_;
goto v___jp_1947_;
}
else
{
lean_object* v_a_2028_; 
lean_dec(v_val_1751_);
lean_dec(v_declName_1747_);
lean_dec_ref(v_x_1734_);
lean_dec(v_mvarId_1732_);
v_a_2028_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_a_2028_);
lean_dec_ref(v___x_2025_);
v___y_1942_ = v___x_2018_;
v___y_1943_ = v_a_2012_;
v_a_1944_ = v_a_2028_;
goto v___jp_1941_;
}
}
}
}
else
{
lean_object* v___x_2030_; 
v___x_2030_ = lean_io_get_num_heartbeats();
if (v___x_1906_ == 0)
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
lean_del_object(v___x_2014_);
v___x_2031_ = lean_box(0);
v___x_2032_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1(v_val_1751_, v___x_1757_, v_x_1734_, v_mvarId_1732_, v_declName_1747_, v___x_2017_, v___x_2031_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
lean_dec_ref(v_x_1734_);
v___y_1998_ = v_a_2012_;
v___y_1999_ = v___x_2030_;
v___y_2000_ = v___x_2032_;
goto v___jp_1997_;
}
else
{
lean_object* v___x_2033_; lean_object* v___x_2035_; 
v___x_2033_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__3);
lean_inc(v_mvarId_1732_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set_tag(v___x_2014_, 1);
lean_ctor_set(v___x_2014_, 0, v_mvarId_1732_);
v___x_2035_ = v___x_2014_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_mvarId_1732_);
v___x_2035_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2033_);
lean_ctor_set(v___x_2036_, 1, v___x_2035_);
v___x_2037_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1758_, v___x_2036_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; lean_object* v___x_2039_; 
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_a_2038_);
lean_dec_ref(v___x_2037_);
v___x_2039_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1(v_val_1751_, v___x_1757_, v_x_1734_, v_mvarId_1732_, v_declName_1747_, v___x_2017_, v_a_2038_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
lean_dec_ref(v_x_1734_);
v___y_1998_ = v_a_2012_;
v___y_1999_ = v___x_2030_;
v___y_2000_ = v___x_2039_;
goto v___jp_1997_;
}
else
{
lean_object* v_a_2040_; 
lean_dec(v_val_1751_);
lean_dec(v_declName_1747_);
lean_dec_ref(v_x_1734_);
lean_dec(v_mvarId_1732_);
v_a_2040_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_a_2040_);
lean_dec_ref(v___x_2037_);
v___y_1992_ = v_a_2012_;
v___y_1993_ = v___x_2030_;
v_a_1994_ = v_a_2040_;
goto v___jp_1991_;
}
}
}
}
}
}
}
v___jp_1759_:
{
if (v___y_1762_ == 0)
{
lean_object* v___x_1763_; lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1793_; 
lean_dec_ref(v___y_1761_);
v___x_1763_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__0(v___x_1758_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1766_ = v___x_1763_;
v_isShared_1767_ = v_isSharedCheck_1793_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1763_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1793_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
uint8_t v___x_1768_; 
v___x_1768_ = lean_unbox(v_a_1764_);
lean_dec(v_a_1764_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1770_; 
if (v_isShared_1767_ == 0)
{
lean_ctor_set_tag(v___x_1766_, 1);
lean_ctor_set(v___x_1766_, 0, v___y_1760_);
v___x_1770_ = v___x_1766_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___y_1760_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
else
{
lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
lean_del_object(v___x_1766_);
v___x_1772_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1);
lean_inc_ref(v___y_1760_);
v___x_1773_ = l_Lean_Exception_toMessageData(v___y_1760_);
v___x_1774_ = l_Lean_indentD(v___x_1773_);
v___x_1775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1772_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
v___x_1776_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1758_, v___x_1775_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1783_ == 0)
{
lean_object* v_unused_1784_; 
v_unused_1784_ = lean_ctor_get(v___x_1776_, 0);
lean_dec(v_unused_1784_);
v___x_1778_ = v___x_1776_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_dec(v___x_1776_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
lean_ctor_set_tag(v___x_1778_, 1);
lean_ctor_set(v___x_1778_, 0, v___y_1760_);
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___y_1760_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
else
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
lean_dec_ref(v___y_1760_);
v_a_1785_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___x_1776_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1776_);
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
}
}
}
else
{
lean_dec_ref(v___y_1760_);
return v___y_1761_;
}
}
v___jp_1794_:
{
uint8_t v___x_1797_; 
v___x_1797_ = l_Lean_Exception_isInterrupt(v_a_1796_);
if (v___x_1797_ == 0)
{
uint8_t v___x_1798_; 
lean_inc_ref(v_a_1796_);
v___x_1798_ = l_Lean_Exception_isRuntime(v_a_1796_);
v___y_1760_ = v_a_1796_;
v___y_1761_ = v___y_1795_;
v___y_1762_ = v___x_1798_;
goto v___jp_1759_;
}
else
{
v___y_1760_ = v_a_1796_;
v___y_1761_ = v___y_1795_;
v___y_1762_ = v___x_1797_;
goto v___jp_1759_;
}
}
v___jp_1799_:
{
if (lean_obj_tag(v___y_1800_) == 0)
{
return v___y_1800_;
}
else
{
lean_object* v_a_1801_; 
v_a_1801_ = lean_ctor_get(v___y_1800_, 0);
lean_inc(v_a_1801_);
v___y_1795_ = v___y_1800_;
v_a_1796_ = v_a_1801_;
goto v___jp_1794_;
}
}
v___jp_1802_:
{
if (v___y_1805_ == 0)
{
lean_object* v___x_1806_; lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1836_; 
lean_dec_ref(v___y_1804_);
v___x_1806_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__0(v___x_1758_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1809_ = v___x_1806_;
v_isShared_1810_ = v_isSharedCheck_1836_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1806_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1836_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
uint8_t v___x_1811_; 
v___x_1811_ = lean_unbox(v_a_1807_);
lean_dec(v_a_1807_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1813_; 
if (v_isShared_1810_ == 0)
{
lean_ctor_set_tag(v___x_1809_, 1);
lean_ctor_set(v___x_1809_, 0, v___y_1803_);
v___x_1813_ = v___x_1809_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___y_1803_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
else
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
lean_del_object(v___x_1809_);
v___x_1815_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___closed__1);
lean_inc_ref(v___y_1803_);
v___x_1816_ = l_Lean_Exception_toMessageData(v___y_1803_);
v___x_1817_ = l_Lean_indentD(v___x_1816_);
v___x_1818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1815_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
v___x_1819_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1758_, v___x_1818_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1826_; 
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1826_ == 0)
{
lean_object* v_unused_1827_; 
v_unused_1827_ = lean_ctor_get(v___x_1819_, 0);
lean_dec(v_unused_1827_);
v___x_1821_ = v___x_1819_;
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
else
{
lean_dec(v___x_1819_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
lean_ctor_set_tag(v___x_1821_, 1);
lean_ctor_set(v___x_1821_, 0, v___y_1803_);
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___y_1803_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
else
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1835_; 
lean_dec_ref(v___y_1803_);
v_a_1828_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1830_ = v___x_1819_;
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1819_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1833_; 
if (v_isShared_1831_ == 0)
{
v___x_1833_ = v___x_1830_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1828_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_1803_);
return v___y_1804_;
}
}
v___jp_1837_:
{
uint8_t v___x_1840_; 
v___x_1840_ = l_Lean_Exception_isInterrupt(v_a_1839_);
if (v___x_1840_ == 0)
{
uint8_t v___x_1841_; 
lean_inc_ref(v_a_1839_);
v___x_1841_ = l_Lean_Exception_isRuntime(v_a_1839_);
v___y_1803_ = v_a_1839_;
v___y_1804_ = v___y_1838_;
v___y_1805_ = v___x_1841_;
goto v___jp_1802_;
}
else
{
v___y_1803_ = v_a_1839_;
v___y_1804_ = v___y_1838_;
v___y_1805_ = v___x_1840_;
goto v___jp_1802_;
}
}
v___jp_1842_:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1853_; 
v___x_1849_ = lean_array_get(v___x_1757_, v_x_1734_, v___y_1844_);
lean_dec(v___y_1844_);
lean_dec_ref(v_x_1734_);
v___x_1850_ = l_Lean_Expr_fvarId_x21(v___x_1849_);
lean_dec(v___x_1849_);
v___x_1851_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___lam__1___closed__0));
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 0, v___y_1843_);
v___x_1853_ = v___x_1753_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___y_1843_);
v___x_1853_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
lean_object* v___x_1854_; 
v___x_1854_ = l_Lean_MVarId_cases(v_mvarId_1732_, v___x_1850_, v___x_1851_, v_hasTrace_1756_, v___x_1853_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v_a_1855_; size_t v_sz_1856_; size_t v___x_1857_; lean_object* v___x_1858_; 
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_a_1855_);
lean_dec_ref(v___x_1854_);
v_sz_1856_ = lean_array_size(v_a_1855_);
v___x_1857_ = ((size_t)0ULL);
v___x_1858_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(v_declName_1747_, v_val_1751_, v_hasTrace_1756_, v_sz_1856_, v___x_1857_, v_a_1855_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
if (lean_obj_tag(v___x_1858_) == 0)
{
return v___x_1858_;
}
else
{
lean_object* v_a_1859_; 
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_a_1859_);
v___y_1838_ = v___x_1858_;
v_a_1839_ = v_a_1859_;
goto v___jp_1837_;
}
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
lean_dec(v_val_1751_);
lean_dec(v_declName_1747_);
v_a_1860_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1854_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1854_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
lean_inc(v_a_1860_);
if (v_isShared_1863_ == 0)
{
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
v___y_1838_ = v___x_1865_;
v_a_1839_ = v_a_1860_;
goto v___jp_1837_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2062_; lean_object* v___x_2063_; 
lean_dec(v_a_1749_);
lean_dec(v_declName_1747_);
lean_dec_ref(v_x_1734_);
lean_dec(v_mvarId_1732_);
v___x_2062_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12);
v___x_2063_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_2062_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
return v___x_2063_;
}
}
else
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
lean_dec(v_declName_1747_);
lean_dec_ref(v_x_1734_);
lean_dec(v_mvarId_1732_);
v_a_2064_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2066_ = v___x_1748_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_1748_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2064_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
else
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
lean_dec_ref(v_x_1734_);
lean_dec_ref(v_x_1733_);
lean_dec(v_mvarId_1732_);
v___x_2072_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14);
v___x_2073_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_2072_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
return v___x_2073_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5___boxed(lean_object* v_mvarId_2074_, lean_object* v_x_2075_, lean_object* v_x_2076_, lean_object* v_x_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5(v_mvarId_2074_, v_x_2075_, v_x_2076_, v_x_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitSparseCasesOn(lean_object* v_mvarId_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_){
_start:
{
lean_object* v___x_2090_; 
lean_inc(v_mvarId_2084_);
v___x_2090_ = l_Lean_MVarId_getType(v_mvarId_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; lean_object* v___x_2092_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2091_);
lean_dec_ref(v___x_2090_);
v___x_2092_ = l_Lean_Meta_matchEqHEqLHS_x3f(v_a_2091_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2093_);
lean_dec_ref(v___x_2092_);
if (lean_obj_tag(v_a_2093_) == 1)
{
lean_object* v_val_2094_; lean_object* v_snd_2095_; lean_object* v_dummy_2096_; lean_object* v_nargs_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v_val_2094_ = lean_ctor_get(v_a_2093_, 0);
lean_inc(v_val_2094_);
lean_dec_ref(v_a_2093_);
v_snd_2095_ = lean_ctor_get(v_val_2094_, 1);
lean_inc(v_snd_2095_);
lean_dec(v_val_2094_);
v_dummy_2096_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0);
v_nargs_2097_ = l_Lean_Expr_getAppNumArgs(v_snd_2095_);
lean_inc(v_nargs_2097_);
v___x_2098_ = lean_mk_array(v_nargs_2097_, v_dummy_2096_);
v___x_2099_ = lean_unsigned_to_nat(1u);
v___x_2100_ = lean_nat_sub(v_nargs_2097_, v___x_2099_);
lean_dec(v_nargs_2097_);
v___x_2101_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__5(v_mvarId_2084_, v_snd_2095_, v___x_2098_, v___x_2100_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_);
return v___x_2101_;
}
else
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
lean_dec(v_a_2093_);
lean_dec(v_mvarId_2084_);
v___x_2102_ = lean_obj_once(&l_Lean_Meta_reduceSparseCasesOn___closed__1, &l_Lean_Meta_reduceSparseCasesOn___closed__1_once, _init_l_Lean_Meta_reduceSparseCasesOn___closed__1);
v___x_2103_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_2102_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_);
return v___x_2103_;
}
}
else
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
lean_dec(v_mvarId_2084_);
v_a_2104_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2092_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2092_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_dec(v_mvarId_2084_);
v_a_2112_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2090_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2090_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitSparseCasesOn___boxed(lean_object* v_mvarId_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_){
_start:
{
lean_object* v_res_2126_; 
v_res_2126_ = l_Lean_Meta_splitSparseCasesOn(v_mvarId_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_);
lean_dec(v_a_2124_);
lean_dec_ref(v_a_2123_);
lean_dec(v_a_2122_);
lean_dec_ref(v_a_2121_);
return v_res_2126_;
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
