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
lean_object* l_Lean_Meta_isConstructorApp_x27_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_getSparseCasesOnEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_mkHasNotBitProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_rewrite(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_modifyTargetEqLHS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_getSparseCasesOnInfo___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchEqHEqLHS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_div(double, double);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
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
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "splitSparseCasesOn"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Major premise is not a constructor application:"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "Not enough arguments for sparse casesOn application"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9_spec__10(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_unfoldDefinition___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0_value;
static const lean_closure_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(lean_object*, lean_object*, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__0_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Major premise is not a free variable:"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__1_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "splitSparseCasesOn failed"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__0_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "splitSparseCasesOn running on\n"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__2_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v___x_14_, 1);
v___x_16_ = ((lean_object*)(l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq___closed__0));
lean_inc(v_goal_6_);
v___x_17_ = l_Lean_MVarId_rewrite(v_goal_6_, v_a_15_, v_eq_7_, v_symm_8_, v___x_16_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
if (lean_obj_tag(v___x_17_) == 0)
{
lean_object* v_a_18_; lean_object* v_eNew_19_; lean_object* v_eqProof_20_; lean_object* v___x_21_; 
v_a_18_ = lean_ctor_get(v___x_17_, 0);
lean_inc(v_a_18_);
lean_dec_ref_known(v___x_17_, 1);
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
lean_object* v___x_59_; lean_object* v_traceState_60_; lean_object* v_traces_61_; lean_object* v___x_62_; lean_object* v_traceState_63_; lean_object* v_env_64_; lean_object* v_nextMacroScope_65_; lean_object* v_ngen_66_; lean_object* v_auxDeclNGen_67_; lean_object* v_cache_68_; lean_object* v_recordedDeps_69_; lean_object* v_messages_70_; lean_object* v_infoState_71_; lean_object* v_snapshotTasks_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_91_; 
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
v_recordedDeps_69_ = lean_ctor_get(v___x_62_, 6);
v_messages_70_ = lean_ctor_get(v___x_62_, 7);
v_infoState_71_ = lean_ctor_get(v___x_62_, 8);
v_snapshotTasks_72_ = lean_ctor_get(v___x_62_, 9);
v_isSharedCheck_91_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_91_ == 0)
{
v___x_74_ = v___x_62_;
v_isShared_75_ = v_isSharedCheck_91_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_snapshotTasks_72_);
lean_inc(v_infoState_71_);
lean_inc(v_messages_70_);
lean_inc(v_recordedDeps_69_);
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
lean_ctor_set(v_reuseFailAlloc_87_, 6, v_recordedDeps_69_);
lean_ctor_set(v_reuseFailAlloc_87_, 7, v_messages_70_);
lean_ctor_set(v_reuseFailAlloc_87_, 8, v_infoState_71_);
lean_ctor_set(v_reuseFailAlloc_87_, 9, v_snapshotTasks_72_);
v___x_84_ = v_reuseFailAlloc_87_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_st_ref_put(v___y_57_, v___x_84_);
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
lean_dec_ref_known(v___x_112_, 1);
if (lean_obj_tag(v_val_114_) == 1)
{
uint8_t v_v_115_; 
v_v_115_ = lean_ctor_get_uint8(v_val_114_, 0);
lean_dec_ref_known(v_val_114_, 0);
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
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__1(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0));
v___x_123_ = l_Lean_stringToMessageData(v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0(lean_object* v_x_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__1);
v___x_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___boxed(lean_object* v_x_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0(v_x_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec_ref(v_x_132_);
return v_res_138_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1_spec__2(lean_object* v_a_139_, lean_object* v_as_140_, size_t v_i_141_, size_t v_stop_142_){
_start:
{
uint8_t v___x_143_; 
v___x_143_ = lean_usize_dec_eq(v_i_141_, v_stop_142_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_144_ = lean_array_uget_borrowed(v_as_140_, v_i_141_);
v___x_145_ = lean_name_eq(v_a_139_, v___x_144_);
if (v___x_145_ == 0)
{
size_t v___x_146_; size_t v___x_147_; 
v___x_146_ = ((size_t)1ULL);
v___x_147_ = lean_usize_add(v_i_141_, v___x_146_);
v_i_141_ = v___x_147_;
goto _start;
}
else
{
return v___x_145_;
}
}
else
{
uint8_t v___x_149_; 
v___x_149_ = 0;
return v___x_149_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1_spec__2___boxed(lean_object* v_a_150_, lean_object* v_as_151_, lean_object* v_i_152_, lean_object* v_stop_153_){
_start:
{
size_t v_i_boxed_154_; size_t v_stop_boxed_155_; uint8_t v_res_156_; lean_object* v_r_157_; 
v_i_boxed_154_ = lean_unbox_usize(v_i_152_);
lean_dec(v_i_152_);
v_stop_boxed_155_ = lean_unbox_usize(v_stop_153_);
lean_dec(v_stop_153_);
v_res_156_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1_spec__2(v_a_150_, v_as_151_, v_i_boxed_154_, v_stop_boxed_155_);
lean_dec_ref(v_as_151_);
lean_dec(v_a_150_);
v_r_157_ = lean_box(v_res_156_);
return v_r_157_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1(lean_object* v_as_158_, lean_object* v_a_159_){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_160_ = lean_unsigned_to_nat(0u);
v___x_161_ = lean_array_get_size(v_as_158_);
v___x_162_ = lean_nat_dec_lt(v___x_160_, v___x_161_);
if (v___x_162_ == 0)
{
return v___x_162_;
}
else
{
size_t v___x_163_; size_t v___x_164_; uint8_t v___x_165_; 
v___x_163_ = ((size_t)0ULL);
v___x_164_ = lean_usize_of_nat(v___x_161_);
v___x_165_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1_spec__2(v_a_159_, v_as_158_, v___x_163_, v___x_164_);
return v___x_165_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1___boxed(lean_object* v_as_166_, lean_object* v_a_167_){
_start:
{
uint8_t v_res_168_; lean_object* v_r_169_; 
v_res_168_ = l_Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1(v_as_166_, v_a_167_);
lean_dec(v_a_167_);
lean_dec_ref(v_as_166_);
v_r_169_ = lean_box(v_res_168_);
return v_r_169_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_instMonadEIO___redArg();
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0(lean_object* v_msg_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v_toApplicative_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_244_; 
v___x_181_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__0);
v___x_182_ = l_StateRefT_x27_instMonad___redArg(v___x_181_);
v_toApplicative_183_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_244_ == 0)
{
lean_object* v_unused_245_; 
v_unused_245_ = lean_ctor_get(v___x_182_, 1);
lean_dec(v_unused_245_);
v___x_185_ = v___x_182_;
v_isShared_186_ = v_isSharedCheck_244_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_toApplicative_183_);
lean_dec(v___x_182_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_244_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v_toFunctor_187_; lean_object* v_toSeq_188_; lean_object* v_toSeqLeft_189_; lean_object* v_toSeqRight_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_242_; 
v_toFunctor_187_ = lean_ctor_get(v_toApplicative_183_, 0);
v_toSeq_188_ = lean_ctor_get(v_toApplicative_183_, 2);
v_toSeqLeft_189_ = lean_ctor_get(v_toApplicative_183_, 3);
v_toSeqRight_190_ = lean_ctor_get(v_toApplicative_183_, 4);
v_isSharedCheck_242_ = !lean_is_exclusive(v_toApplicative_183_);
if (v_isSharedCheck_242_ == 0)
{
lean_object* v_unused_243_; 
v_unused_243_ = lean_ctor_get(v_toApplicative_183_, 1);
lean_dec(v_unused_243_);
v___x_192_ = v_toApplicative_183_;
v_isShared_193_ = v_isSharedCheck_242_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_toSeqRight_190_);
lean_inc(v_toSeqLeft_189_);
lean_inc(v_toSeq_188_);
lean_inc(v_toFunctor_187_);
lean_dec(v_toApplicative_183_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_242_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___f_194_; lean_object* v___f_195_; lean_object* v___f_196_; lean_object* v___f_197_; lean_object* v___x_198_; lean_object* v___f_199_; lean_object* v___f_200_; lean_object* v___f_201_; lean_object* v___x_203_; 
v___f_194_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__1));
v___f_195_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_187_);
v___f_196_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_196_, 0, v_toFunctor_187_);
v___f_197_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_197_, 0, v_toFunctor_187_);
v___x_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_198_, 0, v___f_196_);
lean_ctor_set(v___x_198_, 1, v___f_197_);
v___f_199_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_199_, 0, v_toSeqRight_190_);
v___f_200_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_200_, 0, v_toSeqLeft_189_);
v___f_201_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_201_, 0, v_toSeq_188_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 4, v___f_199_);
lean_ctor_set(v___x_192_, 3, v___f_200_);
lean_ctor_set(v___x_192_, 2, v___f_201_);
lean_ctor_set(v___x_192_, 1, v___f_194_);
lean_ctor_set(v___x_192_, 0, v___x_198_);
v___x_203_ = v___x_192_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_198_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v___f_194_);
lean_ctor_set(v_reuseFailAlloc_241_, 2, v___f_201_);
lean_ctor_set(v_reuseFailAlloc_241_, 3, v___f_200_);
lean_ctor_set(v_reuseFailAlloc_241_, 4, v___f_199_);
v___x_203_ = v_reuseFailAlloc_241_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
lean_object* v___x_205_; 
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 1, v___f_195_);
lean_ctor_set(v___x_185_, 0, v___x_203_);
v___x_205_ = v___x_185_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_203_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v___f_195_);
v___x_205_ = v_reuseFailAlloc_240_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v___x_206_; lean_object* v_toApplicative_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_238_; 
v___x_206_ = l_StateRefT_x27_instMonad___redArg(v___x_205_);
v_toApplicative_207_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_238_ == 0)
{
lean_object* v_unused_239_; 
v_unused_239_ = lean_ctor_get(v___x_206_, 1);
lean_dec(v_unused_239_);
v___x_209_ = v___x_206_;
v_isShared_210_ = v_isSharedCheck_238_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_toApplicative_207_);
lean_dec(v___x_206_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_238_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v_toFunctor_211_; lean_object* v_toSeq_212_; lean_object* v_toSeqLeft_213_; lean_object* v_toSeqRight_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_236_; 
v_toFunctor_211_ = lean_ctor_get(v_toApplicative_207_, 0);
v_toSeq_212_ = lean_ctor_get(v_toApplicative_207_, 2);
v_toSeqLeft_213_ = lean_ctor_get(v_toApplicative_207_, 3);
v_toSeqRight_214_ = lean_ctor_get(v_toApplicative_207_, 4);
v_isSharedCheck_236_ = !lean_is_exclusive(v_toApplicative_207_);
if (v_isSharedCheck_236_ == 0)
{
lean_object* v_unused_237_; 
v_unused_237_ = lean_ctor_get(v_toApplicative_207_, 1);
lean_dec(v_unused_237_);
v___x_216_ = v_toApplicative_207_;
v_isShared_217_ = v_isSharedCheck_236_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_toSeqRight_214_);
lean_inc(v_toSeqLeft_213_);
lean_inc(v_toSeq_212_);
lean_inc(v_toFunctor_211_);
lean_dec(v_toApplicative_207_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_236_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___f_218_; lean_object* v___f_219_; lean_object* v___f_220_; lean_object* v___f_221_; lean_object* v___x_222_; lean_object* v___f_223_; lean_object* v___f_224_; lean_object* v___f_225_; lean_object* v___x_227_; 
v___f_218_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__3));
v___f_219_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__4));
lean_inc_ref(v_toFunctor_211_);
v___f_220_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_220_, 0, v_toFunctor_211_);
v___f_221_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_221_, 0, v_toFunctor_211_);
v___x_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_222_, 0, v___f_220_);
lean_ctor_set(v___x_222_, 1, v___f_221_);
v___f_223_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_223_, 0, v_toSeqRight_214_);
v___f_224_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_224_, 0, v_toSeqLeft_213_);
v___f_225_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_225_, 0, v_toSeq_212_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 4, v___f_223_);
lean_ctor_set(v___x_216_, 3, v___f_224_);
lean_ctor_set(v___x_216_, 2, v___f_225_);
lean_ctor_set(v___x_216_, 1, v___f_218_);
lean_ctor_set(v___x_216_, 0, v___x_222_);
v___x_227_ = v___x_216_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_222_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v___f_218_);
lean_ctor_set(v_reuseFailAlloc_235_, 2, v___f_225_);
lean_ctor_set(v_reuseFailAlloc_235_, 3, v___f_224_);
lean_ctor_set(v_reuseFailAlloc_235_, 4, v___f_223_);
v___x_227_ = v_reuseFailAlloc_235_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
lean_object* v___x_229_; 
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 1, v___f_219_);
lean_ctor_set(v___x_209_, 0, v___x_227_);
v___x_229_ = v___x_209_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v___f_219_);
v___x_229_ = v_reuseFailAlloc_234_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_10573__overap_232_; lean_object* v___x_233_; 
v___x_230_ = lean_box(0);
v___x_231_ = l_instInhabitedOfMonad___redArg(v___x_229_, v___x_230_);
v___x_10573__overap_232_ = lean_panic_fn_borrowed(v___x_231_, v_msg_175_);
lean_dec(v___x_231_);
lean_inc(v___y_179_);
lean_inc_ref(v___y_178_);
lean_inc(v___y_177_);
lean_inc_ref(v___y_176_);
v___x_233_ = lean_apply_5(v___x_10573__overap_232_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, lean_box(0));
return v___x_233_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___boxed(lean_object* v_msg_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0(v_msg_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(lean_object* v_msgData_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v___x_259_; lean_object* v_env_260_; uint8_t v___x_261_; lean_object* v_env_262_; lean_object* v___x_263_; lean_object* v_toCold_264_; lean_object* v_mctx_265_; lean_object* v_lctx_266_; lean_object* v_options_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_259_ = lean_st_ref_get(v___y_257_);
v_env_260_ = lean_ctor_get(v___x_259_, 0);
lean_inc_ref(v_env_260_);
lean_dec(v___x_259_);
v___x_261_ = 0;
v_env_262_ = l_Lean_Environment_setRecordingDeps(v_env_260_, v___x_261_);
v___x_263_ = lean_st_ref_get(v___y_255_);
v_toCold_264_ = lean_ctor_get(v___y_256_, 0);
v_mctx_265_ = lean_ctor_get(v___x_263_, 0);
lean_inc_ref(v_mctx_265_);
lean_dec(v___x_263_);
v_lctx_266_ = lean_ctor_get(v___y_254_, 2);
v_options_267_ = lean_ctor_get(v_toCold_264_, 2);
lean_inc_ref(v_options_267_);
lean_inc_ref(v_lctx_266_);
v___x_268_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_268_, 0, v_env_262_);
lean_ctor_set(v___x_268_, 1, v_mctx_265_);
lean_ctor_set(v___x_268_, 2, v_lctx_266_);
lean_ctor_set(v___x_268_, 3, v_options_267_);
v___x_269_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v_msgData_253_);
v___x_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5___boxed(lean_object* v_msgData_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msgData_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(lean_object* v_msg_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v_ref_284_; lean_object* v___x_285_; lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_294_; 
v_ref_284_ = lean_ctor_get(v___y_281_, 2);
v___x_285_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msg_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
v_a_286_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_294_ == 0)
{
v___x_288_ = v___x_285_;
v_isShared_289_ = v_isSharedCheck_294_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_285_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_294_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_290_; lean_object* v___x_292_; 
lean_inc(v_ref_284_);
v___x_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_290_, 0, v_ref_284_);
lean_ctor_set(v___x_290_, 1, v_a_286_);
if (v_isShared_289_ == 0)
{
lean_ctor_set_tag(v___x_288_, 1);
lean_ctor_set(v___x_288_, 0, v___x_290_);
v___x_292_ = v___x_288_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_290_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg___boxed(lean_object* v_msg_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v_msg_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
return v_res_301_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__1(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__0));
v___x_304_ = l_Lean_stringToMessageData(v___x_303_);
return v___x_304_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__3(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__2));
v___x_307_ = l_Lean_stringToMessageData(v___x_306_);
return v___x_307_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__7(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_311_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__6));
v___x_312_ = lean_unsigned_to_nat(11u);
v___x_313_ = lean_unsigned_to_nat(122u);
v___x_314_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__5));
v___x_315_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__4));
v___x_316_ = l_mkPanicMessageWithDecl(v___x_315_, v___x_314_, v___x_313_, v___x_312_, v___x_311_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0(lean_object* v_constName_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v___x_331_; lean_object* v_env_332_; uint8_t v___x_333_; lean_object* v___x_334_; 
v___x_331_ = lean_st_ref_get(v___y_321_);
v_env_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc_ref(v_env_332_);
lean_dec(v___x_331_);
v___x_333_ = 0;
lean_inc(v_constName_317_);
v___x_334_ = l_Lean_Environment_findAsync_x3f(v_env_332_, v_constName_317_, v___x_333_);
if (lean_obj_tag(v___x_334_) == 1)
{
lean_object* v_val_335_; uint8_t v_kind_336_; 
v_val_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_val_335_);
lean_dec_ref_known(v___x_334_, 1);
v_kind_336_ = lean_ctor_get_uint8(v_val_335_, sizeof(void*)*3);
if (v_kind_336_ == 6)
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_335_);
if (lean_obj_tag(v___x_337_) == 6)
{
lean_object* v_val_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_345_; 
lean_dec(v_constName_317_);
v_val_338_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_345_ == 0)
{
v___x_340_ = v___x_337_;
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_val_338_);
lean_dec(v___x_337_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_341_ == 0)
{
lean_ctor_set_tag(v___x_340_, 0);
v___x_343_ = v___x_340_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_val_338_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
else
{
lean_object* v___x_346_; lean_object* v___x_347_; 
lean_dec_ref(v___x_337_);
v___x_346_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__7);
v___x_347_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0(v___x_346_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_356_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_356_ == 0)
{
v___x_350_ = v___x_347_;
v_isShared_351_ = v_isSharedCheck_356_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_347_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_356_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
if (lean_obj_tag(v_a_348_) == 0)
{
lean_del_object(v___x_350_);
goto v___jp_323_;
}
else
{
lean_object* v_val_352_; lean_object* v___x_354_; 
lean_dec(v_constName_317_);
v_val_352_ = lean_ctor_get(v_a_348_, 0);
lean_inc(v_val_352_);
lean_dec_ref_known(v_a_348_, 1);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 0, v_val_352_);
v___x_354_ = v___x_350_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_val_352_);
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
else
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_364_; 
lean_dec(v_constName_317_);
v_a_357_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_364_ == 0)
{
v___x_359_ = v___x_347_;
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_347_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
if (v_isShared_360_ == 0)
{
v___x_362_ = v___x_359_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_a_357_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
}
else
{
lean_dec(v_val_335_);
goto v___jp_323_;
}
}
else
{
lean_dec(v___x_334_);
goto v___jp_323_;
}
v___jp_323_:
{
lean_object* v___x_324_; uint8_t v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_324_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__1);
v___x_325_ = 0;
v___x_326_ = l_Lean_MessageData_ofConstName(v_constName_317_, v___x_325_);
v___x_327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_324_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
v___x_328_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__3);
v___x_329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_327_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
v___x_330_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_329_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
return v___x_330_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___boxed(lean_object* v_constName_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0(v_constName_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_reduceSparseCasesOn_spec__2(size_t v_sz_372_, size_t v_i_373_, lean_object* v_bs_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
uint8_t v___x_380_; 
v___x_380_ = lean_usize_dec_lt(v_i_373_, v_sz_372_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; 
v___x_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_381_, 0, v_bs_374_);
return v___x_381_;
}
else
{
lean_object* v_v_382_; lean_object* v___x_383_; lean_object* v_bs_x27_384_; lean_object* v___x_385_; 
v_v_382_ = lean_array_uget(v_bs_374_, v_i_373_);
v___x_383_ = lean_unsigned_to_nat(0u);
v_bs_x27_384_ = lean_array_uset(v_bs_374_, v_i_373_, v___x_383_);
v___x_385_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0(v_v_382_, v___y_375_, v___y_376_, v___y_377_, v___y_378_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; lean_object* v_cidx_387_; size_t v___x_388_; size_t v___x_389_; lean_object* v___x_390_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_a_386_);
lean_dec_ref_known(v___x_385_, 1);
v_cidx_387_ = lean_ctor_get(v_a_386_, 2);
lean_inc(v_cidx_387_);
lean_dec(v_a_386_);
v___x_388_ = ((size_t)1ULL);
v___x_389_ = lean_usize_add(v_i_373_, v___x_388_);
v___x_390_ = lean_array_uset(v_bs_x27_384_, v_i_373_, v_cidx_387_);
v_i_373_ = v___x_389_;
v_bs_374_ = v___x_390_;
goto _start;
}
else
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
lean_dec_ref(v_bs_x27_384_);
v_a_392_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_385_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_385_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_reduceSparseCasesOn_spec__2___boxed(lean_object* v_sz_400_, lean_object* v_i_401_, lean_object* v_bs_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
size_t v_sz_boxed_408_; size_t v_i_boxed_409_; lean_object* v_res_410_; 
v_sz_boxed_408_ = lean_unbox_usize(v_sz_400_);
lean_dec(v_sz_400_);
v_i_boxed_409_ = lean_unbox_usize(v_i_401_);
lean_dec(v_i_401_);
v_res_410_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_reduceSparseCasesOn_spec__2(v_sz_boxed_408_, v_i_boxed_409_, v_bs_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
return v_res_410_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0(void){
_start:
{
lean_object* v___x_411_; lean_object* v_dummy_412_; 
v___x_411_ = lean_box(0);
v_dummy_412_ = l_Lean_Expr_sort___override(v___x_411_);
return v_dummy_412_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__2(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1));
v___x_415_ = l_Lean_stringToMessageData(v___x_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(lean_object* v___x_416_, lean_object* v_x_417_, lean_object* v_majorPos_418_, lean_object* v_insterestingCtors_419_, lean_object* v_declName_420_, lean_object* v_snd_421_, lean_object* v_arity_422_, lean_object* v_mvarId_423_, lean_object* v___f_424_, lean_object* v_____r_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = lean_array_get_borrowed(v___x_416_, v_x_417_, v_majorPos_418_);
lean_inc(v___x_431_);
v___x_432_ = l_Lean_Meta_isConstructorApp_x27_x3f(v___x_431_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_a_433_);
lean_dec_ref_known(v___x_432_, 1);
if (lean_obj_tag(v_a_433_) == 1)
{
lean_object* v_val_434_; lean_object* v_toConstantVal_435_; lean_object* v_cidx_436_; lean_object* v_name_437_; uint8_t v___x_438_; 
v_val_434_ = lean_ctor_get(v_a_433_, 0);
lean_inc(v_val_434_);
lean_dec_ref_known(v_a_433_, 1);
v_toConstantVal_435_ = lean_ctor_get(v_val_434_, 0);
lean_inc_ref(v_toConstantVal_435_);
v_cidx_436_ = lean_ctor_get(v_val_434_, 2);
lean_inc(v_cidx_436_);
lean_dec(v_val_434_);
v_name_437_ = lean_ctor_get(v_toConstantVal_435_, 0);
lean_inc(v_name_437_);
lean_dec_ref(v_toConstantVal_435_);
v___x_438_ = l_Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1(v_insterestingCtors_419_, v_name_437_);
lean_dec(v_name_437_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; 
lean_dec_ref(v___f_424_);
v___x_439_ = l_Lean_Meta_getSparseCasesOnEq(v_declName_420_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v_dummy_444_; lean_object* v_nargs_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; size_t v_sz_454_; size_t v___x_455_; lean_object* v___x_456_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_a_440_);
lean_dec_ref_known(v___x_439_, 1);
v___x_441_ = l_Lean_Expr_getAppFn(v_snd_421_);
v___x_442_ = l_Lean_Expr_constLevels_x21(v___x_441_);
lean_dec_ref(v___x_441_);
v___x_443_ = l_Lean_mkConst(v_a_440_, v___x_442_);
v_dummy_444_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0);
v_nargs_445_ = l_Lean_Expr_getAppNumArgs(v_snd_421_);
lean_inc(v_nargs_445_);
v___x_446_ = lean_mk_array(v_nargs_445_, v_dummy_444_);
v___x_447_ = lean_unsigned_to_nat(1u);
v___x_448_ = lean_nat_sub(v_nargs_445_, v___x_447_);
lean_dec(v_nargs_445_);
v___x_449_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_snd_421_, v___x_446_, v___x_448_);
v___x_450_ = lean_unsigned_to_nat(0u);
v___x_451_ = l_Array_toSubarray___redArg(v___x_449_, v___x_450_, v_arity_422_);
v___x_452_ = l_Subarray_copy___redArg(v___x_451_);
v___x_453_ = l_Lean_mkAppN(v___x_443_, v___x_452_);
lean_dec_ref(v___x_452_);
v_sz_454_ = lean_array_size(v_insterestingCtors_419_);
v___x_455_ = ((size_t)0ULL);
v___x_456_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_reduceSparseCasesOn_spec__2(v_sz_454_, v___x_455_, v_insterestingCtors_419_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_a_457_);
lean_dec_ref_known(v___x_456_, 1);
v___x_458_ = l_Lean_mkRawNatLit(v_cidx_436_);
v___x_459_ = l_Lean_mkHasNotBitProof(v___x_458_, v_a_457_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
lean_dec(v_a_457_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v_a_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_a_460_ = lean_ctor_get(v___x_459_, 0);
lean_inc(v_a_460_);
lean_dec_ref_known(v___x_459_, 1);
v___x_461_ = l_Lean_Expr_app___override(v___x_453_, v_a_460_);
v___x_462_ = l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq(v_mvarId_423_, v___x_461_, v___x_438_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_472_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_472_ == 0)
{
v___x_465_ = v___x_462_;
v_isShared_466_ = v_isSharedCheck_472_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_462_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_472_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_470_; 
v___x_467_ = lean_mk_empty_array_with_capacity(v___x_447_);
v___x_468_ = lean_array_push(v___x_467_, v_a_463_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 0, v___x_468_);
v___x_470_ = v___x_465_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_468_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
else
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
v_a_473_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v___x_462_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_462_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_473_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
else
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
lean_dec_ref(v___x_453_);
lean_dec(v_mvarId_423_);
v_a_481_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_488_ == 0)
{
v___x_483_ = v___x_459_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_459_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_481_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
else
{
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_496_; 
lean_dec_ref(v___x_453_);
lean_dec(v_cidx_436_);
lean_dec(v_mvarId_423_);
v_a_489_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_496_ == 0)
{
v___x_491_ = v___x_456_;
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_456_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_494_; 
if (v_isShared_492_ == 0)
{
v___x_494_ = v___x_491_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_489_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
lean_dec(v_cidx_436_);
lean_dec(v_mvarId_423_);
lean_dec(v_arity_422_);
lean_dec_ref(v_snd_421_);
lean_dec_ref(v_insterestingCtors_419_);
v_a_497_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_439_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_439_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
else
{
lean_object* v___x_505_; 
lean_dec(v_cidx_436_);
lean_dec(v_arity_422_);
lean_dec_ref(v_snd_421_);
lean_dec(v_declName_420_);
lean_dec_ref(v_insterestingCtors_419_);
v___x_505_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_423_, v___f_424_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_516_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_516_ == 0)
{
v___x_508_ = v___x_505_;
v_isShared_509_ = v_isSharedCheck_516_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_505_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_516_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_514_; 
v___x_510_ = lean_unsigned_to_nat(1u);
v___x_511_ = lean_mk_empty_array_with_capacity(v___x_510_);
v___x_512_ = lean_array_push(v___x_511_, v_a_506_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_512_);
v___x_514_ = v___x_508_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_512_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
else
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
v_a_517_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v___x_505_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_505_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_517_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
}
else
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
lean_dec(v_a_433_);
lean_dec_ref(v___f_424_);
lean_dec(v_mvarId_423_);
lean_dec(v_arity_422_);
lean_dec_ref(v_snd_421_);
lean_dec(v_declName_420_);
lean_dec_ref(v_insterestingCtors_419_);
v___x_525_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__2);
lean_inc(v___x_431_);
v___x_526_ = l_Lean_indentExpr(v___x_431_);
v___x_527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_525_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_527_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
return v___x_528_;
}
}
else
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
lean_dec_ref(v___f_424_);
lean_dec(v_mvarId_423_);
lean_dec(v_arity_422_);
lean_dec_ref(v_snd_421_);
lean_dec(v_declName_420_);
lean_dec_ref(v_insterestingCtors_419_);
v_a_529_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_536_ == 0)
{
v___x_531_ = v___x_432_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_432_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_529_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___boxed(lean_object* v___x_537_, lean_object* v_x_538_, lean_object* v_majorPos_539_, lean_object* v_insterestingCtors_540_, lean_object* v_declName_541_, lean_object* v_snd_542_, lean_object* v_arity_543_, lean_object* v_mvarId_544_, lean_object* v___f_545_, lean_object* v_____r_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(v___x_537_, v_x_538_, v_majorPos_539_, v_insterestingCtors_540_, v_declName_541_, v_snd_542_, v_arity_543_, v_mvarId_544_, v___f_545_, v_____r_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v_majorPos_539_);
lean_dec_ref(v_x_538_);
lean_dec_ref(v___x_537_);
return v_res_552_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__0));
v___x_555_ = l_Lean_stringToMessageData(v___x_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2(uint8_t v___x_556_, lean_object* v___f_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
if (v___x_556_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = lean_box(0);
lean_inc(v___y_561_);
lean_inc_ref(v___y_560_);
lean_inc(v___y_559_);
lean_inc_ref(v___y_558_);
v___x_564_ = lean_apply_6(v___f_557_, v___x_563_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, lean_box(0));
return v___x_564_;
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
lean_dec_ref(v___f_557_);
v___x_565_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1);
v___x_566_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_565_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
v_a_567_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_566_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_566_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___boxed(lean_object* v___x_575_, lean_object* v___f_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
uint8_t v___x_14366__boxed_582_; lean_object* v_res_583_; 
v___x_14366__boxed_582_ = lean_unbox(v___x_575_);
v_res_583_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2(v___x_14366__boxed_582_, v___f_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
return v_res_583_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11(lean_object* v_e_584_){
_start:
{
if (lean_obj_tag(v_e_584_) == 0)
{
uint8_t v___x_585_; 
v___x_585_ = 2;
return v___x_585_;
}
else
{
uint8_t v___x_586_; 
v___x_586_ = 0;
return v___x_586_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11___boxed(lean_object* v_e_587_){
_start:
{
uint8_t v_res_588_; lean_object* v_r_589_; 
v_res_588_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11(v_e_587_);
lean_dec_ref(v_e_587_);
v_r_589_ = lean_box(v_res_588_);
return v_r_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12(lean_object* v_opts_590_, lean_object* v_opt_591_){
_start:
{
lean_object* v_name_592_; lean_object* v_defValue_593_; lean_object* v_map_594_; lean_object* v___x_595_; 
v_name_592_ = lean_ctor_get(v_opt_591_, 0);
v_defValue_593_ = lean_ctor_get(v_opt_591_, 1);
v_map_594_ = lean_ctor_get(v_opts_590_, 0);
v___x_595_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_594_, v_name_592_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_inc(v_defValue_593_);
return v_defValue_593_;
}
else
{
lean_object* v_val_596_; 
v_val_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_val_596_);
lean_dec_ref_known(v___x_595_, 1);
if (lean_obj_tag(v_val_596_) == 3)
{
lean_object* v_v_597_; 
v_v_597_ = lean_ctor_get(v_val_596_, 0);
lean_inc(v_v_597_);
lean_dec_ref_known(v_val_596_, 1);
return v_v_597_;
}
else
{
lean_dec(v_val_596_);
lean_inc(v_defValue_593_);
return v_defValue_593_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12___boxed(lean_object* v_opts_598_, lean_object* v_opt_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12(v_opts_598_, v_opt_599_);
lean_dec_ref(v_opt_599_);
lean_dec_ref(v_opts_598_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg(lean_object* v_x_601_){
_start:
{
if (lean_obj_tag(v_x_601_) == 0)
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
v_a_603_ = lean_ctor_get(v_x_601_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v_x_601_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v_x_601_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v_x_601_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
lean_ctor_set_tag(v___x_605_, 1);
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
else
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_618_; 
v_a_611_ = lean_ctor_get(v_x_601_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v_x_601_);
if (v_isSharedCheck_618_ == 0)
{
v___x_613_ = v_x_601_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v_x_601_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_616_; 
if (v_isShared_614_ == 0)
{
lean_ctor_set_tag(v___x_613_, 0);
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_a_611_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg___boxed(lean_object* v_x_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg(v_x_619_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9_spec__10(size_t v_sz_622_, size_t v_i_623_, lean_object* v_bs_624_){
_start:
{
uint8_t v___x_625_; 
v___x_625_ = lean_usize_dec_lt(v_i_623_, v_sz_622_);
if (v___x_625_ == 0)
{
return v_bs_624_;
}
else
{
lean_object* v_v_626_; lean_object* v_msg_627_; lean_object* v___x_628_; lean_object* v_bs_x27_629_; size_t v___x_630_; size_t v___x_631_; lean_object* v___x_632_; 
v_v_626_ = lean_array_uget_borrowed(v_bs_624_, v_i_623_);
v_msg_627_ = lean_ctor_get(v_v_626_, 1);
lean_inc_ref(v_msg_627_);
v___x_628_ = lean_unsigned_to_nat(0u);
v_bs_x27_629_ = lean_array_uset(v_bs_624_, v_i_623_, v___x_628_);
v___x_630_ = ((size_t)1ULL);
v___x_631_ = lean_usize_add(v_i_623_, v___x_630_);
v___x_632_ = lean_array_uset(v_bs_x27_629_, v_i_623_, v_msg_627_);
v_i_623_ = v___x_631_;
v_bs_624_ = v___x_632_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9_spec__10___boxed(lean_object* v_sz_634_, lean_object* v_i_635_, lean_object* v_bs_636_){
_start:
{
size_t v_sz_boxed_637_; size_t v_i_boxed_638_; lean_object* v_res_639_; 
v_sz_boxed_637_ = lean_unbox_usize(v_sz_634_);
lean_dec(v_sz_634_);
v_i_boxed_638_ = lean_unbox_usize(v_i_635_);
lean_dec(v_i_635_);
v_res_639_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9_spec__10(v_sz_boxed_637_, v_i_boxed_638_, v_bs_636_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9(lean_object* v_oldTraces_640_, lean_object* v_data_641_, lean_object* v_ref_642_, lean_object* v_msg_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v_toCold_649_; lean_object* v_currRecDepth_650_; lean_object* v_ref_651_; uint16_t v_optionFlags_652_; uint8_t v_suppressElabErrors_653_; uint8_t v_checkDeprecated_654_; uint8_t v_isRecordingDeps_655_; lean_object* v_ref_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v_traceState_659_; lean_object* v_traces_660_; lean_object* v___x_661_; size_t v_sz_662_; size_t v___x_663_; lean_object* v___x_664_; lean_object* v_msg_665_; lean_object* v___x_666_; lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_705_; 
v_toCold_649_ = lean_ctor_get(v___y_646_, 0);
v_currRecDepth_650_ = lean_ctor_get(v___y_646_, 1);
v_ref_651_ = lean_ctor_get(v___y_646_, 2);
v_optionFlags_652_ = lean_ctor_get_uint16(v___y_646_, sizeof(void*)*3);
v_suppressElabErrors_653_ = lean_ctor_get_uint8(v___y_646_, sizeof(void*)*3 + 2);
v_checkDeprecated_654_ = lean_ctor_get_uint8(v___y_646_, sizeof(void*)*3 + 3);
v_isRecordingDeps_655_ = lean_ctor_get_uint8(v___y_646_, sizeof(void*)*3 + 4);
v_ref_656_ = l_Lean_replaceRef(v_ref_642_, v_ref_651_);
lean_inc(v_currRecDepth_650_);
lean_inc_ref(v_toCold_649_);
v___x_657_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_657_, 0, v_toCold_649_);
lean_ctor_set(v___x_657_, 1, v_currRecDepth_650_);
lean_ctor_set(v___x_657_, 2, v_ref_656_);
lean_ctor_set_uint16(v___x_657_, sizeof(void*)*3, v_optionFlags_652_);
lean_ctor_set_uint8(v___x_657_, sizeof(void*)*3 + 2, v_suppressElabErrors_653_);
lean_ctor_set_uint8(v___x_657_, sizeof(void*)*3 + 3, v_checkDeprecated_654_);
lean_ctor_set_uint8(v___x_657_, sizeof(void*)*3 + 4, v_isRecordingDeps_655_);
v___x_658_ = lean_st_ref_get(v___y_647_);
v_traceState_659_ = lean_ctor_get(v___x_658_, 4);
lean_inc_ref(v_traceState_659_);
lean_dec(v___x_658_);
v_traces_660_ = lean_ctor_get(v_traceState_659_, 0);
lean_inc_ref(v_traces_660_);
lean_dec_ref(v_traceState_659_);
v___x_661_ = l_Lean_PersistentArray_toArray___redArg(v_traces_660_);
lean_dec_ref(v_traces_660_);
v_sz_662_ = lean_array_size(v___x_661_);
v___x_663_ = ((size_t)0ULL);
v___x_664_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9_spec__10(v_sz_662_, v___x_663_, v___x_661_);
v_msg_665_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_665_, 0, v_data_641_);
lean_ctor_set(v_msg_665_, 1, v_msg_643_);
lean_ctor_set(v_msg_665_, 2, v___x_664_);
v___x_666_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msg_665_, v___y_644_, v___y_645_, v___x_657_, v___y_647_);
lean_dec_ref_known(v___x_657_, 3);
v_a_667_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_705_ == 0)
{
v___x_669_ = v___x_666_;
v_isShared_670_ = v_isSharedCheck_705_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_666_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_705_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v_traceState_672_; lean_object* v_env_673_; lean_object* v_nextMacroScope_674_; lean_object* v_ngen_675_; lean_object* v_auxDeclNGen_676_; lean_object* v_cache_677_; lean_object* v_recordedDeps_678_; lean_object* v_messages_679_; lean_object* v_infoState_680_; lean_object* v_snapshotTasks_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_704_; 
v___x_671_ = lean_st_ref_take(v___y_647_);
v_traceState_672_ = lean_ctor_get(v___x_671_, 4);
v_env_673_ = lean_ctor_get(v___x_671_, 0);
v_nextMacroScope_674_ = lean_ctor_get(v___x_671_, 1);
v_ngen_675_ = lean_ctor_get(v___x_671_, 2);
v_auxDeclNGen_676_ = lean_ctor_get(v___x_671_, 3);
v_cache_677_ = lean_ctor_get(v___x_671_, 5);
v_recordedDeps_678_ = lean_ctor_get(v___x_671_, 6);
v_messages_679_ = lean_ctor_get(v___x_671_, 7);
v_infoState_680_ = lean_ctor_get(v___x_671_, 8);
v_snapshotTasks_681_ = lean_ctor_get(v___x_671_, 9);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_704_ == 0)
{
v___x_683_ = v___x_671_;
v_isShared_684_ = v_isSharedCheck_704_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_snapshotTasks_681_);
lean_inc(v_infoState_680_);
lean_inc(v_messages_679_);
lean_inc(v_recordedDeps_678_);
lean_inc(v_cache_677_);
lean_inc(v_traceState_672_);
lean_inc(v_auxDeclNGen_676_);
lean_inc(v_ngen_675_);
lean_inc(v_nextMacroScope_674_);
lean_inc(v_env_673_);
lean_dec(v___x_671_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_704_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
uint64_t v_tid_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_702_; 
v_tid_685_ = lean_ctor_get_uint64(v_traceState_672_, sizeof(void*)*1);
v_isSharedCheck_702_ = !lean_is_exclusive(v_traceState_672_);
if (v_isSharedCheck_702_ == 0)
{
lean_object* v_unused_703_; 
v_unused_703_ = lean_ctor_get(v_traceState_672_, 0);
lean_dec(v_unused_703_);
v___x_687_ = v_traceState_672_;
v_isShared_688_ = v_isSharedCheck_702_;
goto v_resetjp_686_;
}
else
{
lean_dec(v_traceState_672_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_702_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_693_; 
v___x_689_ = lean_box(0);
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v_ref_642_);
lean_ctor_set(v___x_690_, 1, v_a_667_);
v___x_691_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_640_, v___x_690_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v___x_691_);
v___x_693_ = v___x_687_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_691_);
lean_ctor_set_uint64(v_reuseFailAlloc_701_, sizeof(void*)*1, v_tid_685_);
v___x_693_ = v_reuseFailAlloc_701_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
lean_object* v___x_695_; 
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 4, v___x_693_);
v___x_695_ = v___x_683_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_env_673_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_nextMacroScope_674_);
lean_ctor_set(v_reuseFailAlloc_700_, 2, v_ngen_675_);
lean_ctor_set(v_reuseFailAlloc_700_, 3, v_auxDeclNGen_676_);
lean_ctor_set(v_reuseFailAlloc_700_, 4, v___x_693_);
lean_ctor_set(v_reuseFailAlloc_700_, 5, v_cache_677_);
lean_ctor_set(v_reuseFailAlloc_700_, 6, v_recordedDeps_678_);
lean_ctor_set(v_reuseFailAlloc_700_, 7, v_messages_679_);
lean_ctor_set(v_reuseFailAlloc_700_, 8, v_infoState_680_);
lean_ctor_set(v_reuseFailAlloc_700_, 9, v_snapshotTasks_681_);
v___x_695_ = v_reuseFailAlloc_700_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
lean_object* v___x_696_; lean_object* v___x_698_; 
v___x_696_ = lean_st_ref_put(v___y_647_, v___x_695_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_689_);
v___x_698_ = v___x_669_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_689_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9___boxed(lean_object* v_oldTraces_706_, lean_object* v_data_707_, lean_object* v_ref_708_, lean_object* v_msg_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9(v_oldTraces_706_, v_data_707_, v_ref_708_, v_msg_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
return v_res_715_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0(void){
_start:
{
lean_object* v___x_716_; double v___x_717_; 
v___x_716_ = lean_unsigned_to_nat(0u);
v___x_717_ = lean_float_of_nat(v___x_716_);
return v___x_717_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2(void){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__1));
v___x_720_ = l_Lean_stringToMessageData(v___x_719_);
return v___x_720_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__3(void){
_start:
{
lean_object* v___x_721_; double v___x_722_; 
v___x_721_ = lean_unsigned_to_nat(1000u);
v___x_722_ = lean_float_of_nat(v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(lean_object* v_cls_723_, uint8_t v_collapsed_724_, lean_object* v_tag_725_, lean_object* v_opts_726_, uint8_t v_clsEnabled_727_, lean_object* v_oldTraces_728_, lean_object* v_msg_729_, lean_object* v_resStartStop_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v_fst_736_; lean_object* v_snd_737_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v_data_741_; lean_object* v_fst_752_; lean_object* v_snd_753_; lean_object* v___x_754_; uint8_t v___x_755_; lean_object* v___y_757_; lean_object* v_a_758_; uint8_t v___y_773_; double v___y_805_; 
v_fst_736_ = lean_ctor_get(v_resStartStop_730_, 0);
lean_inc(v_fst_736_);
v_snd_737_ = lean_ctor_get(v_resStartStop_730_, 1);
lean_inc(v_snd_737_);
lean_dec_ref(v_resStartStop_730_);
v_fst_752_ = lean_ctor_get(v_snd_737_, 0);
lean_inc(v_fst_752_);
v_snd_753_ = lean_ctor_get(v_snd_737_, 1);
lean_inc(v_snd_753_);
lean_dec(v_snd_737_);
v___x_754_ = l_Lean_trace_profiler;
v___x_755_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_opts_726_, v___x_754_);
if (v___x_755_ == 0)
{
v___y_773_ = v___x_755_;
goto v___jp_772_;
}
else
{
lean_object* v___x_810_; uint8_t v___x_811_; 
v___x_810_ = l_Lean_trace_profiler_useHeartbeats;
v___x_811_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_opts_726_, v___x_810_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; lean_object* v___x_813_; double v___x_814_; double v___x_815_; double v___x_816_; 
v___x_812_ = l_Lean_trace_profiler_threshold;
v___x_813_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12(v_opts_726_, v___x_812_);
v___x_814_ = lean_float_of_nat(v___x_813_);
v___x_815_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__3);
v___x_816_ = lean_float_div(v___x_814_, v___x_815_);
v___y_805_ = v___x_816_;
goto v___jp_804_;
}
else
{
lean_object* v___x_817_; lean_object* v___x_818_; double v___x_819_; 
v___x_817_ = l_Lean_trace_profiler_threshold;
v___x_818_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12(v_opts_726_, v___x_817_);
v___x_819_ = lean_float_of_nat(v___x_818_);
v___y_805_ = v___x_819_;
goto v___jp_804_;
}
}
v___jp_738_:
{
lean_object* v___x_742_; 
lean_inc(v___y_740_);
v___x_742_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9(v_oldTraces_728_, v_data_741_, v___y_740_, v___y_739_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v___x_743_; 
lean_dec_ref_known(v___x_742_, 1);
v___x_743_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg(v_fst_736_);
return v___x_743_;
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_dec(v_fst_736_);
v_a_744_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_742_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_742_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
v___jp_756_:
{
uint8_t v_result_759_; lean_object* v___x_760_; lean_object* v___x_761_; double v___x_762_; lean_object* v_data_763_; 
v_result_759_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11(v_fst_736_);
v___x_760_ = lean_box(v_result_759_);
v___x_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
v___x_762_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0);
lean_inc_ref(v_tag_725_);
lean_inc_ref(v___x_761_);
lean_inc(v_cls_723_);
v_data_763_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_763_, 0, v_cls_723_);
lean_ctor_set(v_data_763_, 1, v___x_761_);
lean_ctor_set(v_data_763_, 2, v_tag_725_);
lean_ctor_set_float(v_data_763_, sizeof(void*)*3, v___x_762_);
lean_ctor_set_float(v_data_763_, sizeof(void*)*3 + 8, v___x_762_);
lean_ctor_set_uint8(v_data_763_, sizeof(void*)*3 + 16, v_collapsed_724_);
if (v___x_755_ == 0)
{
lean_dec_ref_known(v___x_761_, 1);
lean_dec(v_snd_753_);
lean_dec(v_fst_752_);
lean_dec_ref(v_tag_725_);
lean_dec(v_cls_723_);
v___y_739_ = v_a_758_;
v___y_740_ = v___y_757_;
v_data_741_ = v_data_763_;
goto v___jp_738_;
}
else
{
lean_object* v_data_764_; double v___x_765_; double v___x_766_; 
lean_dec_ref_known(v_data_763_, 3);
v_data_764_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_764_, 0, v_cls_723_);
lean_ctor_set(v_data_764_, 1, v___x_761_);
lean_ctor_set(v_data_764_, 2, v_tag_725_);
v___x_765_ = lean_unbox_float(v_fst_752_);
lean_dec(v_fst_752_);
lean_ctor_set_float(v_data_764_, sizeof(void*)*3, v___x_765_);
v___x_766_ = lean_unbox_float(v_snd_753_);
lean_dec(v_snd_753_);
lean_ctor_set_float(v_data_764_, sizeof(void*)*3 + 8, v___x_766_);
lean_ctor_set_uint8(v_data_764_, sizeof(void*)*3 + 16, v_collapsed_724_);
v___y_739_ = v_a_758_;
v___y_740_ = v___y_757_;
v_data_741_ = v_data_764_;
goto v___jp_738_;
}
}
v___jp_767_:
{
lean_object* v_ref_768_; lean_object* v___x_769_; 
v_ref_768_ = lean_ctor_get(v___y_733_, 2);
lean_inc(v___y_734_);
lean_inc_ref(v___y_733_);
lean_inc(v___y_732_);
lean_inc_ref(v___y_731_);
lean_inc(v_fst_736_);
v___x_769_ = lean_apply_6(v_msg_729_, v_fst_736_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, lean_box(0));
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_a_770_);
lean_dec_ref_known(v___x_769_, 1);
v___y_757_ = v_ref_768_;
v_a_758_ = v_a_770_;
goto v___jp_756_;
}
else
{
lean_object* v___x_771_; 
lean_dec_ref_known(v___x_769_, 1);
v___x_771_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2);
v___y_757_ = v_ref_768_;
v_a_758_ = v___x_771_;
goto v___jp_756_;
}
}
v___jp_772_:
{
if (v_clsEnabled_727_ == 0)
{
if (v___y_773_ == 0)
{
lean_object* v___x_774_; lean_object* v_traceState_775_; lean_object* v_env_776_; lean_object* v_nextMacroScope_777_; lean_object* v_ngen_778_; lean_object* v_auxDeclNGen_779_; lean_object* v_cache_780_; lean_object* v_recordedDeps_781_; lean_object* v_messages_782_; lean_object* v_infoState_783_; lean_object* v_snapshotTasks_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_803_; 
lean_dec(v_snd_753_);
lean_dec(v_fst_752_);
lean_dec_ref(v_msg_729_);
lean_dec_ref(v_tag_725_);
lean_dec(v_cls_723_);
v___x_774_ = lean_st_ref_take(v___y_734_);
v_traceState_775_ = lean_ctor_get(v___x_774_, 4);
v_env_776_ = lean_ctor_get(v___x_774_, 0);
v_nextMacroScope_777_ = lean_ctor_get(v___x_774_, 1);
v_ngen_778_ = lean_ctor_get(v___x_774_, 2);
v_auxDeclNGen_779_ = lean_ctor_get(v___x_774_, 3);
v_cache_780_ = lean_ctor_get(v___x_774_, 5);
v_recordedDeps_781_ = lean_ctor_get(v___x_774_, 6);
v_messages_782_ = lean_ctor_get(v___x_774_, 7);
v_infoState_783_ = lean_ctor_get(v___x_774_, 8);
v_snapshotTasks_784_ = lean_ctor_get(v___x_774_, 9);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_803_ == 0)
{
v___x_786_ = v___x_774_;
v_isShared_787_ = v_isSharedCheck_803_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_snapshotTasks_784_);
lean_inc(v_infoState_783_);
lean_inc(v_messages_782_);
lean_inc(v_recordedDeps_781_);
lean_inc(v_cache_780_);
lean_inc(v_traceState_775_);
lean_inc(v_auxDeclNGen_779_);
lean_inc(v_ngen_778_);
lean_inc(v_nextMacroScope_777_);
lean_inc(v_env_776_);
lean_dec(v___x_774_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_803_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
uint64_t v_tid_788_; lean_object* v_traces_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_802_; 
v_tid_788_ = lean_ctor_get_uint64(v_traceState_775_, sizeof(void*)*1);
v_traces_789_ = lean_ctor_get(v_traceState_775_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v_traceState_775_);
if (v_isSharedCheck_802_ == 0)
{
v___x_791_ = v_traceState_775_;
v_isShared_792_ = v_isSharedCheck_802_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_traces_789_);
lean_dec(v_traceState_775_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_802_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_793_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_728_, v_traces_789_);
lean_dec_ref(v_traces_789_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_793_);
v___x_795_ = v___x_791_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_793_);
lean_ctor_set_uint64(v_reuseFailAlloc_801_, sizeof(void*)*1, v_tid_788_);
v___x_795_ = v_reuseFailAlloc_801_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
lean_object* v___x_797_; 
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 4, v___x_795_);
v___x_797_ = v___x_786_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_env_776_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_nextMacroScope_777_);
lean_ctor_set(v_reuseFailAlloc_800_, 2, v_ngen_778_);
lean_ctor_set(v_reuseFailAlloc_800_, 3, v_auxDeclNGen_779_);
lean_ctor_set(v_reuseFailAlloc_800_, 4, v___x_795_);
lean_ctor_set(v_reuseFailAlloc_800_, 5, v_cache_780_);
lean_ctor_set(v_reuseFailAlloc_800_, 6, v_recordedDeps_781_);
lean_ctor_set(v_reuseFailAlloc_800_, 7, v_messages_782_);
lean_ctor_set(v_reuseFailAlloc_800_, 8, v_infoState_783_);
lean_ctor_set(v_reuseFailAlloc_800_, 9, v_snapshotTasks_784_);
v___x_797_ = v_reuseFailAlloc_800_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = lean_st_ref_put(v___y_734_, v___x_797_);
v___x_799_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg(v_fst_736_);
return v___x_799_;
}
}
}
}
}
else
{
goto v___jp_767_;
}
}
else
{
goto v___jp_767_;
}
}
v___jp_804_:
{
double v___x_806_; double v___x_807_; double v___x_808_; uint8_t v___x_809_; 
v___x_806_ = lean_unbox_float(v_snd_753_);
v___x_807_ = lean_unbox_float(v_fst_752_);
v___x_808_ = lean_float_sub(v___x_806_, v___x_807_);
v___x_809_ = lean_float_decLt(v___y_805_, v___x_808_);
v___y_773_ = v___x_809_;
goto v___jp_772_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___boxed(lean_object* v_cls_820_, lean_object* v_collapsed_821_, lean_object* v_tag_822_, lean_object* v_opts_823_, lean_object* v_clsEnabled_824_, lean_object* v_oldTraces_825_, lean_object* v_msg_826_, lean_object* v_resStartStop_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
uint8_t v_collapsed_boxed_833_; uint8_t v_clsEnabled_boxed_834_; lean_object* v_res_835_; 
v_collapsed_boxed_833_ = lean_unbox(v_collapsed_821_);
v_clsEnabled_boxed_834_ = lean_unbox(v_clsEnabled_824_);
v_res_835_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v_cls_820_, v_collapsed_boxed_833_, v_tag_822_, v_opts_823_, v_clsEnabled_boxed_834_, v_oldTraces_825_, v_msg_826_, v_resStartStop_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec_ref(v_opts_823_);
return v_res_835_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_849_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5));
v___x_850_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__8));
v___x_851_ = l_Lean_Name_append(v___x_850_, v___x_849_);
return v___x_851_;
}
}
static double _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10(void){
_start:
{
lean_object* v___x_852_; double v___x_853_; 
v___x_852_ = lean_unsigned_to_nat(1000000000u);
v___x_853_ = lean_float_of_nat(v___x_852_);
return v___x_853_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12(void){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_855_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__11));
v___x_856_ = l_Lean_stringToMessageData(v___x_855_);
return v___x_856_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14(void){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__13));
v___x_859_ = l_Lean_stringToMessageData(v___x_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7(lean_object* v_snd_860_, lean_object* v_mvarId_861_, lean_object* v_x_862_, lean_object* v_x_863_, lean_object* v_x_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
if (lean_obj_tag(v_x_862_) == 5)
{
lean_object* v_fn_870_; lean_object* v_arg_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v_fn_870_ = lean_ctor_get(v_x_862_, 0);
lean_inc_ref(v_fn_870_);
v_arg_871_ = lean_ctor_get(v_x_862_, 1);
lean_inc_ref(v_arg_871_);
lean_dec_ref_known(v_x_862_, 2);
v___x_872_ = lean_array_set(v_x_863_, v_x_864_, v_arg_871_);
v___x_873_ = lean_unsigned_to_nat(1u);
v___x_874_ = lean_nat_sub(v_x_864_, v___x_873_);
lean_dec(v_x_864_);
v_x_862_ = v_fn_870_;
v_x_863_ = v___x_872_;
v_x_864_ = v___x_874_;
goto _start;
}
else
{
lean_dec(v_x_864_);
if (lean_obj_tag(v_x_862_) == 4)
{
lean_object* v_declName_876_; lean_object* v___f_877_; lean_object* v___f_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v_declName_876_ = lean_ctor_get(v_x_862_, 0);
lean_inc_n(v_declName_876_, 2);
lean_dec_ref_known(v_x_862_, 2);
v___f_877_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0));
v___f_878_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1));
v___x_879_ = l_Lean_instInhabitedExpr;
v___x_880_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_declName_876_, v___y_868_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_a_881_);
lean_dec_ref_known(v___x_880_, 1);
if (lean_obj_tag(v_a_881_) == 1)
{
lean_object* v_val_882_; lean_object* v_toCold_883_; lean_object* v_options_884_; lean_object* v_majorPos_885_; lean_object* v_arity_886_; lean_object* v_insterestingCtors_887_; lean_object* v_inheritedTraceOptions_888_; uint8_t v_hasTrace_889_; lean_object* v___f_890_; lean_object* v___x_891_; uint8_t v___x_892_; 
v_val_882_ = lean_ctor_get(v_a_881_, 0);
lean_inc(v_val_882_);
lean_dec_ref_known(v_a_881_, 1);
v_toCold_883_ = lean_ctor_get(v___y_867_, 0);
v_options_884_ = lean_ctor_get(v_toCold_883_, 2);
v_majorPos_885_ = lean_ctor_get(v_val_882_, 1);
lean_inc(v_majorPos_885_);
v_arity_886_ = lean_ctor_get(v_val_882_, 2);
lean_inc_n(v_arity_886_, 2);
v_insterestingCtors_887_ = lean_ctor_get(v_val_882_, 3);
lean_inc_ref(v_insterestingCtors_887_);
lean_dec(v_val_882_);
v_inheritedTraceOptions_888_ = lean_ctor_get(v_toCold_883_, 11);
v_hasTrace_889_ = lean_ctor_get_uint8(v_options_884_, sizeof(void*)*1);
lean_inc_ref(v_x_863_);
v___f_890_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___boxed), 15, 9);
lean_closure_set(v___f_890_, 0, v___x_879_);
lean_closure_set(v___f_890_, 1, v_x_863_);
lean_closure_set(v___f_890_, 2, v_majorPos_885_);
lean_closure_set(v___f_890_, 3, v_insterestingCtors_887_);
lean_closure_set(v___f_890_, 4, v_declName_876_);
lean_closure_set(v___f_890_, 5, v_snd_860_);
lean_closure_set(v___f_890_, 6, v_arity_886_);
lean_closure_set(v___f_890_, 7, v_mvarId_861_);
lean_closure_set(v___f_890_, 8, v___f_877_);
v___x_891_ = lean_array_get_size(v_x_863_);
lean_dec_ref(v_x_863_);
v___x_892_ = lean_nat_dec_lt(v___x_891_, v_arity_886_);
lean_dec(v_arity_886_);
if (v_hasTrace_889_ == 0)
{
lean_object* v___x_893_; 
v___x_893_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2(v___x_892_, v___f_890_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
return v___x_893_;
}
else
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; uint8_t v___x_897_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v_a_901_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v_a_916_; 
v___x_894_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5));
v___x_895_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__6));
v___x_896_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9);
v___x_897_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_888_, v_options_884_, v___x_896_);
if (v___x_897_ == 0)
{
lean_object* v___x_966_; uint8_t v___x_967_; 
v___x_966_ = l_Lean_trace_profiler;
v___x_967_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_options_884_, v___x_966_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; 
v___x_968_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2(v___x_892_, v___f_890_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
return v___x_968_;
}
else
{
goto v___jp_925_;
}
}
else
{
goto v___jp_925_;
}
v___jp_898_:
{
lean_object* v___x_902_; double v___x_903_; double v___x_904_; double v___x_905_; double v___x_906_; double v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_902_ = lean_io_mono_nanos_now();
v___x_903_ = lean_float_of_nat(v___y_900_);
v___x_904_ = lean_float_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10);
v___x_905_ = lean_float_div(v___x_903_, v___x_904_);
v___x_906_ = lean_float_of_nat(v___x_902_);
v___x_907_ = lean_float_div(v___x_906_, v___x_904_);
v___x_908_ = lean_box_float(v___x_905_);
v___x_909_ = lean_box_float(v___x_907_);
v___x_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_908_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v_a_901_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_894_, v_hasTrace_889_, v___x_895_, v_options_884_, v___x_897_, v___y_899_, v___f_878_, v___x_911_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
return v___x_912_;
}
v___jp_913_:
{
lean_object* v___x_917_; double v___x_918_; double v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_917_ = lean_io_get_num_heartbeats();
v___x_918_ = lean_float_of_nat(v___y_914_);
v___x_919_ = lean_float_of_nat(v___x_917_);
v___x_920_ = lean_box_float(v___x_918_);
v___x_921_ = lean_box_float(v___x_919_);
v___x_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_920_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_923_, 0, v_a_916_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
v___x_924_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_894_, v_hasTrace_889_, v___x_895_, v_options_884_, v___x_897_, v___y_915_, v___f_878_, v___x_923_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
return v___x_924_;
}
v___jp_925_:
{
lean_object* v___x_926_; lean_object* v_a_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_926_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___y_868_);
v_a_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_a_927_);
lean_dec_ref(v___x_926_);
v___x_928_ = l_Lean_trace_profiler_useHeartbeats;
v___x_929_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_options_884_, v___x_928_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = lean_io_mono_nanos_now();
v___x_931_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2(v___x_892_, v___f_890_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
v_a_932_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___x_931_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_931_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
lean_ctor_set_tag(v___x_934_, 1);
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_932_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
v___y_899_ = v_a_927_;
v___y_900_ = v___x_930_;
v_a_901_ = v___x_937_;
goto v___jp_898_;
}
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
v_a_940_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_931_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_931_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
lean_ctor_set_tag(v___x_942_, 0);
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
v___y_899_ = v_a_927_;
v___y_900_ = v___x_930_;
v_a_901_ = v___x_945_;
goto v___jp_898_;
}
}
}
}
else
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = lean_io_get_num_heartbeats();
v___x_949_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2(v___x_892_, v___f_890_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_949_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_949_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
lean_ctor_set_tag(v___x_952_, 1);
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
v___y_914_ = v___x_948_;
v___y_915_ = v_a_927_;
v_a_916_ = v___x_955_;
goto v___jp_913_;
}
}
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
v_a_958_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_949_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_949_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
lean_ctor_set_tag(v___x_960_, 0);
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
v___y_914_ = v___x_948_;
v___y_915_ = v_a_927_;
v_a_916_ = v___x_963_;
goto v___jp_913_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_969_; lean_object* v___x_970_; 
lean_dec(v_a_881_);
lean_dec(v_declName_876_);
lean_dec_ref(v_x_863_);
lean_dec(v_mvarId_861_);
lean_dec_ref(v_snd_860_);
v___x_969_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12);
v___x_970_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_969_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
return v___x_970_;
}
}
else
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_978_; 
lean_dec(v_declName_876_);
lean_dec_ref(v_x_863_);
lean_dec(v_mvarId_861_);
lean_dec_ref(v_snd_860_);
v_a_971_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_978_ == 0)
{
v___x_973_ = v___x_880_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_880_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_976_; 
if (v_isShared_974_ == 0)
{
v___x_976_ = v___x_973_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_a_971_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
else
{
lean_object* v___x_979_; lean_object* v___x_980_; 
lean_dec_ref(v_x_863_);
lean_dec_ref(v_x_862_);
lean_dec(v_mvarId_861_);
lean_dec_ref(v_snd_860_);
v___x_979_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14);
v___x_980_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_979_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
return v___x_980_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___boxed(lean_object* v_snd_981_, lean_object* v_mvarId_982_, lean_object* v_x_983_, lean_object* v_x_984_, lean_object* v_x_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7(v_snd_981_, v_mvarId_982_, v_x_983_, v_x_984_, v_x_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
return v_res_991_;
}
}
static lean_object* _init_l_Lean_Meta_reduceSparseCasesOn___closed__1(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = ((lean_object*)(l_Lean_Meta_reduceSparseCasesOn___closed__0));
v___x_994_ = l_Lean_stringToMessageData(v___x_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceSparseCasesOn(lean_object* v_mvarId_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_){
_start:
{
lean_object* v___x_1001_; 
lean_inc(v_mvarId_995_);
v___x_1001_ = l_Lean_MVarId_getType(v_mvarId_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1003_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1002_);
lean_dec_ref_known(v___x_1001_, 1);
v___x_1003_ = l_Lean_Meta_matchEqHEqLHS_x3f(v_a_1002_, v_a_996_, v_a_997_, v_a_998_, v_a_999_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1003_, 1);
if (lean_obj_tag(v_a_1004_) == 1)
{
lean_object* v_val_1005_; lean_object* v_snd_1006_; lean_object* v_dummy_1007_; lean_object* v_nargs_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v_val_1005_ = lean_ctor_get(v_a_1004_, 0);
lean_inc(v_val_1005_);
lean_dec_ref_known(v_a_1004_, 1);
v_snd_1006_ = lean_ctor_get(v_val_1005_, 1);
lean_inc_n(v_snd_1006_, 2);
lean_dec(v_val_1005_);
v_dummy_1007_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0);
v_nargs_1008_ = l_Lean_Expr_getAppNumArgs(v_snd_1006_);
lean_inc(v_nargs_1008_);
v___x_1009_ = lean_mk_array(v_nargs_1008_, v_dummy_1007_);
v___x_1010_ = lean_unsigned_to_nat(1u);
v___x_1011_ = lean_nat_sub(v_nargs_1008_, v___x_1010_);
lean_dec(v_nargs_1008_);
v___x_1012_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7(v_snd_1006_, v_mvarId_995_, v_snd_1006_, v___x_1009_, v___x_1011_, v_a_996_, v_a_997_, v_a_998_, v_a_999_);
return v___x_1012_;
}
else
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
lean_dec(v_a_1004_);
lean_dec(v_mvarId_995_);
v___x_1013_ = lean_obj_once(&l_Lean_Meta_reduceSparseCasesOn___closed__1, &l_Lean_Meta_reduceSparseCasesOn___closed__1_once, _init_l_Lean_Meta_reduceSparseCasesOn___closed__1);
v___x_1014_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1013_, v_a_996_, v_a_997_, v_a_998_, v_a_999_);
return v___x_1014_;
}
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
lean_dec(v_mvarId_995_);
v_a_1015_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_1003_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1003_);
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
lean_dec(v_mvarId_995_);
v_a_1023_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_1001_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1001_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_reduceSparseCasesOn___boxed(lean_object* v_mvarId_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_Meta_reduceSparseCasesOn(v_mvarId_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_);
lean_dec(v_a_1035_);
lean_dec_ref(v_a_1034_);
lean_dec(v_a_1033_);
lean_dec_ref(v_a_1032_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3(lean_object* v_00_u03b1_1038_, lean_object* v_msg_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v_msg_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___boxed(lean_object* v_00_u03b1_1046_, lean_object* v_msg_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3(v_00_u03b1_1046_, v_msg_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10(lean_object* v_00_u03b1_1054_, lean_object* v_x_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg(v_x_1055_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___boxed(lean_object* v_00_u03b1_1062_, lean_object* v_x_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10(v_00_u03b1_1062_, v_x_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(lean_object* v_mvarId_1070_, lean_object* v_x_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1070_, v_x_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1077_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1077_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
v_a_1086_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___x_1077_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1077_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg___boxed(lean_object* v_mvarId_1094_, lean_object* v_x_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1094_, v_x_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2(lean_object* v_00_u03b1_1102_, lean_object* v_mvarId_1103_, lean_object* v_x_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1103_, v_x_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___boxed(lean_object* v_00_u03b1_1111_, lean_object* v_mvarId_1112_, lean_object* v_x_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2(v_00_u03b1_1111_, v_mvarId_1112_, v_x_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_splitSparseCasesOn_spec__1(lean_object* v_a_1120_, lean_object* v_a_1121_){
_start:
{
if (lean_obj_tag(v_a_1120_) == 0)
{
lean_object* v___x_1122_; 
v___x_1122_ = l_List_reverse___redArg(v_a_1121_);
return v___x_1122_;
}
else
{
lean_object* v_head_1123_; lean_object* v_tail_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1133_; 
v_head_1123_ = lean_ctor_get(v_a_1120_, 0);
v_tail_1124_ = lean_ctor_get(v_a_1120_, 1);
v_isSharedCheck_1133_ = !lean_is_exclusive(v_a_1120_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1126_ = v_a_1120_;
v_isShared_1127_ = v_isSharedCheck_1133_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_tail_1124_);
lean_inc(v_head_1123_);
lean_dec(v_a_1120_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1133_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1128_; lean_object* v___x_1130_; 
v___x_1128_ = l_Lean_MessageData_ofExpr(v_head_1123_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 1, v_a_1121_);
lean_ctor_set(v___x_1126_, 0, v___x_1128_);
v___x_1130_ = v___x_1126_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1128_);
lean_ctor_set(v_reuseFailAlloc_1132_, 1, v_a_1121_);
v___x_1130_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
v_a_1120_ = v_tail_1124_;
v_a_1121_ = v___x_1130_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__0));
v___x_1136_ = l_Lean_stringToMessageData(v___x_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0(uint8_t v___y_1137_, lean_object* v_mvarId_1138_, lean_object* v___f_1139_, lean_object* v_declName_1140_, lean_object* v_val_1141_, lean_object* v___x_1142_, lean_object* v_fields_1143_, uint8_t v___x_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; 
if (v___y_1137_ == 0)
{
lean_object* v___x_1206_; 
lean_dec_ref(v_fields_1143_);
lean_dec_ref(v_val_1141_);
lean_dec(v_declName_1140_);
v___x_1206_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_1138_, v___f_1139_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
return v___x_1206_;
}
else
{
lean_object* v___x_1207_; lean_object* v___x_1208_; uint8_t v___x_1209_; 
lean_dec_ref(v___f_1139_);
v___x_1207_ = lean_array_get_size(v_fields_1143_);
v___x_1208_ = lean_unsigned_to_nat(1u);
v___x_1209_ = lean_nat_dec_eq(v___x_1207_, v___x_1208_);
if (v___x_1209_ == 0)
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1210_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1);
lean_inc_ref(v_fields_1143_);
v___x_1211_ = lean_array_to_list(v_fields_1143_);
v___x_1212_ = lean_box(0);
v___x_1213_ = l_List_mapTR_loop___at___00Lean_Meta_splitSparseCasesOn_spec__1(v___x_1211_, v___x_1212_);
v___x_1214_ = l_Lean_MessageData_ofList(v___x_1213_);
v___x_1215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1210_);
lean_ctor_set(v___x_1215_, 1, v___x_1214_);
v___x_1216_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1215_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_dec_ref_known(v___x_1216_, 1);
v___y_1151_ = v___y_1145_;
v___y_1152_ = v___y_1146_;
v___y_1153_ = v___y_1147_;
v___y_1154_ = v___y_1148_;
goto v___jp_1150_;
}
else
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
lean_dec_ref(v_fields_1143_);
lean_dec_ref(v_val_1141_);
lean_dec(v_declName_1140_);
lean_dec(v_mvarId_1138_);
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1216_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1216_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
else
{
v___y_1151_ = v___y_1145_;
v___y_1152_ = v___y_1146_;
v___y_1153_ = v___y_1147_;
v___y_1154_ = v___y_1148_;
goto v___jp_1150_;
}
}
v___jp_1150_:
{
lean_object* v___x_1155_; 
v___x_1155_ = l_Lean_Meta_getSparseCasesOnEq(v_declName_1140_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_a_1156_; lean_object* v___x_1157_; 
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_a_1156_);
lean_dec_ref_known(v___x_1155_, 1);
lean_inc(v_mvarId_1138_);
v___x_1157_ = l_Lean_MVarId_getType(v_mvarId_1138_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; lean_object* v___x_1159_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_a_1158_);
lean_dec_ref_known(v___x_1157_, 1);
v___x_1159_ = l_Lean_Meta_matchEqHEqLHS_x3f(v_a_1158_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1160_; 
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_a_1160_);
lean_dec_ref_known(v___x_1159_, 1);
if (lean_obj_tag(v_a_1160_) == 1)
{
lean_object* v_val_1161_; lean_object* v_snd_1162_; lean_object* v_arity_1163_; lean_object* v___x_1164_; lean_object* v_nargs_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v_dummy_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v_val_1161_ = lean_ctor_get(v_a_1160_, 0);
lean_inc(v_val_1161_);
lean_dec_ref_known(v_a_1160_, 1);
v_snd_1162_ = lean_ctor_get(v_val_1161_, 1);
lean_inc(v_snd_1162_);
lean_dec(v_val_1161_);
v_arity_1163_ = lean_ctor_get(v_val_1141_, 2);
lean_inc(v_arity_1163_);
lean_dec_ref(v_val_1141_);
v___x_1164_ = l_Lean_Expr_getAppFn(v_snd_1162_);
v_nargs_1165_ = l_Lean_Expr_getAppNumArgs(v_snd_1162_);
v___x_1166_ = l_Lean_Expr_constLevels_x21(v___x_1164_);
lean_dec_ref(v___x_1164_);
v___x_1167_ = l_Lean_mkConst(v_a_1156_, v___x_1166_);
v_dummy_1168_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0);
lean_inc(v_nargs_1165_);
v___x_1169_ = lean_mk_array(v_nargs_1165_, v_dummy_1168_);
v___x_1170_ = lean_unsigned_to_nat(1u);
v___x_1171_ = lean_nat_sub(v_nargs_1165_, v___x_1170_);
lean_dec(v_nargs_1165_);
v___x_1172_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_snd_1162_, v___x_1169_, v___x_1171_);
v___x_1173_ = lean_unsigned_to_nat(0u);
v___x_1174_ = l_Array_toSubarray___redArg(v___x_1172_, v___x_1173_, v_arity_1163_);
v___x_1175_ = l_Subarray_copy___redArg(v___x_1174_);
v___x_1176_ = l_Lean_mkAppN(v___x_1167_, v___x_1175_);
lean_dec_ref(v___x_1175_);
v___x_1177_ = lean_array_get(v___x_1142_, v_fields_1143_, v___x_1173_);
lean_dec_ref(v_fields_1143_);
v___x_1178_ = l_Lean_Expr_app___override(v___x_1176_, v___x_1177_);
v___x_1179_ = l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq(v_mvarId_1138_, v___x_1178_, v___x_1144_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
return v___x_1179_;
}
else
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
lean_dec(v_a_1160_);
lean_dec(v_a_1156_);
lean_dec_ref(v_fields_1143_);
lean_dec_ref(v_val_1141_);
lean_dec(v_mvarId_1138_);
v___x_1180_ = lean_obj_once(&l_Lean_Meta_reduceSparseCasesOn___closed__1, &l_Lean_Meta_reduceSparseCasesOn___closed__1_once, _init_l_Lean_Meta_reduceSparseCasesOn___closed__1);
v___x_1181_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1180_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
return v___x_1181_;
}
}
else
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1189_; 
lean_dec(v_a_1156_);
lean_dec_ref(v_fields_1143_);
lean_dec_ref(v_val_1141_);
lean_dec(v_mvarId_1138_);
v_a_1182_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1184_ = v___x_1159_;
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1159_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1187_; 
if (v_isShared_1185_ == 0)
{
v___x_1187_ = v___x_1184_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_a_1182_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
else
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1197_; 
lean_dec(v_a_1156_);
lean_dec_ref(v_fields_1143_);
lean_dec_ref(v_val_1141_);
lean_dec(v_mvarId_1138_);
v_a_1190_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1192_ = v___x_1157_;
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1157_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
if (v_isShared_1193_ == 0)
{
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1190_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
else
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
lean_dec_ref(v_fields_1143_);
lean_dec_ref(v_val_1141_);
lean_dec(v_mvarId_1138_);
v_a_1198_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1155_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1155_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1198_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed(lean_object* v___y_1225_, lean_object* v_mvarId_1226_, lean_object* v___f_1227_, lean_object* v_declName_1228_, lean_object* v_val_1229_, lean_object* v___x_1230_, lean_object* v_fields_1231_, lean_object* v___x_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
uint8_t v___y_31214__boxed_1238_; uint8_t v___x_31219__boxed_1239_; lean_object* v_res_1240_; 
v___y_31214__boxed_1238_ = lean_unbox(v___y_1225_);
v___x_31219__boxed_1239_ = lean_unbox(v___x_1232_);
v_res_1240_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0(v___y_31214__boxed_1238_, v_mvarId_1226_, v___f_1227_, v_declName_1228_, v_val_1229_, v___x_1230_, v_fields_1231_, v___x_31219__boxed_1239_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec_ref(v___x_1230_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(lean_object* v_declName_1241_, lean_object* v_val_1242_, uint8_t v___x_1243_, size_t v_sz_1244_, size_t v_i_1245_, lean_object* v_bs_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
uint8_t v___x_1252_; 
v___x_1252_ = lean_usize_dec_lt(v_i_1245_, v_sz_1244_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; 
lean_dec_ref(v_val_1242_);
lean_dec(v_declName_1241_);
v___x_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1253_, 0, v_bs_1246_);
return v___x_1253_;
}
else
{
lean_object* v_v_1254_; lean_object* v_toInductionSubgoal_1255_; lean_object* v_ctorName_1256_; lean_object* v_mvarId_1257_; lean_object* v_fields_1258_; lean_object* v___f_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v_bs_x27_1262_; uint8_t v___y_1264_; 
v_v_1254_ = lean_array_uget_borrowed(v_bs_1246_, v_i_1245_);
v_toInductionSubgoal_1255_ = lean_ctor_get(v_v_1254_, 0);
v_ctorName_1256_ = lean_ctor_get(v_v_1254_, 1);
lean_inc(v_ctorName_1256_);
v_mvarId_1257_ = lean_ctor_get(v_toInductionSubgoal_1255_, 0);
lean_inc(v_mvarId_1257_);
v_fields_1258_ = lean_ctor_get(v_toInductionSubgoal_1255_, 1);
lean_inc_ref(v_fields_1258_);
v___f_1259_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0));
v___x_1260_ = l_Lean_instInhabitedExpr;
v___x_1261_ = lean_unsigned_to_nat(0u);
v_bs_x27_1262_ = lean_array_uset(v_bs_1246_, v_i_1245_, v___x_1261_);
if (lean_obj_tag(v_ctorName_1256_) == 0)
{
v___y_1264_ = v___x_1252_;
goto v___jp_1263_;
}
else
{
lean_dec_ref_known(v_ctorName_1256_, 1);
v___y_1264_ = v___x_1243_;
goto v___jp_1263_;
}
v___jp_1263_:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___y_1267_; lean_object* v___x_1268_; 
v___x_1265_ = lean_box(v___y_1264_);
v___x_1266_ = lean_box(v___x_1243_);
lean_inc_ref(v_val_1242_);
lean_inc(v_declName_1241_);
lean_inc(v_mvarId_1257_);
v___y_1267_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed), 13, 8);
lean_closure_set(v___y_1267_, 0, v___x_1265_);
lean_closure_set(v___y_1267_, 1, v_mvarId_1257_);
lean_closure_set(v___y_1267_, 2, v___f_1259_);
lean_closure_set(v___y_1267_, 3, v_declName_1241_);
lean_closure_set(v___y_1267_, 4, v_val_1242_);
lean_closure_set(v___y_1267_, 5, v___x_1260_);
lean_closure_set(v___y_1267_, 6, v_fields_1258_);
lean_closure_set(v___y_1267_, 7, v___x_1266_);
v___x_1268_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1257_, v___y_1267_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; size_t v___x_1270_; size_t v___x_1271_; lean_object* v___x_1272_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_a_1269_);
lean_dec_ref_known(v___x_1268_, 1);
v___x_1270_ = ((size_t)1ULL);
v___x_1271_ = lean_usize_add(v_i_1245_, v___x_1270_);
v___x_1272_ = lean_array_uset(v_bs_x27_1262_, v_i_1245_, v_a_1269_);
v_i_1245_ = v___x_1271_;
v_bs_1246_ = v___x_1272_;
goto _start;
}
else
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
lean_dec_ref(v_bs_x27_1262_);
lean_dec_ref(v_val_1242_);
lean_dec(v_declName_1241_);
v_a_1274_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v___x_1268_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1268_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1274_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___boxed(lean_object* v_declName_1282_, lean_object* v_val_1283_, lean_object* v___x_1284_, lean_object* v_sz_1285_, lean_object* v_i_1286_, lean_object* v_bs_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
uint8_t v___x_31398__boxed_1293_; size_t v_sz_boxed_1294_; size_t v_i_boxed_1295_; lean_object* v_res_1296_; 
v___x_31398__boxed_1293_ = lean_unbox(v___x_1284_);
v_sz_boxed_1294_ = lean_unbox_usize(v_sz_1285_);
lean_dec(v_sz_1285_);
v_i_boxed_1295_ = lean_unbox_usize(v_i_1286_);
lean_dec(v_i_1286_);
v_res_1296_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(v_declName_1282_, v_val_1283_, v___x_31398__boxed_1293_, v_sz_boxed_1294_, v_i_boxed_1295_, v_bs_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(lean_object* v___x_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v_toCold_1303_; lean_object* v_options_1304_; uint8_t v_hasTrace_1305_; 
v_toCold_1303_ = lean_ctor_get(v___y_1300_, 0);
v_options_1304_ = lean_ctor_get(v_toCold_1303_, 2);
v_hasTrace_1305_ = lean_ctor_get_uint8(v_options_1304_, sizeof(void*)*1);
if (v_hasTrace_1305_ == 0)
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
lean_dec(v___x_1297_);
v___x_1306_ = lean_box(v_hasTrace_1305_);
v___x_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
return v___x_1307_;
}
else
{
lean_object* v_inheritedTraceOptions_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; uint8_t v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v_inheritedTraceOptions_1308_ = lean_ctor_get(v_toCold_1303_, 11);
v___x_1309_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__8));
v___x_1310_ = l_Lean_Name_append(v___x_1309_, v___x_1297_);
v___x_1311_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1308_, v_options_1304_, v___x_1310_);
lean_dec(v___x_1310_);
v___x_1312_ = lean_box(v___x_1311_);
v___x_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
return v___x_1313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___boxed(lean_object* v___x_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(v___x_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(lean_object* v_cls_1323_, lean_object* v_msg_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v_ref_1330_; lean_object* v___x_1331_; lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1377_; 
v_ref_1330_ = lean_ctor_get(v___y_1327_, 2);
v___x_1331_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msg_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1334_ = v___x_1331_;
v_isShared_1335_ = v_isSharedCheck_1377_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1331_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1377_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1336_; lean_object* v_traceState_1337_; lean_object* v_env_1338_; lean_object* v_nextMacroScope_1339_; lean_object* v_ngen_1340_; lean_object* v_auxDeclNGen_1341_; lean_object* v_cache_1342_; lean_object* v_recordedDeps_1343_; lean_object* v_messages_1344_; lean_object* v_infoState_1345_; lean_object* v_snapshotTasks_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1376_; 
v___x_1336_ = lean_st_ref_take(v___y_1328_);
v_traceState_1337_ = lean_ctor_get(v___x_1336_, 4);
v_env_1338_ = lean_ctor_get(v___x_1336_, 0);
v_nextMacroScope_1339_ = lean_ctor_get(v___x_1336_, 1);
v_ngen_1340_ = lean_ctor_get(v___x_1336_, 2);
v_auxDeclNGen_1341_ = lean_ctor_get(v___x_1336_, 3);
v_cache_1342_ = lean_ctor_get(v___x_1336_, 5);
v_recordedDeps_1343_ = lean_ctor_get(v___x_1336_, 6);
v_messages_1344_ = lean_ctor_get(v___x_1336_, 7);
v_infoState_1345_ = lean_ctor_get(v___x_1336_, 8);
v_snapshotTasks_1346_ = lean_ctor_get(v___x_1336_, 9);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1348_ = v___x_1336_;
v_isShared_1349_ = v_isSharedCheck_1376_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_snapshotTasks_1346_);
lean_inc(v_infoState_1345_);
lean_inc(v_messages_1344_);
lean_inc(v_recordedDeps_1343_);
lean_inc(v_cache_1342_);
lean_inc(v_traceState_1337_);
lean_inc(v_auxDeclNGen_1341_);
lean_inc(v_ngen_1340_);
lean_inc(v_nextMacroScope_1339_);
lean_inc(v_env_1338_);
lean_dec(v___x_1336_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1376_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
uint64_t v_tid_1350_; lean_object* v_traces_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1375_; 
v_tid_1350_ = lean_ctor_get_uint64(v_traceState_1337_, sizeof(void*)*1);
v_traces_1351_ = lean_ctor_get(v_traceState_1337_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v_traceState_1337_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1353_ = v_traceState_1337_;
v_isShared_1354_ = v_isSharedCheck_1375_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_traces_1351_);
lean_dec(v_traceState_1337_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1375_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; double v___x_1357_; uint8_t v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1366_; 
v___x_1355_ = lean_box(0);
v___x_1356_ = lean_box(0);
v___x_1357_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0);
v___x_1358_ = 0;
v___x_1359_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__6));
v___x_1360_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1360_, 0, v_cls_1323_);
lean_ctor_set(v___x_1360_, 1, v___x_1356_);
lean_ctor_set(v___x_1360_, 2, v___x_1359_);
lean_ctor_set_float(v___x_1360_, sizeof(void*)*3, v___x_1357_);
lean_ctor_set_float(v___x_1360_, sizeof(void*)*3 + 8, v___x_1357_);
lean_ctor_set_uint8(v___x_1360_, sizeof(void*)*3 + 16, v___x_1358_);
v___x_1361_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___closed__0));
v___x_1362_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1360_);
lean_ctor_set(v___x_1362_, 1, v_a_1332_);
lean_ctor_set(v___x_1362_, 2, v___x_1361_);
lean_inc(v_ref_1330_);
v___x_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1363_, 0, v_ref_1330_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
v___x_1364_ = l_Lean_PersistentArray_push___redArg(v_traces_1351_, v___x_1363_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 0, v___x_1364_);
v___x_1366_ = v___x_1353_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1364_);
lean_ctor_set_uint64(v_reuseFailAlloc_1374_, sizeof(void*)*1, v_tid_1350_);
v___x_1366_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
lean_object* v___x_1368_; 
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 4, v___x_1366_);
v___x_1368_ = v___x_1348_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_env_1338_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_nextMacroScope_1339_);
lean_ctor_set(v_reuseFailAlloc_1373_, 2, v_ngen_1340_);
lean_ctor_set(v_reuseFailAlloc_1373_, 3, v_auxDeclNGen_1341_);
lean_ctor_set(v_reuseFailAlloc_1373_, 4, v___x_1366_);
lean_ctor_set(v_reuseFailAlloc_1373_, 5, v_cache_1342_);
lean_ctor_set(v_reuseFailAlloc_1373_, 6, v_recordedDeps_1343_);
lean_ctor_set(v_reuseFailAlloc_1373_, 7, v_messages_1344_);
lean_ctor_set(v_reuseFailAlloc_1373_, 8, v_infoState_1345_);
lean_ctor_set(v_reuseFailAlloc_1373_, 9, v_snapshotTasks_1346_);
v___x_1368_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
lean_object* v___x_1369_; lean_object* v___x_1371_; 
v___x_1369_ = lean_st_ref_put(v___y_1328_, v___x_1368_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v___x_1355_);
v___x_1371_ = v___x_1334_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1355_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___boxed(lean_object* v_cls_1378_, lean_object* v_msg_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v_cls_1378_, v_msg_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(lean_object* v_declName_1386_, lean_object* v_val_1387_, uint8_t v___x_1388_, size_t v_sz_1389_, size_t v_i_1390_, lean_object* v_bs_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
uint8_t v___x_1397_; 
v___x_1397_ = lean_usize_dec_lt(v_i_1390_, v_sz_1389_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1398_; 
lean_dec_ref(v_val_1387_);
lean_dec(v_declName_1386_);
v___x_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1398_, 0, v_bs_1391_);
return v___x_1398_;
}
else
{
lean_object* v_v_1399_; lean_object* v_toInductionSubgoal_1400_; lean_object* v_ctorName_1401_; lean_object* v_mvarId_1402_; lean_object* v_fields_1403_; lean_object* v___f_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; lean_object* v___x_1407_; lean_object* v_bs_x27_1408_; uint8_t v___y_1410_; 
v_v_1399_ = lean_array_uget_borrowed(v_bs_1391_, v_i_1390_);
v_toInductionSubgoal_1400_ = lean_ctor_get(v_v_1399_, 0);
v_ctorName_1401_ = lean_ctor_get(v_v_1399_, 1);
lean_inc(v_ctorName_1401_);
v_mvarId_1402_ = lean_ctor_get(v_toInductionSubgoal_1400_, 0);
lean_inc(v_mvarId_1402_);
v_fields_1403_ = lean_ctor_get(v_toInductionSubgoal_1400_, 1);
lean_inc_ref(v_fields_1403_);
v___f_1404_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0));
v___x_1405_ = l_Lean_instInhabitedExpr;
v___x_1406_ = 0;
v___x_1407_ = lean_unsigned_to_nat(0u);
v_bs_x27_1408_ = lean_array_uset(v_bs_1391_, v_i_1390_, v___x_1407_);
if (lean_obj_tag(v_ctorName_1401_) == 0)
{
v___y_1410_ = v___x_1388_;
goto v___jp_1409_;
}
else
{
lean_dec_ref_known(v_ctorName_1401_, 1);
v___y_1410_ = v___x_1406_;
goto v___jp_1409_;
}
v___jp_1409_:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___y_1413_; lean_object* v___x_1414_; 
v___x_1411_ = lean_box(v___y_1410_);
v___x_1412_ = lean_box(v___x_1406_);
lean_inc_ref(v_val_1387_);
lean_inc(v_declName_1386_);
lean_inc(v_mvarId_1402_);
v___y_1413_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed), 13, 8);
lean_closure_set(v___y_1413_, 0, v___x_1411_);
lean_closure_set(v___y_1413_, 1, v_mvarId_1402_);
lean_closure_set(v___y_1413_, 2, v___f_1404_);
lean_closure_set(v___y_1413_, 3, v_declName_1386_);
lean_closure_set(v___y_1413_, 4, v_val_1387_);
lean_closure_set(v___y_1413_, 5, v___x_1405_);
lean_closure_set(v___y_1413_, 6, v_fields_1403_);
lean_closure_set(v___y_1413_, 7, v___x_1412_);
v___x_1414_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1402_, v___y_1413_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; size_t v___x_1416_; size_t v___x_1417_; lean_object* v___x_1418_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_a_1415_);
lean_dec_ref_known(v___x_1414_, 1);
v___x_1416_ = ((size_t)1ULL);
v___x_1417_ = lean_usize_add(v_i_1390_, v___x_1416_);
v___x_1418_ = lean_array_uset(v_bs_x27_1408_, v_i_1390_, v_a_1415_);
v_i_1390_ = v___x_1417_;
v_bs_1391_ = v___x_1418_;
goto _start;
}
else
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
lean_dec_ref(v_bs_x27_1408_);
lean_dec_ref(v_val_1387_);
lean_dec(v_declName_1386_);
v_a_1420_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v___x_1414_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1414_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4___boxed(lean_object* v_declName_1428_, lean_object* v_val_1429_, lean_object* v___x_1430_, lean_object* v_sz_1431_, lean_object* v_i_1432_, lean_object* v_bs_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
uint8_t v___x_31603__boxed_1439_; size_t v_sz_boxed_1440_; size_t v_i_boxed_1441_; lean_object* v_res_1442_; 
v___x_31603__boxed_1439_ = lean_unbox(v___x_1430_);
v_sz_boxed_1440_ = lean_unbox_usize(v_sz_1431_);
lean_dec(v_sz_1431_);
v_i_boxed_1441_ = lean_unbox_usize(v_i_1432_);
lean_dec(v_i_1432_);
v_res_1442_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(v_declName_1428_, v_val_1429_, v___x_31603__boxed_1439_, v_sz_boxed_1440_, v_i_boxed_1441_, v_bs_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
return v_res_1442_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__1));
v___x_1447_ = l_Lean_stringToMessageData(v___x_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(lean_object* v_val_1448_, lean_object* v___x_1449_, lean_object* v_x_1450_, lean_object* v_mvarId_1451_, lean_object* v_declName_1452_, uint8_t v___x_1453_, lean_object* v_____r_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v_majorPos_1485_; lean_object* v_arity_1486_; lean_object* v_insterestingCtors_1487_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v___x_1507_; uint8_t v___x_1508_; 
v_majorPos_1485_ = lean_ctor_get(v_val_1448_, 1);
v_arity_1486_ = lean_ctor_get(v_val_1448_, 2);
v_insterestingCtors_1487_ = lean_ctor_get(v_val_1448_, 3);
v___x_1507_ = lean_array_get_size(v_x_1450_);
v___x_1508_ = lean_nat_dec_lt(v___x_1507_, v_arity_1486_);
if (v___x_1508_ == 0)
{
v___y_1489_ = v___y_1455_;
v___y_1490_ = v___y_1456_;
v___y_1491_ = v___y_1457_;
v___y_1492_ = v___y_1458_;
goto v___jp_1488_;
}
else
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
lean_dec(v_declName_1452_);
lean_dec(v_mvarId_1451_);
lean_dec_ref(v_val_1448_);
v___x_1509_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1);
v___x_1510_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1509_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1513_ = v___x_1510_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1510_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
v___jp_1460_:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; uint8_t v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1467_ = lean_array_get_borrowed(v___x_1449_, v_x_1450_, v___y_1462_);
lean_dec(v___y_1462_);
v___x_1468_ = l_Lean_Expr_fvarId_x21(v___x_1467_);
v___x_1469_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__0));
v___x_1470_ = 0;
v___x_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1471_, 0, v___y_1461_);
v___x_1472_ = l_Lean_MVarId_cases(v_mvarId_1451_, v___x_1468_, v___x_1469_, v___x_1470_, v___x_1471_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; size_t v_sz_1474_; size_t v___x_1475_; lean_object* v___x_1476_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_a_1473_);
lean_dec_ref_known(v___x_1472_, 1);
v_sz_1474_ = lean_array_size(v_a_1473_);
v___x_1475_ = ((size_t)0ULL);
v___x_1476_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(v_declName_1452_, v_val_1448_, v___x_1453_, v_sz_1474_, v___x_1475_, v_a_1473_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
return v___x_1476_;
}
else
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1484_; 
lean_dec(v_declName_1452_);
lean_dec_ref(v_val_1448_);
v_a_1477_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1479_ = v___x_1472_;
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1472_);
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
v___jp_1488_:
{
lean_object* v___x_1493_; uint8_t v___x_1494_; 
v___x_1493_ = lean_array_get_borrowed(v___x_1449_, v_x_1450_, v_majorPos_1485_);
v___x_1494_ = l_Lean_Expr_isFVar(v___x_1493_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1506_; 
lean_dec(v_declName_1452_);
lean_dec(v_mvarId_1451_);
lean_dec_ref(v_val_1448_);
v___x_1495_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__2);
lean_inc(v___x_1493_);
v___x_1496_ = l_Lean_indentExpr(v___x_1493_);
v___x_1497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1495_);
lean_ctor_set(v___x_1497_, 1, v___x_1496_);
v___x_1498_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1497_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1501_ = v___x_1498_;
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1498_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1504_; 
if (v_isShared_1502_ == 0)
{
v___x_1504_ = v___x_1501_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
else
{
lean_inc(v_majorPos_1485_);
lean_inc_ref(v_insterestingCtors_1487_);
v___y_1461_ = v_insterestingCtors_1487_;
v___y_1462_ = v_majorPos_1485_;
v___y_1463_ = v___y_1489_;
v___y_1464_ = v___y_1490_;
v___y_1465_ = v___y_1491_;
v___y_1466_ = v___y_1492_;
goto v___jp_1460_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___boxed(lean_object* v_val_1519_, lean_object* v___x_1520_, lean_object* v_x_1521_, lean_object* v_mvarId_1522_, lean_object* v_declName_1523_, lean_object* v___x_1524_, lean_object* v_____r_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
uint8_t v___x_31693__boxed_1531_; lean_object* v_res_1532_; 
v___x_31693__boxed_1531_ = lean_unbox(v___x_1524_);
v_res_1532_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(v_val_1519_, v___x_1520_, v_x_1521_, v_mvarId_1522_, v_declName_1523_, v___x_31693__boxed_1531_, v_____r_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec_ref(v_x_1521_);
lean_dec_ref(v___x_1520_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5(lean_object* v_declName_1533_, lean_object* v_val_1534_, uint8_t v___x_1535_, uint8_t v___x_1536_, size_t v_sz_1537_, size_t v_i_1538_, lean_object* v_bs_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
uint8_t v___x_1545_; 
v___x_1545_ = lean_usize_dec_lt(v_i_1538_, v_sz_1537_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; 
lean_dec_ref(v_val_1534_);
lean_dec(v_declName_1533_);
v___x_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1546_, 0, v_bs_1539_);
return v___x_1546_;
}
else
{
lean_object* v_v_1547_; lean_object* v_toInductionSubgoal_1548_; lean_object* v_ctorName_1549_; lean_object* v_mvarId_1550_; lean_object* v_fields_1551_; lean_object* v___f_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v_bs_x27_1555_; uint8_t v___y_1557_; 
v_v_1547_ = lean_array_uget_borrowed(v_bs_1539_, v_i_1538_);
v_toInductionSubgoal_1548_ = lean_ctor_get(v_v_1547_, 0);
v_ctorName_1549_ = lean_ctor_get(v_v_1547_, 1);
lean_inc(v_ctorName_1549_);
v_mvarId_1550_ = lean_ctor_get(v_toInductionSubgoal_1548_, 0);
lean_inc(v_mvarId_1550_);
v_fields_1551_ = lean_ctor_get(v_toInductionSubgoal_1548_, 1);
lean_inc_ref(v_fields_1551_);
v___f_1552_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0));
v___x_1553_ = l_Lean_instInhabitedExpr;
v___x_1554_ = lean_unsigned_to_nat(0u);
v_bs_x27_1555_ = lean_array_uset(v_bs_1539_, v_i_1538_, v___x_1554_);
if (lean_obj_tag(v_ctorName_1549_) == 0)
{
v___y_1557_ = v___x_1536_;
goto v___jp_1556_;
}
else
{
lean_dec_ref_known(v_ctorName_1549_, 1);
v___y_1557_ = v___x_1535_;
goto v___jp_1556_;
}
v___jp_1556_:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___y_1560_; lean_object* v___x_1561_; 
v___x_1558_ = lean_box(v___y_1557_);
v___x_1559_ = lean_box(v___x_1535_);
lean_inc_ref(v_val_1534_);
lean_inc(v_declName_1533_);
lean_inc(v_mvarId_1550_);
v___y_1560_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed), 13, 8);
lean_closure_set(v___y_1560_, 0, v___x_1558_);
lean_closure_set(v___y_1560_, 1, v_mvarId_1550_);
lean_closure_set(v___y_1560_, 2, v___f_1552_);
lean_closure_set(v___y_1560_, 3, v_declName_1533_);
lean_closure_set(v___y_1560_, 4, v_val_1534_);
lean_closure_set(v___y_1560_, 5, v___x_1553_);
lean_closure_set(v___y_1560_, 6, v_fields_1551_);
lean_closure_set(v___y_1560_, 7, v___x_1559_);
v___x_1561_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1550_, v___y_1560_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; size_t v___x_1563_; size_t v___x_1564_; lean_object* v___x_1565_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_a_1562_);
lean_dec_ref_known(v___x_1561_, 1);
v___x_1563_ = ((size_t)1ULL);
v___x_1564_ = lean_usize_add(v_i_1538_, v___x_1563_);
v___x_1565_ = lean_array_uset(v_bs_x27_1555_, v_i_1538_, v_a_1562_);
v_i_1538_ = v___x_1564_;
v_bs_1539_ = v___x_1565_;
goto _start;
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_dec_ref(v_bs_x27_1555_);
lean_dec_ref(v_val_1534_);
lean_dec(v_declName_1533_);
v_a_1567_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1569_ = v___x_1561_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1561_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1567_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5___boxed(lean_object* v_declName_1575_, lean_object* v_val_1576_, lean_object* v___x_1577_, lean_object* v___x_1578_, lean_object* v_sz_1579_, lean_object* v_i_1580_, lean_object* v_bs_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
uint8_t v___x_31842__boxed_1587_; uint8_t v___x_31843__boxed_1588_; size_t v_sz_boxed_1589_; size_t v_i_boxed_1590_; lean_object* v_res_1591_; 
v___x_31842__boxed_1587_ = lean_unbox(v___x_1577_);
v___x_31843__boxed_1588_ = lean_unbox(v___x_1578_);
v_sz_boxed_1589_ = lean_unbox_usize(v_sz_1579_);
lean_dec(v_sz_1579_);
v_i_boxed_1590_ = lean_unbox_usize(v_i_1580_);
lean_dec(v_i_1580_);
v_res_1591_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5(v_declName_1575_, v_val_1576_, v___x_31842__boxed_1587_, v___x_31843__boxed_1588_, v_sz_boxed_1589_, v_i_boxed_1590_, v_bs_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(lean_object* v_val_1592_, lean_object* v___x_1593_, lean_object* v_x_1594_, lean_object* v_mvarId_1595_, uint8_t v___x_1596_, lean_object* v_declName_1597_, uint8_t v_hasTrace_1598_, lean_object* v_____r_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v_majorPos_1629_; lean_object* v_arity_1630_; lean_object* v_insterestingCtors_1631_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___x_1651_; uint8_t v___x_1652_; 
v_majorPos_1629_ = lean_ctor_get(v_val_1592_, 1);
v_arity_1630_ = lean_ctor_get(v_val_1592_, 2);
v_insterestingCtors_1631_ = lean_ctor_get(v_val_1592_, 3);
v___x_1651_ = lean_array_get_size(v_x_1594_);
v___x_1652_ = lean_nat_dec_lt(v___x_1651_, v_arity_1630_);
if (v___x_1652_ == 0)
{
v___y_1633_ = v___y_1600_;
v___y_1634_ = v___y_1601_;
v___y_1635_ = v___y_1602_;
v___y_1636_ = v___y_1603_;
goto v___jp_1632_;
}
else
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1662_; 
lean_dec(v_declName_1597_);
lean_dec(v_mvarId_1595_);
lean_dec_ref(v_val_1592_);
v___x_1653_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1);
v___x_1654_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1653_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1657_ = v___x_1654_;
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1654_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1660_; 
if (v_isShared_1658_ == 0)
{
v___x_1660_ = v___x_1657_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_a_1655_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
v___jp_1605_:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1612_ = lean_array_get_borrowed(v___x_1593_, v_x_1594_, v___y_1607_);
lean_dec(v___y_1607_);
v___x_1613_ = l_Lean_Expr_fvarId_x21(v___x_1612_);
v___x_1614_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__0));
v___x_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1615_, 0, v___y_1606_);
v___x_1616_ = l_Lean_MVarId_cases(v_mvarId_1595_, v___x_1613_, v___x_1614_, v___x_1596_, v___x_1615_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; size_t v_sz_1618_; size_t v___x_1619_; lean_object* v___x_1620_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_a_1617_);
lean_dec_ref_known(v___x_1616_, 1);
v_sz_1618_ = lean_array_size(v_a_1617_);
v___x_1619_ = ((size_t)0ULL);
v___x_1620_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5(v_declName_1597_, v_val_1592_, v___x_1596_, v_hasTrace_1598_, v_sz_1618_, v___x_1619_, v_a_1617_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
return v___x_1620_;
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
lean_dec(v_declName_1597_);
lean_dec_ref(v_val_1592_);
v_a_1621_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1616_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1616_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
v___jp_1632_:
{
lean_object* v___x_1637_; uint8_t v___x_1638_; 
v___x_1637_ = lean_array_get_borrowed(v___x_1593_, v_x_1594_, v_majorPos_1629_);
v___x_1638_ = l_Lean_Expr_isFVar(v___x_1637_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
lean_dec(v_declName_1597_);
lean_dec(v_mvarId_1595_);
lean_dec_ref(v_val_1592_);
v___x_1639_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__2);
lean_inc(v___x_1637_);
v___x_1640_ = l_Lean_indentExpr(v___x_1637_);
v___x_1641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1639_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
v___x_1642_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1641_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
else
{
lean_inc(v_majorPos_1629_);
lean_inc_ref(v_insterestingCtors_1631_);
v___y_1606_ = v_insterestingCtors_1631_;
v___y_1607_ = v_majorPos_1629_;
v___y_1608_ = v___y_1633_;
v___y_1609_ = v___y_1634_;
v___y_1610_ = v___y_1635_;
v___y_1611_ = v___y_1636_;
goto v___jp_1605_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0___boxed(lean_object* v_val_1663_, lean_object* v___x_1664_, lean_object* v_x_1665_, lean_object* v_mvarId_1666_, lean_object* v___x_1667_, lean_object* v_declName_1668_, lean_object* v_hasTrace_1669_, lean_object* v_____r_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
uint8_t v___x_31927__boxed_1676_; uint8_t v_hasTrace_boxed_1677_; lean_object* v_res_1678_; 
v___x_31927__boxed_1676_ = lean_unbox(v___x_1667_);
v_hasTrace_boxed_1677_ = lean_unbox(v_hasTrace_1669_);
v_res_1678_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v_val_1663_, v___x_1664_, v_x_1665_, v_mvarId_1666_, v___x_31927__boxed_1676_, v_declName_1668_, v_hasTrace_boxed_1677_, v_____r_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec_ref(v_x_1665_);
lean_dec_ref(v___x_1664_);
return v_res_1678_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1(void){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1680_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__0));
v___x_1681_ = l_Lean_stringToMessageData(v___x_1680_);
return v___x_1681_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3(void){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1683_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__2));
v___x_1684_ = l_Lean_stringToMessageData(v___x_1683_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6(lean_object* v_mvarId_1685_, lean_object* v_x_1686_, lean_object* v_x_1687_, lean_object* v_x_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
if (lean_obj_tag(v_x_1686_) == 5)
{
lean_object* v_fn_1694_; lean_object* v_arg_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v_fn_1694_ = lean_ctor_get(v_x_1686_, 0);
lean_inc_ref(v_fn_1694_);
v_arg_1695_ = lean_ctor_get(v_x_1686_, 1);
lean_inc_ref(v_arg_1695_);
lean_dec_ref_known(v_x_1686_, 2);
v___x_1696_ = lean_array_set(v_x_1687_, v_x_1688_, v_arg_1695_);
v___x_1697_ = lean_unsigned_to_nat(1u);
v___x_1698_ = lean_nat_sub(v_x_1688_, v___x_1697_);
lean_dec(v_x_1688_);
v_x_1686_ = v_fn_1694_;
v_x_1687_ = v___x_1696_;
v_x_1688_ = v___x_1698_;
goto _start;
}
else
{
lean_dec(v_x_1688_);
if (lean_obj_tag(v_x_1686_) == 4)
{
lean_object* v_declName_1700_; lean_object* v___f_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v_declName_1700_ = lean_ctor_get(v_x_1686_, 0);
lean_inc_n(v_declName_1700_, 2);
lean_dec_ref_known(v_x_1686_, 2);
v___f_1701_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1));
v___x_1702_ = l_Lean_instInhabitedExpr;
v___x_1703_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_declName_1700_, v___y_1692_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_a_1704_; 
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
lean_inc(v_a_1704_);
lean_dec_ref_known(v___x_1703_, 1);
if (lean_obj_tag(v_a_1704_) == 1)
{
lean_object* v_toCold_1705_; lean_object* v_options_1706_; lean_object* v_val_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1997_; 
v_toCold_1705_ = lean_ctor_get(v___y_1691_, 0);
v_options_1706_ = lean_ctor_get(v_toCold_1705_, 2);
v_val_1707_ = lean_ctor_get(v_a_1704_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v_a_1704_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1709_ = v_a_1704_;
v_isShared_1710_ = v_isSharedCheck_1997_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_val_1707_);
lean_dec(v_a_1704_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1997_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v_inheritedTraceOptions_1711_; uint8_t v_hasTrace_1712_; lean_object* v___x_1713_; lean_object* v___y_1715_; lean_object* v_a_1716_; lean_object* v___y_1751_; lean_object* v___y_1754_; lean_object* v_a_1755_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; 
v_inheritedTraceOptions_1711_ = lean_ctor_get(v_toCold_1705_, 11);
v_hasTrace_1712_ = lean_ctor_get_uint8(v_options_1706_, sizeof(void*)*1);
v___x_1713_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5));
if (v_hasTrace_1712_ == 0)
{
lean_object* v_majorPos_1816_; lean_object* v_arity_1817_; lean_object* v_insterestingCtors_1818_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___x_1838_; uint8_t v___x_1839_; 
v_majorPos_1816_ = lean_ctor_get(v_val_1707_, 1);
v_arity_1817_ = lean_ctor_get(v_val_1707_, 2);
v_insterestingCtors_1818_ = lean_ctor_get(v_val_1707_, 3);
v___x_1838_ = lean_array_get_size(v_x_1687_);
v___x_1839_ = lean_nat_dec_lt(v___x_1838_, v_arity_1817_);
if (v___x_1839_ == 0)
{
v___y_1820_ = v___y_1689_;
v___y_1821_ = v___y_1690_;
v___y_1822_ = v___y_1691_;
v___y_1823_ = v___y_1692_;
goto v___jp_1819_;
}
else
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
lean_del_object(v___x_1709_);
lean_dec(v_val_1707_);
lean_dec(v_declName_1700_);
lean_dec_ref(v_x_1687_);
lean_dec(v_mvarId_1685_);
v___x_1840_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1);
v___x_1841_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1840_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v___x_1841_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1841_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
lean_inc(v_a_1842_);
if (v_isShared_1845_ == 0)
{
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
v___y_1754_ = v___x_1847_;
v_a_1755_ = v_a_1842_;
goto v___jp_1753_;
}
}
}
v___jp_1819_:
{
lean_object* v___x_1824_; uint8_t v___x_1825_; 
v___x_1824_ = lean_array_get_borrowed(v___x_1702_, v_x_1687_, v_majorPos_1816_);
v___x_1825_ = l_Lean_Expr_isFVar(v___x_1824_);
if (v___x_1825_ == 0)
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1837_; 
lean_inc(v___x_1824_);
lean_del_object(v___x_1709_);
lean_dec(v_val_1707_);
lean_dec(v_declName_1700_);
lean_dec_ref(v_x_1687_);
lean_dec(v_mvarId_1685_);
v___x_1826_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__2);
v___x_1827_ = l_Lean_indentExpr(v___x_1824_);
v___x_1828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1826_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
v___x_1829_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1828_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1832_ = v___x_1829_;
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1829_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
lean_inc(v_a_1830_);
if (v_isShared_1833_ == 0)
{
v___x_1835_ = v___x_1832_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_a_1830_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
v___y_1754_ = v___x_1835_;
v_a_1755_ = v_a_1830_;
goto v___jp_1753_;
}
}
}
else
{
lean_inc(v_majorPos_1816_);
lean_inc_ref(v_insterestingCtors_1818_);
v___y_1790_ = v_insterestingCtors_1818_;
v___y_1791_ = v_majorPos_1816_;
v___y_1792_ = v___y_1820_;
v___y_1793_ = v___y_1821_;
v___y_1794_ = v___y_1822_;
v___y_1795_ = v___y_1823_;
goto v___jp_1789_;
}
}
}
else
{
lean_object* v___x_1850_; lean_object* v___x_1851_; uint8_t v___x_1852_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v_a_1856_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v_a_1871_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v_a_1876_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v_a_1904_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v_a_1916_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v_a_1921_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; 
lean_del_object(v___x_1709_);
v___x_1850_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__6));
v___x_1851_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9);
v___x_1852_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1711_, v_options_1706_, v___x_1851_);
if (v___x_1852_ == 0)
{
lean_object* v___x_1979_; uint8_t v___x_1980_; 
v___x_1979_ = l_Lean_trace_profiler;
v___x_1980_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_options_1706_, v___x_1979_);
if (v___x_1980_ == 0)
{
if (v___x_1852_ == 0)
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1981_ = lean_box(0);
v___x_1982_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v_val_1707_, v___x_1702_, v_x_1687_, v_mvarId_1685_, v___x_1980_, v_declName_1700_, v_hasTrace_1712_, v___x_1981_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec_ref(v_x_1687_);
v___y_1751_ = v___x_1982_;
goto v___jp_1750_;
}
else
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1983_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3);
lean_inc(v_mvarId_1685_);
v___x_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1984_, 0, v_mvarId_1685_);
v___x_1985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1983_);
lean_ctor_set(v___x_1985_, 1, v___x_1984_);
v___x_1986_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1713_, v___x_1985_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_a_1987_; lean_object* v___x_1988_; 
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_1987_);
lean_dec_ref_known(v___x_1986_, 1);
v___x_1988_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v_val_1707_, v___x_1702_, v_x_1687_, v_mvarId_1685_, v___x_1980_, v_declName_1700_, v_hasTrace_1712_, v_a_1987_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec_ref(v_x_1687_);
v___y_1751_ = v___x_1988_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1996_; 
lean_dec(v_val_1707_);
lean_dec(v_declName_1700_);
lean_dec_ref(v_x_1687_);
lean_dec(v_mvarId_1685_);
v_a_1989_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1991_ = v___x_1986_;
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1986_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1994_; 
lean_inc(v_a_1989_);
if (v_isShared_1992_ == 0)
{
v___x_1994_ = v___x_1991_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
v___y_1715_ = v___x_1994_;
v_a_1716_ = v_a_1989_;
goto v___jp_1714_;
}
}
}
}
}
else
{
goto v___jp_1946_;
}
}
else
{
goto v___jp_1946_;
}
v___jp_1853_:
{
lean_object* v___x_1857_; double v___x_1858_; double v___x_1859_; double v___x_1860_; double v___x_1861_; double v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1857_ = lean_io_mono_nanos_now();
v___x_1858_ = lean_float_of_nat(v___y_1854_);
v___x_1859_ = lean_float_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10);
v___x_1860_ = lean_float_div(v___x_1858_, v___x_1859_);
v___x_1861_ = lean_float_of_nat(v___x_1857_);
v___x_1862_ = lean_float_div(v___x_1861_, v___x_1859_);
v___x_1863_ = lean_box_float(v___x_1860_);
v___x_1864_ = lean_box_float(v___x_1862_);
v___x_1865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1863_);
lean_ctor_set(v___x_1865_, 1, v___x_1864_);
v___x_1866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1866_, 0, v_a_1856_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
v___x_1867_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_1713_, v_hasTrace_1712_, v___x_1850_, v_options_1706_, v___x_1852_, v___y_1855_, v___f_1701_, v___x_1866_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
return v___x_1867_;
}
v___jp_1868_:
{
lean_object* v___x_1872_; 
v___x_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1872_, 0, v_a_1871_);
v___y_1854_ = v___y_1869_;
v___y_1855_ = v___y_1870_;
v_a_1856_ = v___x_1872_;
goto v___jp_1853_;
}
v___jp_1873_:
{
uint8_t v___x_1877_; 
v___x_1877_ = l_Lean_Exception_isInterrupt(v_a_1876_);
if (v___x_1877_ == 0)
{
uint8_t v___x_1878_; 
lean_inc_ref(v_a_1876_);
v___x_1878_ = l_Lean_Exception_isRuntime(v_a_1876_);
if (v___x_1878_ == 0)
{
lean_object* v___x_1879_; lean_object* v_a_1880_; uint8_t v___x_1881_; 
v___x_1879_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(v___x_1713_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
v_a_1880_ = lean_ctor_get(v___x_1879_, 0);
lean_inc(v_a_1880_);
lean_dec_ref(v___x_1879_);
v___x_1881_ = lean_unbox(v_a_1880_);
lean_dec(v_a_1880_);
if (v___x_1881_ == 0)
{
v___y_1869_ = v___y_1874_;
v___y_1870_ = v___y_1875_;
v_a_1871_ = v_a_1876_;
goto v___jp_1868_;
}
else
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1882_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1);
lean_inc_ref(v_a_1876_);
v___x_1883_ = l_Lean_Exception_toMessageData(v_a_1876_);
v___x_1884_ = l_Lean_indentD(v___x_1883_);
v___x_1885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1882_);
lean_ctor_set(v___x_1885_, 1, v___x_1884_);
v___x_1886_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1713_, v___x_1885_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_dec_ref_known(v___x_1886_, 1);
v___y_1869_ = v___y_1874_;
v___y_1870_ = v___y_1875_;
v_a_1871_ = v_a_1876_;
goto v___jp_1868_;
}
else
{
lean_object* v_a_1887_; 
lean_dec_ref(v_a_1876_);
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_a_1887_);
lean_dec_ref_known(v___x_1886_, 1);
v___y_1869_ = v___y_1874_;
v___y_1870_ = v___y_1875_;
v_a_1871_ = v_a_1887_;
goto v___jp_1868_;
}
}
}
else
{
v___y_1869_ = v___y_1874_;
v___y_1870_ = v___y_1875_;
v_a_1871_ = v_a_1876_;
goto v___jp_1868_;
}
}
else
{
v___y_1869_ = v___y_1874_;
v___y_1870_ = v___y_1875_;
v_a_1871_ = v_a_1876_;
goto v___jp_1868_;
}
}
v___jp_1888_:
{
if (lean_obj_tag(v___y_1891_) == 0)
{
lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1899_; 
v_a_1892_ = lean_ctor_get(v___y_1891_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___y_1891_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1894_ = v___y_1891_;
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_dec(v___y_1891_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1897_; 
if (v_isShared_1895_ == 0)
{
lean_ctor_set_tag(v___x_1894_, 1);
v___x_1897_ = v___x_1894_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_a_1892_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
v___y_1854_ = v___y_1889_;
v___y_1855_ = v___y_1890_;
v_a_1856_ = v___x_1897_;
goto v___jp_1853_;
}
}
}
else
{
lean_object* v_a_1900_; 
v_a_1900_ = lean_ctor_get(v___y_1891_, 0);
lean_inc(v_a_1900_);
lean_dec_ref_known(v___y_1891_, 1);
v___y_1874_ = v___y_1889_;
v___y_1875_ = v___y_1890_;
v_a_1876_ = v_a_1900_;
goto v___jp_1873_;
}
}
v___jp_1901_:
{
lean_object* v___x_1905_; double v___x_1906_; double v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1905_ = lean_io_get_num_heartbeats();
v___x_1906_ = lean_float_of_nat(v___y_1902_);
v___x_1907_ = lean_float_of_nat(v___x_1905_);
v___x_1908_ = lean_box_float(v___x_1906_);
v___x_1909_ = lean_box_float(v___x_1907_);
v___x_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1908_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
v___x_1911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1911_, 0, v_a_1904_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1912_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_1713_, v_hasTrace_1712_, v___x_1850_, v_options_1706_, v___x_1852_, v___y_1903_, v___f_1701_, v___x_1911_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
return v___x_1912_;
}
v___jp_1913_:
{
lean_object* v___x_1917_; 
v___x_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1917_, 0, v_a_1916_);
v___y_1902_ = v___y_1914_;
v___y_1903_ = v___y_1915_;
v_a_1904_ = v___x_1917_;
goto v___jp_1901_;
}
v___jp_1918_:
{
uint8_t v___x_1922_; 
v___x_1922_ = l_Lean_Exception_isInterrupt(v_a_1921_);
if (v___x_1922_ == 0)
{
uint8_t v___x_1923_; 
lean_inc_ref(v_a_1921_);
v___x_1923_ = l_Lean_Exception_isRuntime(v_a_1921_);
if (v___x_1923_ == 0)
{
lean_object* v___x_1924_; lean_object* v_a_1925_; uint8_t v___x_1926_; 
v___x_1924_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(v___x_1713_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_a_1925_);
lean_dec_ref(v___x_1924_);
v___x_1926_ = lean_unbox(v_a_1925_);
lean_dec(v_a_1925_);
if (v___x_1926_ == 0)
{
v___y_1914_ = v___y_1919_;
v___y_1915_ = v___y_1920_;
v_a_1916_ = v_a_1921_;
goto v___jp_1913_;
}
else
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1927_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1);
lean_inc_ref(v_a_1921_);
v___x_1928_ = l_Lean_Exception_toMessageData(v_a_1921_);
v___x_1929_ = l_Lean_indentD(v___x_1928_);
v___x_1930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1927_);
lean_ctor_set(v___x_1930_, 1, v___x_1929_);
v___x_1931_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1713_, v___x_1930_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_dec_ref_known(v___x_1931_, 1);
v___y_1914_ = v___y_1919_;
v___y_1915_ = v___y_1920_;
v_a_1916_ = v_a_1921_;
goto v___jp_1913_;
}
else
{
lean_object* v_a_1932_; 
lean_dec_ref(v_a_1921_);
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
lean_dec_ref_known(v___x_1931_, 1);
v___y_1914_ = v___y_1919_;
v___y_1915_ = v___y_1920_;
v_a_1916_ = v_a_1932_;
goto v___jp_1913_;
}
}
}
else
{
v___y_1914_ = v___y_1919_;
v___y_1915_ = v___y_1920_;
v_a_1916_ = v_a_1921_;
goto v___jp_1913_;
}
}
else
{
v___y_1914_ = v___y_1919_;
v___y_1915_ = v___y_1920_;
v_a_1916_ = v_a_1921_;
goto v___jp_1913_;
}
}
v___jp_1933_:
{
if (lean_obj_tag(v___y_1936_) == 0)
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
v_a_1937_ = lean_ctor_get(v___y_1936_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___y_1936_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___y_1936_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___y_1936_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
lean_ctor_set_tag(v___x_1939_, 1);
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
v___y_1902_ = v___y_1934_;
v___y_1903_ = v___y_1935_;
v_a_1904_ = v___x_1942_;
goto v___jp_1901_;
}
}
}
else
{
lean_object* v_a_1945_; 
v_a_1945_ = lean_ctor_get(v___y_1936_, 0);
lean_inc(v_a_1945_);
lean_dec_ref_known(v___y_1936_, 1);
v___y_1919_ = v___y_1934_;
v___y_1920_ = v___y_1935_;
v_a_1921_ = v_a_1945_;
goto v___jp_1918_;
}
}
v___jp_1946_:
{
lean_object* v___x_1947_; lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1978_; 
v___x_1947_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___y_1692_);
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1950_ = v___x_1947_;
v_isShared_1951_ = v_isSharedCheck_1978_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1947_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1978_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1952_; uint8_t v___x_1953_; 
v___x_1952_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1953_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_options_1706_, v___x_1952_);
if (v___x_1953_ == 0)
{
lean_object* v___x_1954_; 
v___x_1954_ = lean_io_mono_nanos_now();
if (v___x_1852_ == 0)
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
lean_del_object(v___x_1950_);
v___x_1955_ = lean_box(0);
v___x_1956_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v_val_1707_, v___x_1702_, v_x_1687_, v_mvarId_1685_, v___x_1953_, v_declName_1700_, v_hasTrace_1712_, v___x_1955_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec_ref(v_x_1687_);
v___y_1889_ = v___x_1954_;
v___y_1890_ = v_a_1948_;
v___y_1891_ = v___x_1956_;
goto v___jp_1888_;
}
else
{
lean_object* v___x_1957_; lean_object* v___x_1959_; 
v___x_1957_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3);
lean_inc(v_mvarId_1685_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set_tag(v___x_1950_, 1);
lean_ctor_set(v___x_1950_, 0, v_mvarId_1685_);
v___x_1959_ = v___x_1950_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_mvarId_1685_);
v___x_1959_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1957_);
lean_ctor_set(v___x_1960_, 1, v___x_1959_);
v___x_1961_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1713_, v___x_1960_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v_a_1962_; lean_object* v___x_1963_; 
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_a_1962_);
lean_dec_ref_known(v___x_1961_, 1);
v___x_1963_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v_val_1707_, v___x_1702_, v_x_1687_, v_mvarId_1685_, v___x_1953_, v_declName_1700_, v_hasTrace_1712_, v_a_1962_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec_ref(v_x_1687_);
v___y_1889_ = v___x_1954_;
v___y_1890_ = v_a_1948_;
v___y_1891_ = v___x_1963_;
goto v___jp_1888_;
}
else
{
lean_object* v_a_1964_; 
lean_dec(v_val_1707_);
lean_dec(v_declName_1700_);
lean_dec_ref(v_x_1687_);
lean_dec(v_mvarId_1685_);
v_a_1964_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_a_1964_);
lean_dec_ref_known(v___x_1961_, 1);
v___y_1874_ = v___x_1954_;
v___y_1875_ = v_a_1948_;
v_a_1876_ = v_a_1964_;
goto v___jp_1873_;
}
}
}
}
else
{
lean_object* v___x_1966_; 
v___x_1966_ = lean_io_get_num_heartbeats();
if (v___x_1852_ == 0)
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
lean_del_object(v___x_1950_);
v___x_1967_ = lean_box(0);
v___x_1968_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(v_val_1707_, v___x_1702_, v_x_1687_, v_mvarId_1685_, v_declName_1700_, v___x_1953_, v___x_1967_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec_ref(v_x_1687_);
v___y_1934_ = v___x_1966_;
v___y_1935_ = v_a_1948_;
v___y_1936_ = v___x_1968_;
goto v___jp_1933_;
}
else
{
lean_object* v___x_1969_; lean_object* v___x_1971_; 
v___x_1969_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3);
lean_inc(v_mvarId_1685_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set_tag(v___x_1950_, 1);
lean_ctor_set(v___x_1950_, 0, v_mvarId_1685_);
v___x_1971_ = v___x_1950_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_mvarId_1685_);
v___x_1971_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1969_);
lean_ctor_set(v___x_1972_, 1, v___x_1971_);
v___x_1973_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1713_, v___x_1972_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v___x_1975_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
lean_inc(v_a_1974_);
lean_dec_ref_known(v___x_1973_, 1);
v___x_1975_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(v_val_1707_, v___x_1702_, v_x_1687_, v_mvarId_1685_, v_declName_1700_, v___x_1953_, v_a_1974_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec_ref(v_x_1687_);
v___y_1934_ = v___x_1966_;
v___y_1935_ = v_a_1948_;
v___y_1936_ = v___x_1975_;
goto v___jp_1933_;
}
else
{
lean_object* v_a_1976_; 
lean_dec(v_val_1707_);
lean_dec(v_declName_1700_);
lean_dec_ref(v_x_1687_);
lean_dec(v_mvarId_1685_);
v_a_1976_ = lean_ctor_get(v___x_1973_, 0);
lean_inc(v_a_1976_);
lean_dec_ref_known(v___x_1973_, 1);
v___y_1919_ = v___x_1966_;
v___y_1920_ = v_a_1948_;
v_a_1921_ = v_a_1976_;
goto v___jp_1918_;
}
}
}
}
}
}
}
v___jp_1714_:
{
uint8_t v___x_1717_; 
v___x_1717_ = l_Lean_Exception_isInterrupt(v_a_1716_);
if (v___x_1717_ == 0)
{
uint8_t v___x_1718_; 
lean_inc_ref(v_a_1716_);
v___x_1718_ = l_Lean_Exception_isRuntime(v_a_1716_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1749_; 
lean_dec_ref(v___y_1715_);
v___x_1719_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(v___x_1713_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1722_ = v___x_1719_;
v_isShared_1723_ = v_isSharedCheck_1749_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v___x_1719_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1749_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
uint8_t v___x_1724_; 
v___x_1724_ = lean_unbox(v_a_1720_);
lean_dec(v_a_1720_);
if (v___x_1724_ == 0)
{
lean_object* v___x_1726_; 
if (v_isShared_1723_ == 0)
{
lean_ctor_set_tag(v___x_1722_, 1);
lean_ctor_set(v___x_1722_, 0, v_a_1716_);
v___x_1726_ = v___x_1722_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1716_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
else
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
lean_del_object(v___x_1722_);
v___x_1728_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1);
lean_inc_ref(v_a_1716_);
v___x_1729_ = l_Lean_Exception_toMessageData(v_a_1716_);
v___x_1730_ = l_Lean_indentD(v___x_1729_);
v___x_1731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1728_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
v___x_1732_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1713_, v___x_1731_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1739_; 
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1739_ == 0)
{
lean_object* v_unused_1740_; 
v_unused_1740_ = lean_ctor_get(v___x_1732_, 0);
lean_dec(v_unused_1740_);
v___x_1734_ = v___x_1732_;
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
else
{
lean_dec(v___x_1732_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
lean_ctor_set_tag(v___x_1734_, 1);
lean_ctor_set(v___x_1734_, 0, v_a_1716_);
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1716_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
else
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
lean_dec_ref(v_a_1716_);
v_a_1741_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1743_ = v___x_1732_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1732_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1741_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_a_1716_);
return v___y_1715_;
}
}
else
{
lean_dec_ref(v_a_1716_);
return v___y_1715_;
}
}
v___jp_1750_:
{
if (lean_obj_tag(v___y_1751_) == 0)
{
return v___y_1751_;
}
else
{
lean_object* v_a_1752_; 
v_a_1752_ = lean_ctor_get(v___y_1751_, 0);
lean_inc(v_a_1752_);
v___y_1715_ = v___y_1751_;
v_a_1716_ = v_a_1752_;
goto v___jp_1714_;
}
}
v___jp_1753_:
{
uint8_t v___x_1756_; 
v___x_1756_ = l_Lean_Exception_isInterrupt(v_a_1755_);
if (v___x_1756_ == 0)
{
uint8_t v___x_1757_; 
lean_inc_ref(v_a_1755_);
v___x_1757_ = l_Lean_Exception_isRuntime(v_a_1755_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1788_; 
lean_dec_ref(v___y_1754_);
v___x_1758_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(v___x_1713_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1761_ = v___x_1758_;
v_isShared_1762_ = v_isSharedCheck_1788_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1758_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1788_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
uint8_t v___x_1763_; 
v___x_1763_ = lean_unbox(v_a_1759_);
lean_dec(v_a_1759_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1765_; 
if (v_isShared_1762_ == 0)
{
lean_ctor_set_tag(v___x_1761_, 1);
lean_ctor_set(v___x_1761_, 0, v_a_1755_);
v___x_1765_ = v___x_1761_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1755_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
else
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
lean_del_object(v___x_1761_);
v___x_1767_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1);
lean_inc_ref(v_a_1755_);
v___x_1768_ = l_Lean_Exception_toMessageData(v_a_1755_);
v___x_1769_ = l_Lean_indentD(v___x_1768_);
v___x_1770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1767_);
lean_ctor_set(v___x_1770_, 1, v___x_1769_);
v___x_1771_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1713_, v___x_1770_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1778_ == 0)
{
lean_object* v_unused_1779_; 
v_unused_1779_ = lean_ctor_get(v___x_1771_, 0);
lean_dec(v_unused_1779_);
v___x_1773_ = v___x_1771_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_dec(v___x_1771_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
lean_ctor_set_tag(v___x_1773_, 1);
lean_ctor_set(v___x_1773_, 0, v_a_1755_);
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1755_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
else
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
lean_dec_ref(v_a_1755_);
v_a_1780_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1771_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1771_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_a_1755_);
return v___y_1754_;
}
}
else
{
lean_dec_ref(v_a_1755_);
return v___y_1754_;
}
}
v___jp_1789_:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1800_; 
v___x_1796_ = lean_array_get(v___x_1702_, v_x_1687_, v___y_1791_);
lean_dec(v___y_1791_);
lean_dec_ref(v_x_1687_);
v___x_1797_ = l_Lean_Expr_fvarId_x21(v___x_1796_);
lean_dec(v___x_1796_);
v___x_1798_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__0));
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 0, v___y_1790_);
v___x_1800_ = v___x_1709_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___y_1790_);
v___x_1800_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
lean_object* v___x_1801_; 
v___x_1801_ = l_Lean_MVarId_cases(v_mvarId_1685_, v___x_1797_, v___x_1798_, v_hasTrace_1712_, v___x_1800_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; size_t v_sz_1803_; size_t v___x_1804_; lean_object* v___x_1805_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_a_1802_);
lean_dec_ref_known(v___x_1801_, 1);
v_sz_1803_ = lean_array_size(v_a_1802_);
v___x_1804_ = ((size_t)0ULL);
v___x_1805_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(v_declName_1700_, v_val_1707_, v_hasTrace_1712_, v_sz_1803_, v___x_1804_, v_a_1802_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
if (lean_obj_tag(v___x_1805_) == 0)
{
return v___x_1805_;
}
else
{
lean_object* v_a_1806_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_a_1806_);
v___y_1754_ = v___x_1805_;
v_a_1755_ = v_a_1806_;
goto v___jp_1753_;
}
}
else
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1814_; 
lean_dec(v_val_1707_);
lean_dec(v_declName_1700_);
v_a_1807_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1809_ = v___x_1801_;
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1801_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1812_; 
lean_inc(v_a_1807_);
if (v_isShared_1810_ == 0)
{
v___x_1812_ = v___x_1809_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1807_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
v___y_1754_ = v___x_1812_;
v_a_1755_ = v_a_1807_;
goto v___jp_1753_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
lean_dec(v_a_1704_);
lean_dec(v_declName_1700_);
lean_dec_ref(v_x_1687_);
lean_dec(v_mvarId_1685_);
v___x_1998_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12);
v___x_1999_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1998_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
return v___x_1999_;
}
}
else
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
lean_dec(v_declName_1700_);
lean_dec_ref(v_x_1687_);
lean_dec(v_mvarId_1685_);
v_a_2000_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1703_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1703_);
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
else
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
lean_dec_ref(v_x_1687_);
lean_dec_ref(v_x_1686_);
lean_dec(v_mvarId_1685_);
v___x_2008_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14);
v___x_2009_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_2008_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
return v___x_2009_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___boxed(lean_object* v_mvarId_2010_, lean_object* v_x_2011_, lean_object* v_x_2012_, lean_object* v_x_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6(v_mvarId_2010_, v_x_2011_, v_x_2012_, v_x_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitSparseCasesOn(lean_object* v_mvarId_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_){
_start:
{
lean_object* v___x_2026_; 
lean_inc(v_mvarId_2020_);
v___x_2026_ = l_Lean_MVarId_getType(v_mvarId_2020_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; lean_object* v___x_2028_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2027_);
lean_dec_ref_known(v___x_2026_, 1);
v___x_2028_ = l_Lean_Meta_matchEqHEqLHS_x3f(v_a_2027_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v_a_2029_; 
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
lean_inc(v_a_2029_);
lean_dec_ref_known(v___x_2028_, 1);
if (lean_obj_tag(v_a_2029_) == 1)
{
lean_object* v_val_2030_; lean_object* v_snd_2031_; lean_object* v_dummy_2032_; lean_object* v_nargs_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v_val_2030_ = lean_ctor_get(v_a_2029_, 0);
lean_inc(v_val_2030_);
lean_dec_ref_known(v_a_2029_, 1);
v_snd_2031_ = lean_ctor_get(v_val_2030_, 1);
lean_inc(v_snd_2031_);
lean_dec(v_val_2030_);
v_dummy_2032_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0);
v_nargs_2033_ = l_Lean_Expr_getAppNumArgs(v_snd_2031_);
lean_inc(v_nargs_2033_);
v___x_2034_ = lean_mk_array(v_nargs_2033_, v_dummy_2032_);
v___x_2035_ = lean_unsigned_to_nat(1u);
v___x_2036_ = lean_nat_sub(v_nargs_2033_, v___x_2035_);
lean_dec(v_nargs_2033_);
v___x_2037_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6(v_mvarId_2020_, v_snd_2031_, v___x_2034_, v___x_2036_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_);
return v___x_2037_;
}
else
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
lean_dec(v_a_2029_);
lean_dec(v_mvarId_2020_);
v___x_2038_ = lean_obj_once(&l_Lean_Meta_reduceSparseCasesOn___closed__1, &l_Lean_Meta_reduceSparseCasesOn___closed__1_once, _init_l_Lean_Meta_reduceSparseCasesOn___closed__1);
v___x_2039_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_2038_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_);
return v___x_2039_;
}
}
else
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
lean_dec(v_mvarId_2020_);
v_a_2040_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_2028_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2028_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
else
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2055_; 
lean_dec(v_mvarId_2020_);
v_a_2048_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2050_ = v___x_2026_;
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_2026_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2051_ == 0)
{
v___x_2053_ = v___x_2050_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitSparseCasesOn___boxed(lean_object* v_mvarId_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l_Lean_Meta_splitSparseCasesOn(v_mvarId_2056_, v_a_2057_, v_a_2058_, v_a_2059_, v_a_2060_);
lean_dec(v_a_2060_);
lean_dec_ref(v_a_2059_);
lean_dec(v_a_2058_);
lean_dec_ref(v_a_2057_);
return v_res_2062_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_SparseCasesOn(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_SparseCasesOnEq(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_HasNotBit(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cases(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_SplitSparseCasesOn(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
