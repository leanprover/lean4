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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
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
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_10567__overap_232_; lean_object* v___x_233_; 
v___x_230_ = lean_box(0);
v___x_231_ = l_instInhabitedOfMonad___redArg(v___x_229_, v___x_230_);
v___x_10567__overap_232_ = lean_panic_fn_borrowed(v___x_231_, v_msg_175_);
lean_dec(v___x_231_);
lean_inc(v___y_179_);
lean_inc_ref(v___y_178_);
lean_inc(v___y_177_);
lean_inc_ref(v___y_176_);
v___x_233_ = lean_apply_5(v___x_10567__overap_232_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, lean_box(0));
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
uint8_t v___x_14343__boxed_582_; lean_object* v_res_583_; 
v___x_14343__boxed_582_ = lean_unbox(v___x_575_);
v_res_583_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2(v___x_14343__boxed_582_, v___f_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
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
lean_object* v_toCold_649_; lean_object* v_currRecDepth_650_; lean_object* v_ref_651_; uint16_t v_optionFlags_652_; uint8_t v_suppressElabErrors_653_; uint8_t v_isRecordingDeps_654_; lean_object* v_ref_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v_traceState_658_; lean_object* v_traces_659_; lean_object* v___x_660_; size_t v_sz_661_; size_t v___x_662_; lean_object* v___x_663_; lean_object* v_msg_664_; lean_object* v___x_665_; lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_704_; 
v_toCold_649_ = lean_ctor_get(v___y_646_, 0);
v_currRecDepth_650_ = lean_ctor_get(v___y_646_, 1);
v_ref_651_ = lean_ctor_get(v___y_646_, 2);
v_optionFlags_652_ = lean_ctor_get_uint16(v___y_646_, sizeof(void*)*3);
v_suppressElabErrors_653_ = lean_ctor_get_uint8(v___y_646_, sizeof(void*)*3 + 2);
v_isRecordingDeps_654_ = lean_ctor_get_uint8(v___y_646_, sizeof(void*)*3 + 3);
v_ref_655_ = l_Lean_replaceRef(v_ref_642_, v_ref_651_);
lean_inc(v_currRecDepth_650_);
lean_inc_ref(v_toCold_649_);
v___x_656_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_656_, 0, v_toCold_649_);
lean_ctor_set(v___x_656_, 1, v_currRecDepth_650_);
lean_ctor_set(v___x_656_, 2, v_ref_655_);
lean_ctor_set_uint16(v___x_656_, sizeof(void*)*3, v_optionFlags_652_);
lean_ctor_set_uint8(v___x_656_, sizeof(void*)*3 + 2, v_suppressElabErrors_653_);
lean_ctor_set_uint8(v___x_656_, sizeof(void*)*3 + 3, v_isRecordingDeps_654_);
v___x_657_ = lean_st_ref_get(v___y_647_);
v_traceState_658_ = lean_ctor_get(v___x_657_, 4);
lean_inc_ref(v_traceState_658_);
lean_dec(v___x_657_);
v_traces_659_ = lean_ctor_get(v_traceState_658_, 0);
lean_inc_ref(v_traces_659_);
lean_dec_ref(v_traceState_658_);
v___x_660_ = l_Lean_PersistentArray_toArray___redArg(v_traces_659_);
lean_dec_ref(v_traces_659_);
v_sz_661_ = lean_array_size(v___x_660_);
v___x_662_ = ((size_t)0ULL);
v___x_663_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9_spec__10(v_sz_661_, v___x_662_, v___x_660_);
v_msg_664_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_664_, 0, v_data_641_);
lean_ctor_set(v_msg_664_, 1, v_msg_643_);
lean_ctor_set(v_msg_664_, 2, v___x_663_);
v___x_665_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msg_664_, v___y_644_, v___y_645_, v___x_656_, v___y_647_);
lean_dec_ref_known(v___x_656_, 3);
v_a_666_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_704_ == 0)
{
v___x_668_ = v___x_665_;
v_isShared_669_ = v_isSharedCheck_704_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_665_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_704_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v_traceState_671_; lean_object* v_env_672_; lean_object* v_nextMacroScope_673_; lean_object* v_ngen_674_; lean_object* v_auxDeclNGen_675_; lean_object* v_cache_676_; lean_object* v_recordedDeps_677_; lean_object* v_messages_678_; lean_object* v_infoState_679_; lean_object* v_snapshotTasks_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_703_; 
v___x_670_ = lean_st_ref_take(v___y_647_);
v_traceState_671_ = lean_ctor_get(v___x_670_, 4);
v_env_672_ = lean_ctor_get(v___x_670_, 0);
v_nextMacroScope_673_ = lean_ctor_get(v___x_670_, 1);
v_ngen_674_ = lean_ctor_get(v___x_670_, 2);
v_auxDeclNGen_675_ = lean_ctor_get(v___x_670_, 3);
v_cache_676_ = lean_ctor_get(v___x_670_, 5);
v_recordedDeps_677_ = lean_ctor_get(v___x_670_, 6);
v_messages_678_ = lean_ctor_get(v___x_670_, 7);
v_infoState_679_ = lean_ctor_get(v___x_670_, 8);
v_snapshotTasks_680_ = lean_ctor_get(v___x_670_, 9);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_703_ == 0)
{
v___x_682_ = v___x_670_;
v_isShared_683_ = v_isSharedCheck_703_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_snapshotTasks_680_);
lean_inc(v_infoState_679_);
lean_inc(v_messages_678_);
lean_inc(v_recordedDeps_677_);
lean_inc(v_cache_676_);
lean_inc(v_traceState_671_);
lean_inc(v_auxDeclNGen_675_);
lean_inc(v_ngen_674_);
lean_inc(v_nextMacroScope_673_);
lean_inc(v_env_672_);
lean_dec(v___x_670_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_703_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
uint64_t v_tid_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_701_; 
v_tid_684_ = lean_ctor_get_uint64(v_traceState_671_, sizeof(void*)*1);
v_isSharedCheck_701_ = !lean_is_exclusive(v_traceState_671_);
if (v_isSharedCheck_701_ == 0)
{
lean_object* v_unused_702_; 
v_unused_702_ = lean_ctor_get(v_traceState_671_, 0);
lean_dec(v_unused_702_);
v___x_686_ = v_traceState_671_;
v_isShared_687_ = v_isSharedCheck_701_;
goto v_resetjp_685_;
}
else
{
lean_dec(v_traceState_671_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_701_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_692_; 
v___x_688_ = lean_box(0);
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v_ref_642_);
lean_ctor_set(v___x_689_, 1, v_a_666_);
v___x_690_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_640_, v___x_689_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v___x_690_);
v___x_692_ = v___x_686_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_690_);
lean_ctor_set_uint64(v_reuseFailAlloc_700_, sizeof(void*)*1, v_tid_684_);
v___x_692_ = v_reuseFailAlloc_700_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v___x_694_; 
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 4, v___x_692_);
v___x_694_ = v___x_682_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_env_672_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_nextMacroScope_673_);
lean_ctor_set(v_reuseFailAlloc_699_, 2, v_ngen_674_);
lean_ctor_set(v_reuseFailAlloc_699_, 3, v_auxDeclNGen_675_);
lean_ctor_set(v_reuseFailAlloc_699_, 4, v___x_692_);
lean_ctor_set(v_reuseFailAlloc_699_, 5, v_cache_676_);
lean_ctor_set(v_reuseFailAlloc_699_, 6, v_recordedDeps_677_);
lean_ctor_set(v_reuseFailAlloc_699_, 7, v_messages_678_);
lean_ctor_set(v_reuseFailAlloc_699_, 8, v_infoState_679_);
lean_ctor_set(v_reuseFailAlloc_699_, 9, v_snapshotTasks_680_);
v___x_694_ = v_reuseFailAlloc_699_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_695_ = lean_st_ref_put(v___y_647_, v___x_694_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v___x_688_);
v___x_697_ = v___x_668_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_688_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9___boxed(lean_object* v_oldTraces_705_, lean_object* v_data_706_, lean_object* v_ref_707_, lean_object* v_msg_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9(v_oldTraces_705_, v_data_706_, v_ref_707_, v_msg_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
return v_res_714_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0(void){
_start:
{
lean_object* v___x_715_; double v___x_716_; 
v___x_715_ = lean_unsigned_to_nat(0u);
v___x_716_ = lean_float_of_nat(v___x_715_);
return v___x_716_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__1));
v___x_719_ = l_Lean_stringToMessageData(v___x_718_);
return v___x_719_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__3(void){
_start:
{
lean_object* v___x_720_; double v___x_721_; 
v___x_720_ = lean_unsigned_to_nat(1000u);
v___x_721_ = lean_float_of_nat(v___x_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(lean_object* v_cls_722_, uint8_t v_collapsed_723_, lean_object* v_tag_724_, lean_object* v_opts_725_, uint8_t v_clsEnabled_726_, lean_object* v_oldTraces_727_, lean_object* v_msg_728_, lean_object* v_resStartStop_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v_fst_735_; lean_object* v_snd_736_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v_data_740_; lean_object* v_fst_751_; lean_object* v_snd_752_; lean_object* v___x_753_; uint8_t v___x_754_; lean_object* v___y_756_; lean_object* v_a_757_; uint8_t v___y_772_; double v___y_804_; 
v_fst_735_ = lean_ctor_get(v_resStartStop_729_, 0);
lean_inc(v_fst_735_);
v_snd_736_ = lean_ctor_get(v_resStartStop_729_, 1);
lean_inc(v_snd_736_);
lean_dec_ref(v_resStartStop_729_);
v_fst_751_ = lean_ctor_get(v_snd_736_, 0);
lean_inc(v_fst_751_);
v_snd_752_ = lean_ctor_get(v_snd_736_, 1);
lean_inc(v_snd_752_);
lean_dec(v_snd_736_);
v___x_753_ = l_Lean_trace_profiler;
v___x_754_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_opts_725_, v___x_753_);
if (v___x_754_ == 0)
{
v___y_772_ = v___x_754_;
goto v___jp_771_;
}
else
{
lean_object* v___x_809_; uint8_t v___x_810_; 
v___x_809_ = l_Lean_trace_profiler_useHeartbeats;
v___x_810_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_opts_725_, v___x_809_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; lean_object* v___x_812_; double v___x_813_; double v___x_814_; double v___x_815_; 
v___x_811_ = l_Lean_trace_profiler_threshold;
v___x_812_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12(v_opts_725_, v___x_811_);
v___x_813_ = lean_float_of_nat(v___x_812_);
v___x_814_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__3);
v___x_815_ = lean_float_div(v___x_813_, v___x_814_);
v___y_804_ = v___x_815_;
goto v___jp_803_;
}
else
{
lean_object* v___x_816_; lean_object* v___x_817_; double v___x_818_; 
v___x_816_ = l_Lean_trace_profiler_threshold;
v___x_817_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12(v_opts_725_, v___x_816_);
v___x_818_ = lean_float_of_nat(v___x_817_);
v___y_804_ = v___x_818_;
goto v___jp_803_;
}
}
v___jp_737_:
{
lean_object* v___x_741_; 
lean_inc(v___y_739_);
v___x_741_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9(v_oldTraces_727_, v_data_740_, v___y_739_, v___y_738_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v___x_742_; 
lean_dec_ref_known(v___x_741_, 1);
v___x_742_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg(v_fst_735_);
return v___x_742_;
}
else
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
lean_dec(v_fst_735_);
v_a_743_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___x_741_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_741_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_743_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
v___jp_755_:
{
uint8_t v_result_758_; lean_object* v___x_759_; lean_object* v___x_760_; double v___x_761_; lean_object* v_data_762_; 
v_result_758_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11(v_fst_735_);
v___x_759_ = lean_box(v_result_758_);
v___x_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
v___x_761_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0);
lean_inc_ref(v_tag_724_);
lean_inc_ref(v___x_760_);
lean_inc(v_cls_722_);
v_data_762_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_762_, 0, v_cls_722_);
lean_ctor_set(v_data_762_, 1, v___x_760_);
lean_ctor_set(v_data_762_, 2, v_tag_724_);
lean_ctor_set_float(v_data_762_, sizeof(void*)*3, v___x_761_);
lean_ctor_set_float(v_data_762_, sizeof(void*)*3 + 8, v___x_761_);
lean_ctor_set_uint8(v_data_762_, sizeof(void*)*3 + 16, v_collapsed_723_);
if (v___x_754_ == 0)
{
lean_dec_ref_known(v___x_760_, 1);
lean_dec(v_snd_752_);
lean_dec(v_fst_751_);
lean_dec_ref(v_tag_724_);
lean_dec(v_cls_722_);
v___y_738_ = v_a_757_;
v___y_739_ = v___y_756_;
v_data_740_ = v_data_762_;
goto v___jp_737_;
}
else
{
lean_object* v_data_763_; double v___x_764_; double v___x_765_; 
lean_dec_ref_known(v_data_762_, 3);
v_data_763_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_763_, 0, v_cls_722_);
lean_ctor_set(v_data_763_, 1, v___x_760_);
lean_ctor_set(v_data_763_, 2, v_tag_724_);
v___x_764_ = lean_unbox_float(v_fst_751_);
lean_dec(v_fst_751_);
lean_ctor_set_float(v_data_763_, sizeof(void*)*3, v___x_764_);
v___x_765_ = lean_unbox_float(v_snd_752_);
lean_dec(v_snd_752_);
lean_ctor_set_float(v_data_763_, sizeof(void*)*3 + 8, v___x_765_);
lean_ctor_set_uint8(v_data_763_, sizeof(void*)*3 + 16, v_collapsed_723_);
v___y_738_ = v_a_757_;
v___y_739_ = v___y_756_;
v_data_740_ = v_data_763_;
goto v___jp_737_;
}
}
v___jp_766_:
{
lean_object* v_ref_767_; lean_object* v___x_768_; 
v_ref_767_ = lean_ctor_get(v___y_732_, 2);
lean_inc(v___y_733_);
lean_inc_ref(v___y_732_);
lean_inc(v___y_731_);
lean_inc_ref(v___y_730_);
lean_inc(v_fst_735_);
v___x_768_ = lean_apply_6(v_msg_728_, v_fst_735_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, lean_box(0));
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
lean_dec_ref_known(v___x_768_, 1);
v___y_756_ = v_ref_767_;
v_a_757_ = v_a_769_;
goto v___jp_755_;
}
else
{
lean_object* v___x_770_; 
lean_dec_ref_known(v___x_768_, 1);
v___x_770_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2);
v___y_756_ = v_ref_767_;
v_a_757_ = v___x_770_;
goto v___jp_755_;
}
}
v___jp_771_:
{
if (v_clsEnabled_726_ == 0)
{
if (v___y_772_ == 0)
{
lean_object* v___x_773_; lean_object* v_traceState_774_; lean_object* v_env_775_; lean_object* v_nextMacroScope_776_; lean_object* v_ngen_777_; lean_object* v_auxDeclNGen_778_; lean_object* v_cache_779_; lean_object* v_recordedDeps_780_; lean_object* v_messages_781_; lean_object* v_infoState_782_; lean_object* v_snapshotTasks_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_802_; 
lean_dec(v_snd_752_);
lean_dec(v_fst_751_);
lean_dec_ref(v_msg_728_);
lean_dec_ref(v_tag_724_);
lean_dec(v_cls_722_);
v___x_773_ = lean_st_ref_take(v___y_733_);
v_traceState_774_ = lean_ctor_get(v___x_773_, 4);
v_env_775_ = lean_ctor_get(v___x_773_, 0);
v_nextMacroScope_776_ = lean_ctor_get(v___x_773_, 1);
v_ngen_777_ = lean_ctor_get(v___x_773_, 2);
v_auxDeclNGen_778_ = lean_ctor_get(v___x_773_, 3);
v_cache_779_ = lean_ctor_get(v___x_773_, 5);
v_recordedDeps_780_ = lean_ctor_get(v___x_773_, 6);
v_messages_781_ = lean_ctor_get(v___x_773_, 7);
v_infoState_782_ = lean_ctor_get(v___x_773_, 8);
v_snapshotTasks_783_ = lean_ctor_get(v___x_773_, 9);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_802_ == 0)
{
v___x_785_ = v___x_773_;
v_isShared_786_ = v_isSharedCheck_802_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_snapshotTasks_783_);
lean_inc(v_infoState_782_);
lean_inc(v_messages_781_);
lean_inc(v_recordedDeps_780_);
lean_inc(v_cache_779_);
lean_inc(v_traceState_774_);
lean_inc(v_auxDeclNGen_778_);
lean_inc(v_ngen_777_);
lean_inc(v_nextMacroScope_776_);
lean_inc(v_env_775_);
lean_dec(v___x_773_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_802_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
uint64_t v_tid_787_; lean_object* v_traces_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_801_; 
v_tid_787_ = lean_ctor_get_uint64(v_traceState_774_, sizeof(void*)*1);
v_traces_788_ = lean_ctor_get(v_traceState_774_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v_traceState_774_);
if (v_isSharedCheck_801_ == 0)
{
v___x_790_ = v_traceState_774_;
v_isShared_791_ = v_isSharedCheck_801_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_traces_788_);
lean_dec(v_traceState_774_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_801_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_792_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_727_, v_traces_788_);
lean_dec_ref(v_traces_788_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_792_);
v___x_794_ = v___x_790_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_792_);
lean_ctor_set_uint64(v_reuseFailAlloc_800_, sizeof(void*)*1, v_tid_787_);
v___x_794_ = v_reuseFailAlloc_800_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
lean_object* v___x_796_; 
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 4, v___x_794_);
v___x_796_ = v___x_785_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_env_775_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v_nextMacroScope_776_);
lean_ctor_set(v_reuseFailAlloc_799_, 2, v_ngen_777_);
lean_ctor_set(v_reuseFailAlloc_799_, 3, v_auxDeclNGen_778_);
lean_ctor_set(v_reuseFailAlloc_799_, 4, v___x_794_);
lean_ctor_set(v_reuseFailAlloc_799_, 5, v_cache_779_);
lean_ctor_set(v_reuseFailAlloc_799_, 6, v_recordedDeps_780_);
lean_ctor_set(v_reuseFailAlloc_799_, 7, v_messages_781_);
lean_ctor_set(v_reuseFailAlloc_799_, 8, v_infoState_782_);
lean_ctor_set(v_reuseFailAlloc_799_, 9, v_snapshotTasks_783_);
v___x_796_ = v_reuseFailAlloc_799_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_st_ref_put(v___y_733_, v___x_796_);
v___x_798_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg(v_fst_735_);
return v___x_798_;
}
}
}
}
}
else
{
goto v___jp_766_;
}
}
else
{
goto v___jp_766_;
}
}
v___jp_803_:
{
double v___x_805_; double v___x_806_; double v___x_807_; uint8_t v___x_808_; 
v___x_805_ = lean_unbox_float(v_snd_752_);
v___x_806_ = lean_unbox_float(v_fst_751_);
v___x_807_ = lean_float_sub(v___x_805_, v___x_806_);
v___x_808_ = lean_float_decLt(v___y_804_, v___x_807_);
v___y_772_ = v___x_808_;
goto v___jp_771_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___boxed(lean_object* v_cls_819_, lean_object* v_collapsed_820_, lean_object* v_tag_821_, lean_object* v_opts_822_, lean_object* v_clsEnabled_823_, lean_object* v_oldTraces_824_, lean_object* v_msg_825_, lean_object* v_resStartStop_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
uint8_t v_collapsed_boxed_832_; uint8_t v_clsEnabled_boxed_833_; lean_object* v_res_834_; 
v_collapsed_boxed_832_ = lean_unbox(v_collapsed_820_);
v_clsEnabled_boxed_833_ = lean_unbox(v_clsEnabled_823_);
v_res_834_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v_cls_819_, v_collapsed_boxed_832_, v_tag_821_, v_opts_822_, v_clsEnabled_boxed_833_, v_oldTraces_824_, v_msg_825_, v_resStartStop_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec_ref(v_opts_822_);
return v_res_834_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9(void){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_848_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5));
v___x_849_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__8));
v___x_850_ = l_Lean_Name_append(v___x_849_, v___x_848_);
return v___x_850_;
}
}
static double _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10(void){
_start:
{
lean_object* v___x_851_; double v___x_852_; 
v___x_851_ = lean_unsigned_to_nat(1000000000u);
v___x_852_ = lean_float_of_nat(v___x_851_);
return v___x_852_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__11));
v___x_855_ = l_Lean_stringToMessageData(v___x_854_);
return v___x_855_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14(void){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__13));
v___x_858_ = l_Lean_stringToMessageData(v___x_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7(lean_object* v_snd_859_, lean_object* v_mvarId_860_, lean_object* v_x_861_, lean_object* v_x_862_, lean_object* v_x_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
if (lean_obj_tag(v_x_861_) == 5)
{
lean_object* v_fn_869_; lean_object* v_arg_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v_fn_869_ = lean_ctor_get(v_x_861_, 0);
lean_inc_ref(v_fn_869_);
v_arg_870_ = lean_ctor_get(v_x_861_, 1);
lean_inc_ref(v_arg_870_);
lean_dec_ref_known(v_x_861_, 2);
v___x_871_ = lean_array_set(v_x_862_, v_x_863_, v_arg_870_);
v___x_872_ = lean_unsigned_to_nat(1u);
v___x_873_ = lean_nat_sub(v_x_863_, v___x_872_);
lean_dec(v_x_863_);
v_x_861_ = v_fn_869_;
v_x_862_ = v___x_871_;
v_x_863_ = v___x_873_;
goto _start;
}
else
{
lean_dec(v_x_863_);
if (lean_obj_tag(v_x_861_) == 4)
{
lean_object* v_declName_875_; lean_object* v___f_876_; lean_object* v___f_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v_declName_875_ = lean_ctor_get(v_x_861_, 0);
lean_inc_n(v_declName_875_, 2);
lean_dec_ref_known(v_x_861_, 2);
v___f_876_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0));
v___f_877_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1));
v___x_878_ = l_Lean_instInhabitedExpr;
v___x_879_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_declName_875_, v___y_867_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v_a_880_; 
v_a_880_ = lean_ctor_get(v___x_879_, 0);
lean_inc(v_a_880_);
lean_dec_ref_known(v___x_879_, 1);
if (lean_obj_tag(v_a_880_) == 1)
{
lean_object* v_val_881_; lean_object* v_toCold_882_; lean_object* v_options_883_; lean_object* v_majorPos_884_; lean_object* v_arity_885_; lean_object* v_insterestingCtors_886_; lean_object* v_inheritedTraceOptions_887_; uint8_t v_hasTrace_888_; lean_object* v___f_889_; lean_object* v___x_890_; uint8_t v___x_891_; 
v_val_881_ = lean_ctor_get(v_a_880_, 0);
lean_inc(v_val_881_);
lean_dec_ref_known(v_a_880_, 1);
v_toCold_882_ = lean_ctor_get(v___y_866_, 0);
v_options_883_ = lean_ctor_get(v_toCold_882_, 2);
v_majorPos_884_ = lean_ctor_get(v_val_881_, 1);
lean_inc(v_majorPos_884_);
v_arity_885_ = lean_ctor_get(v_val_881_, 2);
lean_inc_n(v_arity_885_, 2);
v_insterestingCtors_886_ = lean_ctor_get(v_val_881_, 3);
lean_inc_ref(v_insterestingCtors_886_);
lean_dec(v_val_881_);
v_inheritedTraceOptions_887_ = lean_ctor_get(v_toCold_882_, 11);
v_hasTrace_888_ = lean_ctor_get_uint8(v_options_883_, sizeof(void*)*1);
lean_inc_ref(v_x_862_);
v___f_889_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___boxed), 15, 9);
lean_closure_set(v___f_889_, 0, v___x_878_);
lean_closure_set(v___f_889_, 1, v_x_862_);
lean_closure_set(v___f_889_, 2, v_majorPos_884_);
lean_closure_set(v___f_889_, 3, v_insterestingCtors_886_);
lean_closure_set(v___f_889_, 4, v_declName_875_);
lean_closure_set(v___f_889_, 5, v_snd_859_);
lean_closure_set(v___f_889_, 6, v_arity_885_);
lean_closure_set(v___f_889_, 7, v_mvarId_860_);
lean_closure_set(v___f_889_, 8, v___f_876_);
v___x_890_ = lean_array_get_size(v_x_862_);
lean_dec_ref(v_x_862_);
v___x_891_ = lean_nat_dec_lt(v___x_890_, v_arity_885_);
lean_dec(v_arity_885_);
if (v_hasTrace_888_ == 0)
{
lean_object* v___x_892_; 
v___x_892_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2(v___x_891_, v___f_889_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
return v___x_892_;
}
else
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; uint8_t v___x_896_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v_a_900_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v_a_915_; 
v___x_893_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5));
v___x_894_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__6));
v___x_895_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9);
v___x_896_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_887_, v_options_883_, v___x_895_);
if (v___x_896_ == 0)
{
lean_object* v___x_965_; uint8_t v___x_966_; 
v___x_965_ = l_Lean_trace_profiler;
v___x_966_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_options_883_, v___x_965_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2(v___x_891_, v___f_889_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
return v___x_967_;
}
else
{
goto v___jp_924_;
}
}
else
{
goto v___jp_924_;
}
v___jp_897_:
{
lean_object* v___x_901_; double v___x_902_; double v___x_903_; double v___x_904_; double v___x_905_; double v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_901_ = lean_io_mono_nanos_now();
v___x_902_ = lean_float_of_nat(v___y_898_);
v___x_903_ = lean_float_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10);
v___x_904_ = lean_float_div(v___x_902_, v___x_903_);
v___x_905_ = lean_float_of_nat(v___x_901_);
v___x_906_ = lean_float_div(v___x_905_, v___x_903_);
v___x_907_ = lean_box_float(v___x_904_);
v___x_908_ = lean_box_float(v___x_906_);
v___x_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_907_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_910_, 0, v_a_900_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_893_, v_hasTrace_888_, v___x_894_, v_options_883_, v___x_896_, v___y_899_, v___f_877_, v___x_910_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
return v___x_911_;
}
v___jp_912_:
{
lean_object* v___x_916_; double v___x_917_; double v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_916_ = lean_io_get_num_heartbeats();
v___x_917_ = lean_float_of_nat(v___y_914_);
v___x_918_ = lean_float_of_nat(v___x_916_);
v___x_919_ = lean_box_float(v___x_917_);
v___x_920_ = lean_box_float(v___x_918_);
v___x_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_919_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
v___x_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_922_, 0, v_a_915_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_893_, v_hasTrace_888_, v___x_894_, v_options_883_, v___x_896_, v___y_913_, v___f_877_, v___x_922_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
return v___x_923_;
}
v___jp_924_:
{
lean_object* v___x_925_; lean_object* v_a_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v___x_925_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___y_867_);
v_a_926_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_a_926_);
lean_dec_ref(v___x_925_);
v___x_927_ = l_Lean_trace_profiler_useHeartbeats;
v___x_928_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_options_883_, v___x_927_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = lean_io_mono_nanos_now();
v___x_930_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2(v___x_891_, v___f_889_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_938_ == 0)
{
v___x_933_ = v___x_930_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_930_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set_tag(v___x_933_, 1);
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_931_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
v___y_898_ = v___x_929_;
v___y_899_ = v_a_926_;
v_a_900_ = v___x_936_;
goto v___jp_897_;
}
}
}
else
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_946_; 
v_a_939_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_946_ == 0)
{
v___x_941_ = v___x_930_;
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_930_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_944_; 
if (v_isShared_942_ == 0)
{
lean_ctor_set_tag(v___x_941_, 0);
v___x_944_ = v___x_941_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_a_939_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
v___y_898_ = v___x_929_;
v___y_899_ = v_a_926_;
v_a_900_ = v___x_944_;
goto v___jp_897_;
}
}
}
}
else
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = lean_io_get_num_heartbeats();
v___x_948_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2(v___x_891_, v___f_889_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_948_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_948_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
lean_ctor_set_tag(v___x_951_, 1);
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
v___y_913_ = v_a_926_;
v___y_914_ = v___x_947_;
v_a_915_ = v___x_954_;
goto v___jp_912_;
}
}
}
else
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
v_a_957_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_948_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_948_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
lean_ctor_set_tag(v___x_959_, 0);
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
v___y_913_ = v_a_926_;
v___y_914_ = v___x_947_;
v_a_915_ = v___x_962_;
goto v___jp_912_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_968_; lean_object* v___x_969_; 
lean_dec(v_a_880_);
lean_dec(v_declName_875_);
lean_dec_ref(v_x_862_);
lean_dec(v_mvarId_860_);
lean_dec_ref(v_snd_859_);
v___x_968_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12);
v___x_969_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_968_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
return v___x_969_;
}
}
else
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
lean_dec(v_declName_875_);
lean_dec_ref(v_x_862_);
lean_dec(v_mvarId_860_);
lean_dec_ref(v_snd_859_);
v_a_970_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_879_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_879_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_970_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
else
{
lean_object* v___x_978_; lean_object* v___x_979_; 
lean_dec_ref(v_x_862_);
lean_dec_ref(v_x_861_);
lean_dec(v_mvarId_860_);
lean_dec_ref(v_snd_859_);
v___x_978_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14);
v___x_979_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_978_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
return v___x_979_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___boxed(lean_object* v_snd_980_, lean_object* v_mvarId_981_, lean_object* v_x_982_, lean_object* v_x_983_, lean_object* v_x_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7(v_snd_980_, v_mvarId_981_, v_x_982_, v_x_983_, v_x_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
return v_res_990_;
}
}
static lean_object* _init_l_Lean_Meta_reduceSparseCasesOn___closed__1(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = ((lean_object*)(l_Lean_Meta_reduceSparseCasesOn___closed__0));
v___x_993_ = l_Lean_stringToMessageData(v___x_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceSparseCasesOn(lean_object* v_mvarId_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
lean_object* v___x_1000_; 
lean_inc(v_mvarId_994_);
v___x_1000_ = l_Lean_MVarId_getType(v_mvarId_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1002_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 1);
v___x_1002_ = l_Lean_Meta_matchEqHEqLHS_x3f(v_a_1001_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_a_1003_);
lean_dec_ref_known(v___x_1002_, 1);
if (lean_obj_tag(v_a_1003_) == 1)
{
lean_object* v_val_1004_; lean_object* v_snd_1005_; lean_object* v_dummy_1006_; lean_object* v_nargs_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v_val_1004_ = lean_ctor_get(v_a_1003_, 0);
lean_inc(v_val_1004_);
lean_dec_ref_known(v_a_1003_, 1);
v_snd_1005_ = lean_ctor_get(v_val_1004_, 1);
lean_inc_n(v_snd_1005_, 2);
lean_dec(v_val_1004_);
v_dummy_1006_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0);
v_nargs_1007_ = l_Lean_Expr_getAppNumArgs(v_snd_1005_);
lean_inc(v_nargs_1007_);
v___x_1008_ = lean_mk_array(v_nargs_1007_, v_dummy_1006_);
v___x_1009_ = lean_unsigned_to_nat(1u);
v___x_1010_ = lean_nat_sub(v_nargs_1007_, v___x_1009_);
lean_dec(v_nargs_1007_);
v___x_1011_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7(v_snd_1005_, v_mvarId_994_, v_snd_1005_, v___x_1008_, v___x_1010_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
return v___x_1011_;
}
else
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
lean_dec(v_a_1003_);
lean_dec(v_mvarId_994_);
v___x_1012_ = lean_obj_once(&l_Lean_Meta_reduceSparseCasesOn___closed__1, &l_Lean_Meta_reduceSparseCasesOn___closed__1_once, _init_l_Lean_Meta_reduceSparseCasesOn___closed__1);
v___x_1013_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1012_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
return v___x_1013_;
}
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
lean_dec(v_mvarId_994_);
v_a_1014_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_1002_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1002_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_dec(v_mvarId_994_);
v_a_1022_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_1000_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1000_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceSparseCasesOn___boxed(lean_object* v_mvarId_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_Meta_reduceSparseCasesOn(v_mvarId_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
lean_dec(v_a_1032_);
lean_dec_ref(v_a_1031_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3(lean_object* v_00_u03b1_1037_, lean_object* v_msg_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v_msg_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___boxed(lean_object* v_00_u03b1_1045_, lean_object* v_msg_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3(v_00_u03b1_1045_, v_msg_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10(lean_object* v_00_u03b1_1053_, lean_object* v_x_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg(v_x_1054_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___boxed(lean_object* v_00_u03b1_1061_, lean_object* v_x_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10(v_00_u03b1_1061_, v_x_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(lean_object* v_mvarId_1069_, lean_object* v_x_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1069_, v_x_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1084_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1079_ = v___x_1076_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1076_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1077_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
v_a_1085_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1076_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1076_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg___boxed(lean_object* v_mvarId_1093_, lean_object* v_x_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1093_, v_x_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2(lean_object* v_00_u03b1_1101_, lean_object* v_mvarId_1102_, lean_object* v_x_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1102_, v_x_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___boxed(lean_object* v_00_u03b1_1110_, lean_object* v_mvarId_1111_, lean_object* v_x_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2(v_00_u03b1_1110_, v_mvarId_1111_, v_x_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_splitSparseCasesOn_spec__1(lean_object* v_a_1119_, lean_object* v_a_1120_){
_start:
{
if (lean_obj_tag(v_a_1119_) == 0)
{
lean_object* v___x_1121_; 
v___x_1121_ = l_List_reverse___redArg(v_a_1120_);
return v___x_1121_;
}
else
{
lean_object* v_head_1122_; lean_object* v_tail_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1132_; 
v_head_1122_ = lean_ctor_get(v_a_1119_, 0);
v_tail_1123_ = lean_ctor_get(v_a_1119_, 1);
v_isSharedCheck_1132_ = !lean_is_exclusive(v_a_1119_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1125_ = v_a_1119_;
v_isShared_1126_ = v_isSharedCheck_1132_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_tail_1123_);
lean_inc(v_head_1122_);
lean_dec(v_a_1119_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1132_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; lean_object* v___x_1129_; 
v___x_1127_ = l_Lean_MessageData_ofExpr(v_head_1122_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 1, v_a_1120_);
lean_ctor_set(v___x_1125_, 0, v___x_1127_);
v___x_1129_ = v___x_1125_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1127_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v_a_1120_);
v___x_1129_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
v_a_1119_ = v_tail_1123_;
v_a_1120_ = v___x_1129_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__0));
v___x_1135_ = l_Lean_stringToMessageData(v___x_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0(uint8_t v___y_1136_, lean_object* v_mvarId_1137_, lean_object* v___f_1138_, lean_object* v_declName_1139_, lean_object* v_val_1140_, lean_object* v___x_1141_, lean_object* v_fields_1142_, uint8_t v___x_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; 
if (v___y_1136_ == 0)
{
lean_object* v___x_1205_; 
lean_dec_ref(v_fields_1142_);
lean_dec_ref(v_val_1140_);
lean_dec(v_declName_1139_);
v___x_1205_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_1137_, v___f_1138_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
return v___x_1205_;
}
else
{
lean_object* v___x_1206_; lean_object* v___x_1207_; uint8_t v___x_1208_; 
lean_dec_ref(v___f_1138_);
v___x_1206_ = lean_array_get_size(v_fields_1142_);
v___x_1207_ = lean_unsigned_to_nat(1u);
v___x_1208_ = lean_nat_dec_eq(v___x_1206_, v___x_1207_);
if (v___x_1208_ == 0)
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1209_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1);
lean_inc_ref(v_fields_1142_);
v___x_1210_ = lean_array_to_list(v_fields_1142_);
v___x_1211_ = lean_box(0);
v___x_1212_ = l_List_mapTR_loop___at___00Lean_Meta_splitSparseCasesOn_spec__1(v___x_1210_, v___x_1211_);
v___x_1213_ = l_Lean_MessageData_ofList(v___x_1212_);
v___x_1214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1209_);
lean_ctor_set(v___x_1214_, 1, v___x_1213_);
v___x_1215_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1214_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_dec_ref_known(v___x_1215_, 1);
v___y_1150_ = v___y_1144_;
v___y_1151_ = v___y_1145_;
v___y_1152_ = v___y_1146_;
v___y_1153_ = v___y_1147_;
goto v___jp_1149_;
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_dec_ref(v_fields_1142_);
lean_dec_ref(v_val_1140_);
lean_dec(v_declName_1139_);
lean_dec(v_mvarId_1137_);
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1215_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1215_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1216_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
else
{
v___y_1150_ = v___y_1144_;
v___y_1151_ = v___y_1145_;
v___y_1152_ = v___y_1146_;
v___y_1153_ = v___y_1147_;
goto v___jp_1149_;
}
}
v___jp_1149_:
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Lean_Meta_getSparseCasesOnEq(v_declName_1139_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; lean_object* v___x_1156_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
lean_inc(v_a_1155_);
lean_dec_ref_known(v___x_1154_, 1);
lean_inc(v_mvarId_1137_);
v___x_1156_ = l_Lean_MVarId_getType(v_mvarId_1137_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1158_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_a_1157_);
lean_dec_ref_known(v___x_1156_, 1);
v___x_1158_ = l_Lean_Meta_matchEqHEqLHS_x3f(v_a_1157_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_a_1159_);
lean_dec_ref_known(v___x_1158_, 1);
if (lean_obj_tag(v_a_1159_) == 1)
{
lean_object* v_val_1160_; lean_object* v_snd_1161_; lean_object* v_arity_1162_; lean_object* v___x_1163_; lean_object* v_nargs_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v_dummy_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v_val_1160_ = lean_ctor_get(v_a_1159_, 0);
lean_inc(v_val_1160_);
lean_dec_ref_known(v_a_1159_, 1);
v_snd_1161_ = lean_ctor_get(v_val_1160_, 1);
lean_inc(v_snd_1161_);
lean_dec(v_val_1160_);
v_arity_1162_ = lean_ctor_get(v_val_1140_, 2);
lean_inc(v_arity_1162_);
lean_dec_ref(v_val_1140_);
v___x_1163_ = l_Lean_Expr_getAppFn(v_snd_1161_);
v_nargs_1164_ = l_Lean_Expr_getAppNumArgs(v_snd_1161_);
v___x_1165_ = l_Lean_Expr_constLevels_x21(v___x_1163_);
lean_dec_ref(v___x_1163_);
v___x_1166_ = l_Lean_mkConst(v_a_1155_, v___x_1165_);
v_dummy_1167_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0);
lean_inc(v_nargs_1164_);
v___x_1168_ = lean_mk_array(v_nargs_1164_, v_dummy_1167_);
v___x_1169_ = lean_unsigned_to_nat(1u);
v___x_1170_ = lean_nat_sub(v_nargs_1164_, v___x_1169_);
lean_dec(v_nargs_1164_);
v___x_1171_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_snd_1161_, v___x_1168_, v___x_1170_);
v___x_1172_ = lean_unsigned_to_nat(0u);
v___x_1173_ = l_Array_toSubarray___redArg(v___x_1171_, v___x_1172_, v_arity_1162_);
v___x_1174_ = l_Subarray_copy___redArg(v___x_1173_);
v___x_1175_ = l_Lean_mkAppN(v___x_1166_, v___x_1174_);
lean_dec_ref(v___x_1174_);
v___x_1176_ = lean_array_get(v___x_1141_, v_fields_1142_, v___x_1172_);
lean_dec_ref(v_fields_1142_);
v___x_1177_ = l_Lean_Expr_app___override(v___x_1175_, v___x_1176_);
v___x_1178_ = l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq(v_mvarId_1137_, v___x_1177_, v___x_1143_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
return v___x_1178_;
}
else
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
lean_dec(v_a_1159_);
lean_dec(v_a_1155_);
lean_dec_ref(v_fields_1142_);
lean_dec_ref(v_val_1140_);
lean_dec(v_mvarId_1137_);
v___x_1179_ = lean_obj_once(&l_Lean_Meta_reduceSparseCasesOn___closed__1, &l_Lean_Meta_reduceSparseCasesOn___closed__1_once, _init_l_Lean_Meta_reduceSparseCasesOn___closed__1);
v___x_1180_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1179_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
return v___x_1180_;
}
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
lean_dec(v_a_1155_);
lean_dec_ref(v_fields_1142_);
lean_dec_ref(v_val_1140_);
lean_dec(v_mvarId_1137_);
v_a_1181_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1158_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1158_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1181_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
else
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
lean_dec(v_a_1155_);
lean_dec_ref(v_fields_1142_);
lean_dec_ref(v_val_1140_);
lean_dec(v_mvarId_1137_);
v_a_1189_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1191_ = v___x_1156_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1156_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1194_; 
if (v_isShared_1192_ == 0)
{
v___x_1194_ = v___x_1191_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1189_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
else
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
lean_dec_ref(v_fields_1142_);
lean_dec_ref(v_val_1140_);
lean_dec(v_mvarId_1137_);
v_a_1197_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1154_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1154_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed(lean_object* v___y_1224_, lean_object* v_mvarId_1225_, lean_object* v___f_1226_, lean_object* v_declName_1227_, lean_object* v_val_1228_, lean_object* v___x_1229_, lean_object* v_fields_1230_, lean_object* v___x_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
uint8_t v___y_31417__boxed_1237_; uint8_t v___x_31422__boxed_1238_; lean_object* v_res_1239_; 
v___y_31417__boxed_1237_ = lean_unbox(v___y_1224_);
v___x_31422__boxed_1238_ = lean_unbox(v___x_1231_);
v_res_1239_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0(v___y_31417__boxed_1237_, v_mvarId_1225_, v___f_1226_, v_declName_1227_, v_val_1228_, v___x_1229_, v_fields_1230_, v___x_31422__boxed_1238_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec_ref(v___x_1229_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(lean_object* v_declName_1240_, lean_object* v_val_1241_, uint8_t v___x_1242_, size_t v_sz_1243_, size_t v_i_1244_, lean_object* v_bs_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
uint8_t v___x_1251_; 
v___x_1251_ = lean_usize_dec_lt(v_i_1244_, v_sz_1243_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; 
lean_dec_ref(v_val_1241_);
lean_dec(v_declName_1240_);
v___x_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1252_, 0, v_bs_1245_);
return v___x_1252_;
}
else
{
lean_object* v_v_1253_; lean_object* v_toInductionSubgoal_1254_; lean_object* v_ctorName_1255_; lean_object* v_mvarId_1256_; lean_object* v_fields_1257_; lean_object* v___f_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v_bs_x27_1261_; uint8_t v___y_1263_; 
v_v_1253_ = lean_array_uget_borrowed(v_bs_1245_, v_i_1244_);
v_toInductionSubgoal_1254_ = lean_ctor_get(v_v_1253_, 0);
v_ctorName_1255_ = lean_ctor_get(v_v_1253_, 1);
lean_inc(v_ctorName_1255_);
v_mvarId_1256_ = lean_ctor_get(v_toInductionSubgoal_1254_, 0);
lean_inc(v_mvarId_1256_);
v_fields_1257_ = lean_ctor_get(v_toInductionSubgoal_1254_, 1);
lean_inc_ref(v_fields_1257_);
v___f_1258_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0));
v___x_1259_ = l_Lean_instInhabitedExpr;
v___x_1260_ = lean_unsigned_to_nat(0u);
v_bs_x27_1261_ = lean_array_uset(v_bs_1245_, v_i_1244_, v___x_1260_);
if (lean_obj_tag(v_ctorName_1255_) == 0)
{
v___y_1263_ = v___x_1251_;
goto v___jp_1262_;
}
else
{
lean_dec_ref_known(v_ctorName_1255_, 1);
v___y_1263_ = v___x_1242_;
goto v___jp_1262_;
}
v___jp_1262_:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___y_1266_; lean_object* v___x_1267_; 
v___x_1264_ = lean_box(v___y_1263_);
v___x_1265_ = lean_box(v___x_1242_);
lean_inc_ref(v_val_1241_);
lean_inc(v_declName_1240_);
lean_inc(v_mvarId_1256_);
v___y_1266_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed), 13, 8);
lean_closure_set(v___y_1266_, 0, v___x_1264_);
lean_closure_set(v___y_1266_, 1, v_mvarId_1256_);
lean_closure_set(v___y_1266_, 2, v___f_1258_);
lean_closure_set(v___y_1266_, 3, v_declName_1240_);
lean_closure_set(v___y_1266_, 4, v_val_1241_);
lean_closure_set(v___y_1266_, 5, v___x_1259_);
lean_closure_set(v___y_1266_, 6, v_fields_1257_);
lean_closure_set(v___y_1266_, 7, v___x_1265_);
v___x_1267_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1256_, v___y_1266_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; size_t v___x_1269_; size_t v___x_1270_; lean_object* v___x_1271_; 
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1268_);
lean_dec_ref_known(v___x_1267_, 1);
v___x_1269_ = ((size_t)1ULL);
v___x_1270_ = lean_usize_add(v_i_1244_, v___x_1269_);
v___x_1271_ = lean_array_uset(v_bs_x27_1261_, v_i_1244_, v_a_1268_);
v_i_1244_ = v___x_1270_;
v_bs_1245_ = v___x_1271_;
goto _start;
}
else
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
lean_dec_ref(v_bs_x27_1261_);
lean_dec_ref(v_val_1241_);
lean_dec(v_declName_1240_);
v_a_1273_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v___x_1267_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1267_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___boxed(lean_object* v_declName_1281_, lean_object* v_val_1282_, lean_object* v___x_1283_, lean_object* v_sz_1284_, lean_object* v_i_1285_, lean_object* v_bs_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
uint8_t v___x_31601__boxed_1292_; size_t v_sz_boxed_1293_; size_t v_i_boxed_1294_; lean_object* v_res_1295_; 
v___x_31601__boxed_1292_ = lean_unbox(v___x_1283_);
v_sz_boxed_1293_ = lean_unbox_usize(v_sz_1284_);
lean_dec(v_sz_1284_);
v_i_boxed_1294_ = lean_unbox_usize(v_i_1285_);
lean_dec(v_i_1285_);
v_res_1295_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(v_declName_1281_, v_val_1282_, v___x_31601__boxed_1292_, v_sz_boxed_1293_, v_i_boxed_1294_, v_bs_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(lean_object* v___x_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v_toCold_1302_; lean_object* v_options_1303_; uint8_t v_hasTrace_1304_; 
v_toCold_1302_ = lean_ctor_get(v___y_1299_, 0);
v_options_1303_ = lean_ctor_get(v_toCold_1302_, 2);
v_hasTrace_1304_ = lean_ctor_get_uint8(v_options_1303_, sizeof(void*)*1);
if (v_hasTrace_1304_ == 0)
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
lean_dec(v___x_1296_);
v___x_1305_ = lean_box(v_hasTrace_1304_);
v___x_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
return v___x_1306_;
}
else
{
lean_object* v_inheritedTraceOptions_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v_inheritedTraceOptions_1307_ = lean_ctor_get(v_toCold_1302_, 11);
v___x_1308_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__8));
v___x_1309_ = l_Lean_Name_append(v___x_1308_, v___x_1296_);
v___x_1310_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1307_, v_options_1303_, v___x_1309_);
lean_dec(v___x_1309_);
v___x_1311_ = lean_box(v___x_1310_);
v___x_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
return v___x_1312_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___boxed(lean_object* v___x_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(v___x_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(lean_object* v_cls_1322_, lean_object* v_msg_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v_ref_1329_; lean_object* v___x_1330_; lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1376_; 
v_ref_1329_ = lean_ctor_get(v___y_1326_, 2);
v___x_1330_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msg_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1333_ = v___x_1330_;
v_isShared_1334_ = v_isSharedCheck_1376_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1376_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1335_; lean_object* v_traceState_1336_; lean_object* v_env_1337_; lean_object* v_nextMacroScope_1338_; lean_object* v_ngen_1339_; lean_object* v_auxDeclNGen_1340_; lean_object* v_cache_1341_; lean_object* v_recordedDeps_1342_; lean_object* v_messages_1343_; lean_object* v_infoState_1344_; lean_object* v_snapshotTasks_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1375_; 
v___x_1335_ = lean_st_ref_take(v___y_1327_);
v_traceState_1336_ = lean_ctor_get(v___x_1335_, 4);
v_env_1337_ = lean_ctor_get(v___x_1335_, 0);
v_nextMacroScope_1338_ = lean_ctor_get(v___x_1335_, 1);
v_ngen_1339_ = lean_ctor_get(v___x_1335_, 2);
v_auxDeclNGen_1340_ = lean_ctor_get(v___x_1335_, 3);
v_cache_1341_ = lean_ctor_get(v___x_1335_, 5);
v_recordedDeps_1342_ = lean_ctor_get(v___x_1335_, 6);
v_messages_1343_ = lean_ctor_get(v___x_1335_, 7);
v_infoState_1344_ = lean_ctor_get(v___x_1335_, 8);
v_snapshotTasks_1345_ = lean_ctor_get(v___x_1335_, 9);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1347_ = v___x_1335_;
v_isShared_1348_ = v_isSharedCheck_1375_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_snapshotTasks_1345_);
lean_inc(v_infoState_1344_);
lean_inc(v_messages_1343_);
lean_inc(v_recordedDeps_1342_);
lean_inc(v_cache_1341_);
lean_inc(v_traceState_1336_);
lean_inc(v_auxDeclNGen_1340_);
lean_inc(v_ngen_1339_);
lean_inc(v_nextMacroScope_1338_);
lean_inc(v_env_1337_);
lean_dec(v___x_1335_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1375_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
uint64_t v_tid_1349_; lean_object* v_traces_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1374_; 
v_tid_1349_ = lean_ctor_get_uint64(v_traceState_1336_, sizeof(void*)*1);
v_traces_1350_ = lean_ctor_get(v_traceState_1336_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v_traceState_1336_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1352_ = v_traceState_1336_;
v_isShared_1353_ = v_isSharedCheck_1374_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_traces_1350_);
lean_dec(v_traceState_1336_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1374_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; double v___x_1356_; uint8_t v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1365_; 
v___x_1354_ = lean_box(0);
v___x_1355_ = lean_box(0);
v___x_1356_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0);
v___x_1357_ = 0;
v___x_1358_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__6));
v___x_1359_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1359_, 0, v_cls_1322_);
lean_ctor_set(v___x_1359_, 1, v___x_1355_);
lean_ctor_set(v___x_1359_, 2, v___x_1358_);
lean_ctor_set_float(v___x_1359_, sizeof(void*)*3, v___x_1356_);
lean_ctor_set_float(v___x_1359_, sizeof(void*)*3 + 8, v___x_1356_);
lean_ctor_set_uint8(v___x_1359_, sizeof(void*)*3 + 16, v___x_1357_);
v___x_1360_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___closed__0));
v___x_1361_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1359_);
lean_ctor_set(v___x_1361_, 1, v_a_1331_);
lean_ctor_set(v___x_1361_, 2, v___x_1360_);
lean_inc(v_ref_1329_);
v___x_1362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1362_, 0, v_ref_1329_);
lean_ctor_set(v___x_1362_, 1, v___x_1361_);
v___x_1363_ = l_Lean_PersistentArray_push___redArg(v_traces_1350_, v___x_1362_);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 0, v___x_1363_);
v___x_1365_ = v___x_1352_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1363_);
lean_ctor_set_uint64(v_reuseFailAlloc_1373_, sizeof(void*)*1, v_tid_1349_);
v___x_1365_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
lean_object* v___x_1367_; 
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 4, v___x_1365_);
v___x_1367_ = v___x_1347_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_env_1337_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_nextMacroScope_1338_);
lean_ctor_set(v_reuseFailAlloc_1372_, 2, v_ngen_1339_);
lean_ctor_set(v_reuseFailAlloc_1372_, 3, v_auxDeclNGen_1340_);
lean_ctor_set(v_reuseFailAlloc_1372_, 4, v___x_1365_);
lean_ctor_set(v_reuseFailAlloc_1372_, 5, v_cache_1341_);
lean_ctor_set(v_reuseFailAlloc_1372_, 6, v_recordedDeps_1342_);
lean_ctor_set(v_reuseFailAlloc_1372_, 7, v_messages_1343_);
lean_ctor_set(v_reuseFailAlloc_1372_, 8, v_infoState_1344_);
lean_ctor_set(v_reuseFailAlloc_1372_, 9, v_snapshotTasks_1345_);
v___x_1367_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
lean_object* v___x_1368_; lean_object* v___x_1370_; 
v___x_1368_ = lean_st_ref_put(v___y_1327_, v___x_1367_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v___x_1354_);
v___x_1370_ = v___x_1333_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1354_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___boxed(lean_object* v_cls_1377_, lean_object* v_msg_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v_cls_1377_, v_msg_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(lean_object* v_declName_1385_, lean_object* v_val_1386_, uint8_t v___x_1387_, size_t v_sz_1388_, size_t v_i_1389_, lean_object* v_bs_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
uint8_t v___x_1396_; 
v___x_1396_ = lean_usize_dec_lt(v_i_1389_, v_sz_1388_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; 
lean_dec_ref(v_val_1386_);
lean_dec(v_declName_1385_);
v___x_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1397_, 0, v_bs_1390_);
return v___x_1397_;
}
else
{
lean_object* v_v_1398_; lean_object* v_toInductionSubgoal_1399_; lean_object* v_ctorName_1400_; lean_object* v_mvarId_1401_; lean_object* v_fields_1402_; lean_object* v___f_1403_; lean_object* v___x_1404_; uint8_t v___x_1405_; lean_object* v___x_1406_; lean_object* v_bs_x27_1407_; uint8_t v___y_1409_; 
v_v_1398_ = lean_array_uget_borrowed(v_bs_1390_, v_i_1389_);
v_toInductionSubgoal_1399_ = lean_ctor_get(v_v_1398_, 0);
v_ctorName_1400_ = lean_ctor_get(v_v_1398_, 1);
lean_inc(v_ctorName_1400_);
v_mvarId_1401_ = lean_ctor_get(v_toInductionSubgoal_1399_, 0);
lean_inc(v_mvarId_1401_);
v_fields_1402_ = lean_ctor_get(v_toInductionSubgoal_1399_, 1);
lean_inc_ref(v_fields_1402_);
v___f_1403_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0));
v___x_1404_ = l_Lean_instInhabitedExpr;
v___x_1405_ = 0;
v___x_1406_ = lean_unsigned_to_nat(0u);
v_bs_x27_1407_ = lean_array_uset(v_bs_1390_, v_i_1389_, v___x_1406_);
if (lean_obj_tag(v_ctorName_1400_) == 0)
{
v___y_1409_ = v___x_1387_;
goto v___jp_1408_;
}
else
{
lean_dec_ref_known(v_ctorName_1400_, 1);
v___y_1409_ = v___x_1405_;
goto v___jp_1408_;
}
v___jp_1408_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___y_1412_; lean_object* v___x_1413_; 
v___x_1410_ = lean_box(v___y_1409_);
v___x_1411_ = lean_box(v___x_1405_);
lean_inc_ref(v_val_1386_);
lean_inc(v_declName_1385_);
lean_inc(v_mvarId_1401_);
v___y_1412_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed), 13, 8);
lean_closure_set(v___y_1412_, 0, v___x_1410_);
lean_closure_set(v___y_1412_, 1, v_mvarId_1401_);
lean_closure_set(v___y_1412_, 2, v___f_1403_);
lean_closure_set(v___y_1412_, 3, v_declName_1385_);
lean_closure_set(v___y_1412_, 4, v_val_1386_);
lean_closure_set(v___y_1412_, 5, v___x_1404_);
lean_closure_set(v___y_1412_, 6, v_fields_1402_);
lean_closure_set(v___y_1412_, 7, v___x_1411_);
v___x_1413_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1401_, v___y_1412_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; size_t v___x_1415_; size_t v___x_1416_; lean_object* v___x_1417_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
lean_inc(v_a_1414_);
lean_dec_ref_known(v___x_1413_, 1);
v___x_1415_ = ((size_t)1ULL);
v___x_1416_ = lean_usize_add(v_i_1389_, v___x_1415_);
v___x_1417_ = lean_array_uset(v_bs_x27_1407_, v_i_1389_, v_a_1414_);
v_i_1389_ = v___x_1416_;
v_bs_1390_ = v___x_1417_;
goto _start;
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
lean_dec_ref(v_bs_x27_1407_);
lean_dec_ref(v_val_1386_);
lean_dec(v_declName_1385_);
v_a_1419_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1413_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1413_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4___boxed(lean_object* v_declName_1427_, lean_object* v_val_1428_, lean_object* v___x_1429_, lean_object* v_sz_1430_, lean_object* v_i_1431_, lean_object* v_bs_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
uint8_t v___x_31806__boxed_1438_; size_t v_sz_boxed_1439_; size_t v_i_boxed_1440_; lean_object* v_res_1441_; 
v___x_31806__boxed_1438_ = lean_unbox(v___x_1429_);
v_sz_boxed_1439_ = lean_unbox_usize(v_sz_1430_);
lean_dec(v_sz_1430_);
v_i_boxed_1440_ = lean_unbox_usize(v_i_1431_);
lean_dec(v_i_1431_);
v_res_1441_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(v_declName_1427_, v_val_1428_, v___x_31806__boxed_1438_, v_sz_boxed_1439_, v_i_boxed_1440_, v_bs_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
return v_res_1441_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1445_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__1));
v___x_1446_ = l_Lean_stringToMessageData(v___x_1445_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(lean_object* v_val_1447_, lean_object* v___x_1448_, lean_object* v_x_1449_, lean_object* v_mvarId_1450_, lean_object* v_declName_1451_, uint8_t v___x_1452_, lean_object* v_____r_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v_majorPos_1484_; lean_object* v_arity_1485_; lean_object* v_insterestingCtors_1486_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___x_1506_; uint8_t v___x_1507_; 
v_majorPos_1484_ = lean_ctor_get(v_val_1447_, 1);
v_arity_1485_ = lean_ctor_get(v_val_1447_, 2);
v_insterestingCtors_1486_ = lean_ctor_get(v_val_1447_, 3);
v___x_1506_ = lean_array_get_size(v_x_1449_);
v___x_1507_ = lean_nat_dec_lt(v___x_1506_, v_arity_1485_);
if (v___x_1507_ == 0)
{
v___y_1488_ = v___y_1454_;
v___y_1489_ = v___y_1455_;
v___y_1490_ = v___y_1456_;
v___y_1491_ = v___y_1457_;
goto v___jp_1487_;
}
else
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
lean_dec(v_declName_1451_);
lean_dec(v_mvarId_1450_);
lean_dec_ref(v_val_1447_);
v___x_1508_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1);
v___x_1509_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1508_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1509_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1509_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
v___jp_1459_:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1466_ = lean_array_get_borrowed(v___x_1448_, v_x_1449_, v___y_1461_);
lean_dec(v___y_1461_);
v___x_1467_ = l_Lean_Expr_fvarId_x21(v___x_1466_);
v___x_1468_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__0));
v___x_1469_ = 0;
v___x_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1470_, 0, v___y_1460_);
v___x_1471_ = l_Lean_MVarId_cases(v_mvarId_1450_, v___x_1467_, v___x_1468_, v___x_1469_, v___x_1470_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v_a_1472_; size_t v_sz_1473_; size_t v___x_1474_; lean_object* v___x_1475_; 
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_a_1472_);
lean_dec_ref_known(v___x_1471_, 1);
v_sz_1473_ = lean_array_size(v_a_1472_);
v___x_1474_ = ((size_t)0ULL);
v___x_1475_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(v_declName_1451_, v_val_1447_, v___x_1452_, v_sz_1473_, v___x_1474_, v_a_1472_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
return v___x_1475_;
}
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
lean_dec(v_declName_1451_);
lean_dec_ref(v_val_1447_);
v_a_1476_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1471_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1471_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
v___jp_1487_:
{
lean_object* v___x_1492_; uint8_t v___x_1493_; 
v___x_1492_ = lean_array_get_borrowed(v___x_1448_, v_x_1449_, v_majorPos_1484_);
v___x_1493_ = l_Lean_Expr_isFVar(v___x_1492_);
if (v___x_1493_ == 0)
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
lean_dec(v_declName_1451_);
lean_dec(v_mvarId_1450_);
lean_dec_ref(v_val_1447_);
v___x_1494_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__2);
lean_inc(v___x_1492_);
v___x_1495_ = l_Lean_indentExpr(v___x_1492_);
v___x_1496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1494_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
v___x_1497_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1496_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1497_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1497_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1498_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
else
{
lean_inc(v_majorPos_1484_);
lean_inc_ref(v_insterestingCtors_1486_);
v___y_1460_ = v_insterestingCtors_1486_;
v___y_1461_ = v_majorPos_1484_;
v___y_1462_ = v___y_1488_;
v___y_1463_ = v___y_1489_;
v___y_1464_ = v___y_1490_;
v___y_1465_ = v___y_1491_;
goto v___jp_1459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___boxed(lean_object* v_val_1518_, lean_object* v___x_1519_, lean_object* v_x_1520_, lean_object* v_mvarId_1521_, lean_object* v_declName_1522_, lean_object* v___x_1523_, lean_object* v_____r_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
uint8_t v___x_31896__boxed_1530_; lean_object* v_res_1531_; 
v___x_31896__boxed_1530_ = lean_unbox(v___x_1523_);
v_res_1531_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(v_val_1518_, v___x_1519_, v_x_1520_, v_mvarId_1521_, v_declName_1522_, v___x_31896__boxed_1530_, v_____r_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec_ref(v_x_1520_);
lean_dec_ref(v___x_1519_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5(lean_object* v_declName_1532_, lean_object* v_val_1533_, uint8_t v___x_1534_, uint8_t v___x_1535_, size_t v_sz_1536_, size_t v_i_1537_, lean_object* v_bs_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
uint8_t v___x_1544_; 
v___x_1544_ = lean_usize_dec_lt(v_i_1537_, v_sz_1536_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; 
lean_dec_ref(v_val_1533_);
lean_dec(v_declName_1532_);
v___x_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1545_, 0, v_bs_1538_);
return v___x_1545_;
}
else
{
lean_object* v_v_1546_; lean_object* v_toInductionSubgoal_1547_; lean_object* v_ctorName_1548_; lean_object* v_mvarId_1549_; lean_object* v_fields_1550_; lean_object* v___f_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v_bs_x27_1554_; uint8_t v___y_1556_; 
v_v_1546_ = lean_array_uget_borrowed(v_bs_1538_, v_i_1537_);
v_toInductionSubgoal_1547_ = lean_ctor_get(v_v_1546_, 0);
v_ctorName_1548_ = lean_ctor_get(v_v_1546_, 1);
lean_inc(v_ctorName_1548_);
v_mvarId_1549_ = lean_ctor_get(v_toInductionSubgoal_1547_, 0);
lean_inc(v_mvarId_1549_);
v_fields_1550_ = lean_ctor_get(v_toInductionSubgoal_1547_, 1);
lean_inc_ref(v_fields_1550_);
v___f_1551_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0));
v___x_1552_ = l_Lean_instInhabitedExpr;
v___x_1553_ = lean_unsigned_to_nat(0u);
v_bs_x27_1554_ = lean_array_uset(v_bs_1538_, v_i_1537_, v___x_1553_);
if (lean_obj_tag(v_ctorName_1548_) == 0)
{
v___y_1556_ = v___x_1535_;
goto v___jp_1555_;
}
else
{
lean_dec_ref_known(v_ctorName_1548_, 1);
v___y_1556_ = v___x_1534_;
goto v___jp_1555_;
}
v___jp_1555_:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___y_1559_; lean_object* v___x_1560_; 
v___x_1557_ = lean_box(v___y_1556_);
v___x_1558_ = lean_box(v___x_1534_);
lean_inc_ref(v_val_1533_);
lean_inc(v_declName_1532_);
lean_inc(v_mvarId_1549_);
v___y_1559_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed), 13, 8);
lean_closure_set(v___y_1559_, 0, v___x_1557_);
lean_closure_set(v___y_1559_, 1, v_mvarId_1549_);
lean_closure_set(v___y_1559_, 2, v___f_1551_);
lean_closure_set(v___y_1559_, 3, v_declName_1532_);
lean_closure_set(v___y_1559_, 4, v_val_1533_);
lean_closure_set(v___y_1559_, 5, v___x_1552_);
lean_closure_set(v___y_1559_, 6, v_fields_1550_);
lean_closure_set(v___y_1559_, 7, v___x_1558_);
v___x_1560_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1549_, v___y_1559_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; size_t v___x_1562_; size_t v___x_1563_; lean_object* v___x_1564_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1561_);
lean_dec_ref_known(v___x_1560_, 1);
v___x_1562_ = ((size_t)1ULL);
v___x_1563_ = lean_usize_add(v_i_1537_, v___x_1562_);
v___x_1564_ = lean_array_uset(v_bs_x27_1554_, v_i_1537_, v_a_1561_);
v_i_1537_ = v___x_1563_;
v_bs_1538_ = v___x_1564_;
goto _start;
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
lean_dec_ref(v_bs_x27_1554_);
lean_dec_ref(v_val_1533_);
lean_dec(v_declName_1532_);
v_a_1566_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1560_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1560_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5___boxed(lean_object* v_declName_1574_, lean_object* v_val_1575_, lean_object* v___x_1576_, lean_object* v___x_1577_, lean_object* v_sz_1578_, lean_object* v_i_1579_, lean_object* v_bs_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
uint8_t v___x_32045__boxed_1586_; uint8_t v___x_32046__boxed_1587_; size_t v_sz_boxed_1588_; size_t v_i_boxed_1589_; lean_object* v_res_1590_; 
v___x_32045__boxed_1586_ = lean_unbox(v___x_1576_);
v___x_32046__boxed_1587_ = lean_unbox(v___x_1577_);
v_sz_boxed_1588_ = lean_unbox_usize(v_sz_1578_);
lean_dec(v_sz_1578_);
v_i_boxed_1589_ = lean_unbox_usize(v_i_1579_);
lean_dec(v_i_1579_);
v_res_1590_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5(v_declName_1574_, v_val_1575_, v___x_32045__boxed_1586_, v___x_32046__boxed_1587_, v_sz_boxed_1588_, v_i_boxed_1589_, v_bs_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(lean_object* v_val_1591_, lean_object* v___x_1592_, lean_object* v_x_1593_, lean_object* v_mvarId_1594_, uint8_t v___x_1595_, lean_object* v_declName_1596_, uint8_t v_hasTrace_1597_, lean_object* v_____r_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v_majorPos_1628_; lean_object* v_arity_1629_; lean_object* v_insterestingCtors_1630_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___x_1650_; uint8_t v___x_1651_; 
v_majorPos_1628_ = lean_ctor_get(v_val_1591_, 1);
v_arity_1629_ = lean_ctor_get(v_val_1591_, 2);
v_insterestingCtors_1630_ = lean_ctor_get(v_val_1591_, 3);
v___x_1650_ = lean_array_get_size(v_x_1593_);
v___x_1651_ = lean_nat_dec_lt(v___x_1650_, v_arity_1629_);
if (v___x_1651_ == 0)
{
v___y_1632_ = v___y_1599_;
v___y_1633_ = v___y_1600_;
v___y_1634_ = v___y_1601_;
v___y_1635_ = v___y_1602_;
goto v___jp_1631_;
}
else
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
lean_dec(v_declName_1596_);
lean_dec(v_mvarId_1594_);
lean_dec_ref(v_val_1591_);
v___x_1652_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1);
v___x_1653_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1652_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1656_ = v___x_1653_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1653_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1657_ == 0)
{
v___x_1659_ = v___x_1656_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_a_1654_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
v___jp_1604_:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1611_ = lean_array_get_borrowed(v___x_1592_, v_x_1593_, v___y_1605_);
lean_dec(v___y_1605_);
v___x_1612_ = l_Lean_Expr_fvarId_x21(v___x_1611_);
v___x_1613_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__0));
v___x_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1614_, 0, v___y_1606_);
v___x_1615_ = l_Lean_MVarId_cases(v_mvarId_1594_, v___x_1612_, v___x_1613_, v___x_1595_, v___x_1614_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; size_t v_sz_1617_; size_t v___x_1618_; lean_object* v___x_1619_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_a_1616_);
lean_dec_ref_known(v___x_1615_, 1);
v_sz_1617_ = lean_array_size(v_a_1616_);
v___x_1618_ = ((size_t)0ULL);
v___x_1619_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5(v_declName_1596_, v_val_1591_, v___x_1595_, v_hasTrace_1597_, v_sz_1617_, v___x_1618_, v_a_1616_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
return v___x_1619_;
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
lean_dec(v_declName_1596_);
lean_dec_ref(v_val_1591_);
v_a_1620_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1615_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1615_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
v___jp_1631_:
{
lean_object* v___x_1636_; uint8_t v___x_1637_; 
v___x_1636_ = lean_array_get_borrowed(v___x_1592_, v_x_1593_, v_majorPos_1628_);
v___x_1637_ = l_Lean_Expr_isFVar(v___x_1636_);
if (v___x_1637_ == 0)
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
lean_dec(v_declName_1596_);
lean_dec(v_mvarId_1594_);
lean_dec_ref(v_val_1591_);
v___x_1638_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__2);
lean_inc(v___x_1636_);
v___x_1639_ = l_Lean_indentExpr(v___x_1636_);
v___x_1640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1638_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
v___x_1641_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1640_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1644_ = v___x_1641_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1641_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1642_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
else
{
lean_inc_ref(v_insterestingCtors_1630_);
lean_inc(v_majorPos_1628_);
v___y_1605_ = v_majorPos_1628_;
v___y_1606_ = v_insterestingCtors_1630_;
v___y_1607_ = v___y_1632_;
v___y_1608_ = v___y_1633_;
v___y_1609_ = v___y_1634_;
v___y_1610_ = v___y_1635_;
goto v___jp_1604_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0___boxed(lean_object* v_val_1662_, lean_object* v___x_1663_, lean_object* v_x_1664_, lean_object* v_mvarId_1665_, lean_object* v___x_1666_, lean_object* v_declName_1667_, lean_object* v_hasTrace_1668_, lean_object* v_____r_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
uint8_t v___x_32130__boxed_1675_; uint8_t v_hasTrace_boxed_1676_; lean_object* v_res_1677_; 
v___x_32130__boxed_1675_ = lean_unbox(v___x_1666_);
v_hasTrace_boxed_1676_ = lean_unbox(v_hasTrace_1668_);
v_res_1677_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v_val_1662_, v___x_1663_, v_x_1664_, v_mvarId_1665_, v___x_32130__boxed_1675_, v_declName_1667_, v_hasTrace_boxed_1676_, v_____r_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec_ref(v_x_1664_);
lean_dec_ref(v___x_1663_);
return v_res_1677_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__0));
v___x_1680_ = l_Lean_stringToMessageData(v___x_1679_);
return v___x_1680_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__2));
v___x_1683_ = l_Lean_stringToMessageData(v___x_1682_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6(lean_object* v_mvarId_1684_, lean_object* v_x_1685_, lean_object* v_x_1686_, lean_object* v_x_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
if (lean_obj_tag(v_x_1685_) == 5)
{
lean_object* v_fn_1693_; lean_object* v_arg_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v_fn_1693_ = lean_ctor_get(v_x_1685_, 0);
lean_inc_ref(v_fn_1693_);
v_arg_1694_ = lean_ctor_get(v_x_1685_, 1);
lean_inc_ref(v_arg_1694_);
lean_dec_ref_known(v_x_1685_, 2);
v___x_1695_ = lean_array_set(v_x_1686_, v_x_1687_, v_arg_1694_);
v___x_1696_ = lean_unsigned_to_nat(1u);
v___x_1697_ = lean_nat_sub(v_x_1687_, v___x_1696_);
lean_dec(v_x_1687_);
v_x_1685_ = v_fn_1693_;
v_x_1686_ = v___x_1695_;
v_x_1687_ = v___x_1697_;
goto _start;
}
else
{
lean_dec(v_x_1687_);
if (lean_obj_tag(v_x_1685_) == 4)
{
lean_object* v_declName_1699_; lean_object* v___f_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v_declName_1699_ = lean_ctor_get(v_x_1685_, 0);
lean_inc_n(v_declName_1699_, 2);
lean_dec_ref_known(v_x_1685_, 2);
v___f_1700_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1));
v___x_1701_ = l_Lean_instInhabitedExpr;
v___x_1702_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_declName_1699_, v___y_1691_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v_a_1703_; 
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1703_);
lean_dec_ref_known(v___x_1702_, 1);
if (lean_obj_tag(v_a_1703_) == 1)
{
lean_object* v_toCold_1704_; lean_object* v_options_1705_; lean_object* v_val_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_2014_; 
v_toCold_1704_ = lean_ctor_get(v___y_1690_, 0);
v_options_1705_ = lean_ctor_get(v_toCold_1704_, 2);
v_val_1706_ = lean_ctor_get(v_a_1703_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v_a_1703_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_1708_ = v_a_1703_;
v_isShared_1709_ = v_isSharedCheck_2014_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_val_1706_);
lean_dec(v_a_1703_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_2014_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v_inheritedTraceOptions_1710_; uint8_t v_hasTrace_1711_; lean_object* v___x_1712_; lean_object* v___y_1714_; lean_object* v___y_1715_; uint8_t v___y_1716_; lean_object* v___y_1749_; lean_object* v_a_1750_; lean_object* v___y_1754_; lean_object* v___y_1757_; lean_object* v___y_1758_; uint8_t v___y_1759_; lean_object* v___y_1792_; lean_object* v_a_1793_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; 
v_inheritedTraceOptions_1710_ = lean_ctor_get(v_toCold_1704_, 11);
v_hasTrace_1711_ = lean_ctor_get_uint8(v_options_1705_, sizeof(void*)*1);
v___x_1712_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5));
if (v_hasTrace_1711_ == 0)
{
lean_object* v_majorPos_1823_; lean_object* v_arity_1824_; lean_object* v_insterestingCtors_1825_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___x_1845_; uint8_t v___x_1846_; 
v_majorPos_1823_ = lean_ctor_get(v_val_1706_, 1);
v_arity_1824_ = lean_ctor_get(v_val_1706_, 2);
v_insterestingCtors_1825_ = lean_ctor_get(v_val_1706_, 3);
v___x_1845_ = lean_array_get_size(v_x_1686_);
v___x_1846_ = lean_nat_dec_lt(v___x_1845_, v_arity_1824_);
if (v___x_1846_ == 0)
{
v___y_1827_ = v___y_1688_;
v___y_1828_ = v___y_1689_;
v___y_1829_ = v___y_1690_;
v___y_1830_ = v___y_1691_;
goto v___jp_1826_;
}
else
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
lean_del_object(v___x_1708_);
lean_dec(v_val_1706_);
lean_dec(v_declName_1699_);
lean_dec_ref(v_x_1686_);
lean_dec(v_mvarId_1684_);
v___x_1847_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1);
v___x_1848_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1847_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1848_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1848_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
lean_inc(v_a_1849_);
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
v___y_1792_ = v___x_1854_;
v_a_1793_ = v_a_1849_;
goto v___jp_1791_;
}
}
}
v___jp_1826_:
{
lean_object* v___x_1831_; uint8_t v___x_1832_; 
v___x_1831_ = lean_array_get_borrowed(v___x_1701_, v_x_1686_, v_majorPos_1823_);
v___x_1832_ = l_Lean_Expr_isFVar(v___x_1831_);
if (v___x_1832_ == 0)
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1844_; 
lean_inc(v___x_1831_);
lean_del_object(v___x_1708_);
lean_dec(v_val_1706_);
lean_dec(v_declName_1699_);
lean_dec_ref(v_x_1686_);
lean_dec(v_mvarId_1684_);
v___x_1833_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__2);
v___x_1834_ = l_Lean_indentExpr(v___x_1831_);
v___x_1835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1833_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
v___x_1836_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1835_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1839_ = v___x_1836_;
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1836_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1842_; 
lean_inc(v_a_1837_);
if (v_isShared_1840_ == 0)
{
v___x_1842_ = v___x_1839_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1837_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
v___y_1792_ = v___x_1842_;
v_a_1793_ = v_a_1837_;
goto v___jp_1791_;
}
}
}
else
{
lean_inc_ref(v_insterestingCtors_1825_);
lean_inc(v_majorPos_1823_);
v___y_1797_ = v_majorPos_1823_;
v___y_1798_ = v_insterestingCtors_1825_;
v___y_1799_ = v___y_1827_;
v___y_1800_ = v___y_1828_;
v___y_1801_ = v___y_1829_;
v___y_1802_ = v___y_1830_;
goto v___jp_1796_;
}
}
}
else
{
lean_object* v___x_1857_; lean_object* v___x_1858_; uint8_t v___x_1859_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v_a_1863_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v_a_1878_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; uint8_t v___y_1884_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v_a_1897_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v_a_1916_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v_a_1928_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; uint8_t v___y_1934_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v_a_1947_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; 
lean_del_object(v___x_1708_);
v___x_1857_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__6));
v___x_1858_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9);
v___x_1859_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1710_, v_options_1705_, v___x_1858_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1996_; uint8_t v___x_1997_; 
v___x_1996_ = l_Lean_trace_profiler;
v___x_1997_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_options_1705_, v___x_1996_);
if (v___x_1997_ == 0)
{
if (v___x_1859_ == 0)
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1998_ = lean_box(0);
v___x_1999_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v_val_1706_, v___x_1701_, v_x_1686_, v_mvarId_1684_, v___x_1997_, v_declName_1699_, v_hasTrace_1711_, v___x_1998_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
lean_dec_ref(v_x_1686_);
v___y_1754_ = v___x_1999_;
goto v___jp_1753_;
}
else
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2000_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3);
lean_inc(v_mvarId_1684_);
v___x_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2001_, 0, v_mvarId_1684_);
v___x_2002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2000_);
lean_ctor_set(v___x_2002_, 1, v___x_2001_);
v___x_2003_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1712_, v___x_2002_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; lean_object* v___x_2005_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_a_2004_);
lean_dec_ref_known(v___x_2003_, 1);
v___x_2005_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v_val_1706_, v___x_1701_, v_x_1686_, v_mvarId_1684_, v___x_1997_, v_declName_1699_, v_hasTrace_1711_, v_a_2004_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
lean_dec_ref(v_x_1686_);
v___y_1754_ = v___x_2005_;
goto v___jp_1753_;
}
else
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2013_; 
lean_dec(v_val_1706_);
lean_dec(v_declName_1699_);
lean_dec_ref(v_x_1686_);
lean_dec(v_mvarId_1684_);
v_a_2006_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2008_ = v___x_2003_;
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_2003_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2011_; 
lean_inc(v_a_2006_);
if (v_isShared_2009_ == 0)
{
v___x_2011_ = v___x_2008_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_a_2006_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
v___y_1749_ = v___x_2011_;
v_a_1750_ = v_a_2006_;
goto v___jp_1748_;
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
v___jp_1860_:
{
lean_object* v___x_1864_; double v___x_1865_; double v___x_1866_; double v___x_1867_; double v___x_1868_; double v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1864_ = lean_io_mono_nanos_now();
v___x_1865_ = lean_float_of_nat(v___y_1861_);
v___x_1866_ = lean_float_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10);
v___x_1867_ = lean_float_div(v___x_1865_, v___x_1866_);
v___x_1868_ = lean_float_of_nat(v___x_1864_);
v___x_1869_ = lean_float_div(v___x_1868_, v___x_1866_);
v___x_1870_ = lean_box_float(v___x_1867_);
v___x_1871_ = lean_box_float(v___x_1869_);
v___x_1872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1870_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
v___x_1873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1873_, 0, v_a_1863_);
lean_ctor_set(v___x_1873_, 1, v___x_1872_);
v___x_1874_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_1712_, v_hasTrace_1711_, v___x_1857_, v_options_1705_, v___x_1859_, v___y_1862_, v___f_1700_, v___x_1873_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
return v___x_1874_;
}
v___jp_1875_:
{
lean_object* v___x_1879_; 
v___x_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1879_, 0, v_a_1878_);
v___y_1861_ = v___y_1876_;
v___y_1862_ = v___y_1877_;
v_a_1863_ = v___x_1879_;
goto v___jp_1860_;
}
v___jp_1880_:
{
if (v___y_1884_ == 0)
{
lean_object* v___x_1885_; lean_object* v_a_1886_; uint8_t v___x_1887_; 
v___x_1885_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(v___x_1712_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1886_);
lean_dec_ref(v___x_1885_);
v___x_1887_ = lean_unbox(v_a_1886_);
lean_dec(v_a_1886_);
if (v___x_1887_ == 0)
{
v___y_1876_ = v___y_1881_;
v___y_1877_ = v___y_1883_;
v_a_1878_ = v___y_1882_;
goto v___jp_1875_;
}
else
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1888_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1);
lean_inc_ref(v___y_1882_);
v___x_1889_ = l_Lean_Exception_toMessageData(v___y_1882_);
v___x_1890_ = l_Lean_indentD(v___x_1889_);
v___x_1891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1888_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
v___x_1892_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1712_, v___x_1891_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_dec_ref_known(v___x_1892_, 1);
v___y_1876_ = v___y_1881_;
v___y_1877_ = v___y_1883_;
v_a_1878_ = v___y_1882_;
goto v___jp_1875_;
}
else
{
lean_object* v_a_1893_; 
lean_dec_ref(v___y_1882_);
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_a_1893_);
lean_dec_ref_known(v___x_1892_, 1);
v___y_1876_ = v___y_1881_;
v___y_1877_ = v___y_1883_;
v_a_1878_ = v_a_1893_;
goto v___jp_1875_;
}
}
}
else
{
v___y_1876_ = v___y_1881_;
v___y_1877_ = v___y_1883_;
v_a_1878_ = v___y_1882_;
goto v___jp_1875_;
}
}
v___jp_1894_:
{
uint8_t v___x_1898_; 
v___x_1898_ = l_Lean_Exception_isInterrupt(v_a_1897_);
if (v___x_1898_ == 0)
{
uint8_t v___x_1899_; 
lean_inc_ref(v_a_1897_);
v___x_1899_ = l_Lean_Exception_isRuntime(v_a_1897_);
v___y_1881_ = v___y_1895_;
v___y_1882_ = v_a_1897_;
v___y_1883_ = v___y_1896_;
v___y_1884_ = v___x_1899_;
goto v___jp_1880_;
}
else
{
v___y_1881_ = v___y_1895_;
v___y_1882_ = v_a_1897_;
v___y_1883_ = v___y_1896_;
v___y_1884_ = v___x_1898_;
goto v___jp_1880_;
}
}
v___jp_1900_:
{
if (lean_obj_tag(v___y_1903_) == 0)
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
v_a_1904_ = lean_ctor_get(v___y_1903_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___y_1903_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___y_1903_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___y_1903_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
lean_ctor_set_tag(v___x_1906_, 1);
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
v___y_1861_ = v___y_1901_;
v___y_1862_ = v___y_1902_;
v_a_1863_ = v___x_1909_;
goto v___jp_1860_;
}
}
}
else
{
lean_object* v_a_1912_; 
v_a_1912_ = lean_ctor_get(v___y_1903_, 0);
lean_inc(v_a_1912_);
lean_dec_ref_known(v___y_1903_, 1);
v___y_1895_ = v___y_1901_;
v___y_1896_ = v___y_1902_;
v_a_1897_ = v_a_1912_;
goto v___jp_1894_;
}
}
v___jp_1913_:
{
lean_object* v___x_1917_; double v___x_1918_; double v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1917_ = lean_io_get_num_heartbeats();
v___x_1918_ = lean_float_of_nat(v___y_1914_);
v___x_1919_ = lean_float_of_nat(v___x_1917_);
v___x_1920_ = lean_box_float(v___x_1918_);
v___x_1921_ = lean_box_float(v___x_1919_);
v___x_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1920_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1923_, 0, v_a_1916_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
v___x_1924_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_1712_, v_hasTrace_1711_, v___x_1857_, v_options_1705_, v___x_1859_, v___y_1915_, v___f_1700_, v___x_1923_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
return v___x_1924_;
}
v___jp_1925_:
{
lean_object* v___x_1929_; 
v___x_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1929_, 0, v_a_1928_);
v___y_1914_ = v___y_1926_;
v___y_1915_ = v___y_1927_;
v_a_1916_ = v___x_1929_;
goto v___jp_1913_;
}
v___jp_1930_:
{
if (v___y_1934_ == 0)
{
lean_object* v___x_1935_; lean_object* v_a_1936_; uint8_t v___x_1937_; 
v___x_1935_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(v___x_1712_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
lean_dec_ref(v___x_1935_);
v___x_1937_ = lean_unbox(v_a_1936_);
lean_dec(v_a_1936_);
if (v___x_1937_ == 0)
{
v___y_1926_ = v___y_1932_;
v___y_1927_ = v___y_1933_;
v_a_1928_ = v___y_1931_;
goto v___jp_1925_;
}
else
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1938_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1);
lean_inc_ref(v___y_1931_);
v___x_1939_ = l_Lean_Exception_toMessageData(v___y_1931_);
v___x_1940_ = l_Lean_indentD(v___x_1939_);
v___x_1941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1938_);
lean_ctor_set(v___x_1941_, 1, v___x_1940_);
v___x_1942_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1712_, v___x_1941_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_dec_ref_known(v___x_1942_, 1);
v___y_1926_ = v___y_1932_;
v___y_1927_ = v___y_1933_;
v_a_1928_ = v___y_1931_;
goto v___jp_1925_;
}
else
{
lean_object* v_a_1943_; 
lean_dec_ref(v___y_1931_);
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc(v_a_1943_);
lean_dec_ref_known(v___x_1942_, 1);
v___y_1926_ = v___y_1932_;
v___y_1927_ = v___y_1933_;
v_a_1928_ = v_a_1943_;
goto v___jp_1925_;
}
}
}
else
{
v___y_1926_ = v___y_1932_;
v___y_1927_ = v___y_1933_;
v_a_1928_ = v___y_1931_;
goto v___jp_1925_;
}
}
v___jp_1944_:
{
uint8_t v___x_1948_; 
v___x_1948_ = l_Lean_Exception_isInterrupt(v_a_1947_);
if (v___x_1948_ == 0)
{
uint8_t v___x_1949_; 
lean_inc_ref(v_a_1947_);
v___x_1949_ = l_Lean_Exception_isRuntime(v_a_1947_);
v___y_1931_ = v_a_1947_;
v___y_1932_ = v___y_1945_;
v___y_1933_ = v___y_1946_;
v___y_1934_ = v___x_1949_;
goto v___jp_1930_;
}
else
{
v___y_1931_ = v_a_1947_;
v___y_1932_ = v___y_1945_;
v___y_1933_ = v___y_1946_;
v___y_1934_ = v___x_1948_;
goto v___jp_1930_;
}
}
v___jp_1950_:
{
if (lean_obj_tag(v___y_1953_) == 0)
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
v_a_1954_ = lean_ctor_get(v___y_1953_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___y_1953_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___y_1953_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___y_1953_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
lean_ctor_set_tag(v___x_1956_, 1);
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
v___y_1914_ = v___y_1951_;
v___y_1915_ = v___y_1952_;
v_a_1916_ = v___x_1959_;
goto v___jp_1913_;
}
}
}
else
{
lean_object* v_a_1962_; 
v_a_1962_ = lean_ctor_get(v___y_1953_, 0);
lean_inc(v_a_1962_);
lean_dec_ref_known(v___y_1953_, 1);
v___y_1945_ = v___y_1951_;
v___y_1946_ = v___y_1952_;
v_a_1947_ = v_a_1962_;
goto v___jp_1944_;
}
}
v___jp_1963_:
{
lean_object* v___x_1964_; lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1995_; 
v___x_1964_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___y_1691_);
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1967_ = v___x_1964_;
v_isShared_1968_ = v_isSharedCheck_1995_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1964_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1995_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1969_; uint8_t v___x_1970_; 
v___x_1969_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1970_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_options_1705_, v___x_1969_);
if (v___x_1970_ == 0)
{
lean_object* v___x_1971_; 
v___x_1971_ = lean_io_mono_nanos_now();
if (v___x_1859_ == 0)
{
lean_object* v___x_1972_; lean_object* v___x_1973_; 
lean_del_object(v___x_1967_);
v___x_1972_ = lean_box(0);
v___x_1973_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v_val_1706_, v___x_1701_, v_x_1686_, v_mvarId_1684_, v___x_1970_, v_declName_1699_, v_hasTrace_1711_, v___x_1972_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
lean_dec_ref(v_x_1686_);
v___y_1901_ = v___x_1971_;
v___y_1902_ = v_a_1965_;
v___y_1903_ = v___x_1973_;
goto v___jp_1900_;
}
else
{
lean_object* v___x_1974_; lean_object* v___x_1976_; 
v___x_1974_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3);
lean_inc(v_mvarId_1684_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set_tag(v___x_1967_, 1);
lean_ctor_set(v___x_1967_, 0, v_mvarId_1684_);
v___x_1976_ = v___x_1967_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_mvarId_1684_);
v___x_1976_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1974_);
lean_ctor_set(v___x_1977_, 1, v___x_1976_);
v___x_1978_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1712_, v___x_1977_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v___x_1980_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_1979_);
lean_dec_ref_known(v___x_1978_, 1);
v___x_1980_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v_val_1706_, v___x_1701_, v_x_1686_, v_mvarId_1684_, v___x_1970_, v_declName_1699_, v_hasTrace_1711_, v_a_1979_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
lean_dec_ref(v_x_1686_);
v___y_1901_ = v___x_1971_;
v___y_1902_ = v_a_1965_;
v___y_1903_ = v___x_1980_;
goto v___jp_1900_;
}
else
{
lean_object* v_a_1981_; 
lean_dec(v_val_1706_);
lean_dec(v_declName_1699_);
lean_dec_ref(v_x_1686_);
lean_dec(v_mvarId_1684_);
v_a_1981_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_1981_);
lean_dec_ref_known(v___x_1978_, 1);
v___y_1895_ = v___x_1971_;
v___y_1896_ = v_a_1965_;
v_a_1897_ = v_a_1981_;
goto v___jp_1894_;
}
}
}
}
else
{
lean_object* v___x_1983_; 
v___x_1983_ = lean_io_get_num_heartbeats();
if (v___x_1859_ == 0)
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
lean_del_object(v___x_1967_);
v___x_1984_ = lean_box(0);
v___x_1985_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(v_val_1706_, v___x_1701_, v_x_1686_, v_mvarId_1684_, v_declName_1699_, v___x_1970_, v___x_1984_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
lean_dec_ref(v_x_1686_);
v___y_1951_ = v___x_1983_;
v___y_1952_ = v_a_1965_;
v___y_1953_ = v___x_1985_;
goto v___jp_1950_;
}
else
{
lean_object* v___x_1986_; lean_object* v___x_1988_; 
v___x_1986_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3);
lean_inc(v_mvarId_1684_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set_tag(v___x_1967_, 1);
lean_ctor_set(v___x_1967_, 0, v_mvarId_1684_);
v___x_1988_ = v___x_1967_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_mvarId_1684_);
v___x_1988_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1986_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
v___x_1990_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1712_, v___x_1989_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v___x_1992_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_1991_);
lean_dec_ref_known(v___x_1990_, 1);
v___x_1992_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(v_val_1706_, v___x_1701_, v_x_1686_, v_mvarId_1684_, v_declName_1699_, v___x_1970_, v_a_1991_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
lean_dec_ref(v_x_1686_);
v___y_1951_ = v___x_1983_;
v___y_1952_ = v_a_1965_;
v___y_1953_ = v___x_1992_;
goto v___jp_1950_;
}
else
{
lean_object* v_a_1993_; 
lean_dec(v_val_1706_);
lean_dec(v_declName_1699_);
lean_dec_ref(v_x_1686_);
lean_dec(v_mvarId_1684_);
v_a_1993_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_1993_);
lean_dec_ref_known(v___x_1990_, 1);
v___y_1945_ = v___x_1983_;
v___y_1946_ = v_a_1965_;
v_a_1947_ = v_a_1993_;
goto v___jp_1944_;
}
}
}
}
}
}
}
v___jp_1713_:
{
if (v___y_1716_ == 0)
{
lean_object* v___x_1717_; lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1747_; 
lean_dec_ref(v___y_1715_);
v___x_1717_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(v___x_1712_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1720_ = v___x_1717_;
v_isShared_1721_ = v_isSharedCheck_1747_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1717_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1747_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
uint8_t v___x_1722_; 
v___x_1722_ = lean_unbox(v_a_1718_);
lean_dec(v_a_1718_);
if (v___x_1722_ == 0)
{
lean_object* v___x_1724_; 
if (v_isShared_1721_ == 0)
{
lean_ctor_set_tag(v___x_1720_, 1);
lean_ctor_set(v___x_1720_, 0, v___y_1714_);
v___x_1724_ = v___x_1720_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___y_1714_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
else
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
lean_del_object(v___x_1720_);
v___x_1726_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1);
lean_inc_ref(v___y_1714_);
v___x_1727_ = l_Lean_Exception_toMessageData(v___y_1714_);
v___x_1728_ = l_Lean_indentD(v___x_1727_);
v___x_1729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1726_);
lean_ctor_set(v___x_1729_, 1, v___x_1728_);
v___x_1730_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1712_, v___x_1729_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1737_; 
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1737_ == 0)
{
lean_object* v_unused_1738_; 
v_unused_1738_ = lean_ctor_get(v___x_1730_, 0);
lean_dec(v_unused_1738_);
v___x_1732_ = v___x_1730_;
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
else
{
lean_dec(v___x_1730_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1733_ == 0)
{
lean_ctor_set_tag(v___x_1732_, 1);
lean_ctor_set(v___x_1732_, 0, v___y_1714_);
v___x_1735_ = v___x_1732_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___y_1714_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
lean_dec_ref(v___y_1714_);
v_a_1739_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1730_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1730_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_1714_);
return v___y_1715_;
}
}
v___jp_1748_:
{
uint8_t v___x_1751_; 
v___x_1751_ = l_Lean_Exception_isInterrupt(v_a_1750_);
if (v___x_1751_ == 0)
{
uint8_t v___x_1752_; 
lean_inc_ref(v_a_1750_);
v___x_1752_ = l_Lean_Exception_isRuntime(v_a_1750_);
v___y_1714_ = v_a_1750_;
v___y_1715_ = v___y_1749_;
v___y_1716_ = v___x_1752_;
goto v___jp_1713_;
}
else
{
v___y_1714_ = v_a_1750_;
v___y_1715_ = v___y_1749_;
v___y_1716_ = v___x_1751_;
goto v___jp_1713_;
}
}
v___jp_1753_:
{
if (lean_obj_tag(v___y_1754_) == 0)
{
return v___y_1754_;
}
else
{
lean_object* v_a_1755_; 
v_a_1755_ = lean_ctor_get(v___y_1754_, 0);
lean_inc(v_a_1755_);
v___y_1749_ = v___y_1754_;
v_a_1750_ = v_a_1755_;
goto v___jp_1748_;
}
}
v___jp_1756_:
{
if (v___y_1759_ == 0)
{
lean_object* v___x_1760_; lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1790_; 
lean_dec_ref(v___y_1757_);
v___x_1760_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(v___x_1712_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1763_ = v___x_1760_;
v_isShared_1764_ = v_isSharedCheck_1790_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1760_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1790_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
uint8_t v___x_1765_; 
v___x_1765_ = lean_unbox(v_a_1761_);
lean_dec(v_a_1761_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1767_; 
if (v_isShared_1764_ == 0)
{
lean_ctor_set_tag(v___x_1763_, 1);
lean_ctor_set(v___x_1763_, 0, v___y_1758_);
v___x_1767_ = v___x_1763_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___y_1758_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
else
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
lean_del_object(v___x_1763_);
v___x_1769_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1);
lean_inc_ref(v___y_1758_);
v___x_1770_ = l_Lean_Exception_toMessageData(v___y_1758_);
v___x_1771_ = l_Lean_indentD(v___x_1770_);
v___x_1772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1769_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
v___x_1773_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1712_, v___x_1772_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1780_ == 0)
{
lean_object* v_unused_1781_; 
v_unused_1781_ = lean_ctor_get(v___x_1773_, 0);
lean_dec(v_unused_1781_);
v___x_1775_ = v___x_1773_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_dec(v___x_1773_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
lean_ctor_set_tag(v___x_1775_, 1);
lean_ctor_set(v___x_1775_, 0, v___y_1758_);
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___y_1758_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
else
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
lean_dec_ref(v___y_1758_);
v_a_1782_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v___x_1773_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1773_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1782_);
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
else
{
lean_dec_ref(v___y_1758_);
return v___y_1757_;
}
}
v___jp_1791_:
{
uint8_t v___x_1794_; 
v___x_1794_ = l_Lean_Exception_isInterrupt(v_a_1793_);
if (v___x_1794_ == 0)
{
uint8_t v___x_1795_; 
lean_inc_ref(v_a_1793_);
v___x_1795_ = l_Lean_Exception_isRuntime(v_a_1793_);
v___y_1757_ = v___y_1792_;
v___y_1758_ = v_a_1793_;
v___y_1759_ = v___x_1795_;
goto v___jp_1756_;
}
else
{
v___y_1757_ = v___y_1792_;
v___y_1758_ = v_a_1793_;
v___y_1759_ = v___x_1794_;
goto v___jp_1756_;
}
}
v___jp_1796_:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1807_; 
v___x_1803_ = lean_array_get(v___x_1701_, v_x_1686_, v___y_1797_);
lean_dec(v___y_1797_);
lean_dec_ref(v_x_1686_);
v___x_1804_ = l_Lean_Expr_fvarId_x21(v___x_1803_);
lean_dec(v___x_1803_);
v___x_1805_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__0));
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 0, v___y_1798_);
v___x_1807_ = v___x_1708_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___y_1798_);
v___x_1807_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
lean_object* v___x_1808_; 
v___x_1808_ = l_Lean_MVarId_cases(v_mvarId_1684_, v___x_1804_, v___x_1805_, v_hasTrace_1711_, v___x_1807_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; size_t v_sz_1810_; size_t v___x_1811_; lean_object* v___x_1812_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_a_1809_);
lean_dec_ref_known(v___x_1808_, 1);
v_sz_1810_ = lean_array_size(v_a_1809_);
v___x_1811_ = ((size_t)0ULL);
v___x_1812_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(v_declName_1699_, v_val_1706_, v_hasTrace_1711_, v_sz_1810_, v___x_1811_, v_a_1809_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
if (lean_obj_tag(v___x_1812_) == 0)
{
return v___x_1812_;
}
else
{
lean_object* v_a_1813_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_a_1813_);
v___y_1792_ = v___x_1812_;
v_a_1793_ = v_a_1813_;
goto v___jp_1791_;
}
}
else
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1821_; 
lean_dec(v_val_1706_);
lean_dec(v_declName_1699_);
v_a_1814_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1816_ = v___x_1808_;
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1808_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
lean_inc(v_a_1814_);
if (v_isShared_1817_ == 0)
{
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_a_1814_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
v___y_1792_ = v___x_1819_;
v_a_1793_ = v_a_1814_;
goto v___jp_1791_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
lean_dec(v_a_1703_);
lean_dec(v_declName_1699_);
lean_dec_ref(v_x_1686_);
lean_dec(v_mvarId_1684_);
v___x_2015_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12);
v___x_2016_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_2015_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
return v___x_2016_;
}
}
else
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
lean_dec(v_declName_1699_);
lean_dec_ref(v_x_1686_);
lean_dec(v_mvarId_1684_);
v_a_2017_ = lean_ctor_get(v___x_1702_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_1702_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_1702_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2017_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
else
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
lean_dec_ref(v_x_1686_);
lean_dec_ref(v_x_1685_);
lean_dec(v_mvarId_1684_);
v___x_2025_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14);
v___x_2026_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_2025_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
return v___x_2026_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___boxed(lean_object* v_mvarId_2027_, lean_object* v_x_2028_, lean_object* v_x_2029_, lean_object* v_x_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6(v_mvarId_2027_, v_x_2028_, v_x_2029_, v_x_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitSparseCasesOn(lean_object* v_mvarId_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_){
_start:
{
lean_object* v___x_2043_; 
lean_inc(v_mvarId_2037_);
v___x_2043_ = l_Lean_MVarId_getType(v_mvarId_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; lean_object* v___x_2045_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2044_);
lean_dec_ref_known(v___x_2043_, 1);
v___x_2045_ = l_Lean_Meta_matchEqHEqLHS_x3f(v_a_2044_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc(v_a_2046_);
lean_dec_ref_known(v___x_2045_, 1);
if (lean_obj_tag(v_a_2046_) == 1)
{
lean_object* v_val_2047_; lean_object* v_snd_2048_; lean_object* v_dummy_2049_; lean_object* v_nargs_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v_val_2047_ = lean_ctor_get(v_a_2046_, 0);
lean_inc(v_val_2047_);
lean_dec_ref_known(v_a_2046_, 1);
v_snd_2048_ = lean_ctor_get(v_val_2047_, 1);
lean_inc(v_snd_2048_);
lean_dec(v_val_2047_);
v_dummy_2049_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0);
v_nargs_2050_ = l_Lean_Expr_getAppNumArgs(v_snd_2048_);
lean_inc(v_nargs_2050_);
v___x_2051_ = lean_mk_array(v_nargs_2050_, v_dummy_2049_);
v___x_2052_ = lean_unsigned_to_nat(1u);
v___x_2053_ = lean_nat_sub(v_nargs_2050_, v___x_2052_);
lean_dec(v_nargs_2050_);
v___x_2054_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6(v_mvarId_2037_, v_snd_2048_, v___x_2051_, v___x_2053_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_);
return v___x_2054_;
}
else
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
lean_dec(v_a_2046_);
lean_dec(v_mvarId_2037_);
v___x_2055_ = lean_obj_once(&l_Lean_Meta_reduceSparseCasesOn___closed__1, &l_Lean_Meta_reduceSparseCasesOn___closed__1_once, _init_l_Lean_Meta_reduceSparseCasesOn___closed__1);
v___x_2056_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_2055_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_);
return v___x_2056_;
}
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_dec(v_mvarId_2037_);
v_a_2057_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2045_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2045_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
else
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
lean_dec(v_mvarId_2037_);
v_a_2065_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2067_ = v___x_2043_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2043_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitSparseCasesOn___boxed(lean_object* v_mvarId_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_){
_start:
{
lean_object* v_res_2079_; 
v_res_2079_ = l_Lean_Meta_splitSparseCasesOn(v_mvarId_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
lean_dec(v_a_2077_);
lean_dec_ref(v_a_2076_);
lean_dec(v_a_2075_);
lean_dec_ref(v_a_2074_);
return v_res_2079_;
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
