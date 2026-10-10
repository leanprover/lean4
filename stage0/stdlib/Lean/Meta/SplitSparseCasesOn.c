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
lean_object* l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq(lean_object* v_goal_6_, lean_object* v_eq_7_, uint8_t v_symm_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
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
LEAN_EXPORT void l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_6_ = stack[0].m_obj;
lean_object* v_eq_7_ = stack[1].m_obj;
uint8_t v_symm_8_ = stack[2].m_num;
lean_object* v_a_9_ = stack[3].m_obj;
lean_object* v_a_10_ = stack[4].m_obj;
lean_object* v_a_11_ = stack[5].m_obj;
lean_object* v_a_12_ = stack[6].m_obj;
lean_object* v_res_38_;
v_res_38_ = l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq(v_goal_6_, v_eq_7_, v_symm_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
stack->m_obj
 = v_res_38_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq___boxed(lean_object* v_goal_39_, lean_object* v_eq_40_, lean_object* v_symm_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_){
_start:
{
uint8_t v_symm_boxed_47_; lean_object* v_res_48_; 
v_symm_boxed_47_ = lean_unbox(v_symm_41_);
v_res_48_ = l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq(v_goal_39_, v_eq_40_, v_symm_boxed_47_, v_a_42_, v_a_43_, v_a_44_, v_a_45_);
lean_dec(v_a_45_);
lean_dec_ref(v_a_44_);
lean_dec(v_a_43_);
lean_dec_ref(v_a_42_);
return v_res_48_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_unsigned_to_nat(32u);
v___x_50_ = lean_mk_empty_array_with_capacity(v___x_49_);
v___x_51_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_51_, 0, v___x_50_);
return v___x_51_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_52_ = ((size_t)5ULL);
v___x_53_ = lean_unsigned_to_nat(0u);
v___x_54_ = lean_unsigned_to_nat(32u);
v___x_55_ = lean_mk_empty_array_with_capacity(v___x_54_);
v___x_56_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__0);
v___x_57_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v___x_55_);
lean_ctor_set(v___x_57_, 2, v___x_53_);
lean_ctor_set(v___x_57_, 3, v___x_53_);
lean_ctor_set_usize(v___x_57_, 4, v___x_52_);
return v___x_57_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(lean_object* v___y_58_){
_start:
{
lean_object* v___x_60_; lean_object* v_traceState_61_; lean_object* v_traces_62_; lean_object* v___x_63_; lean_object* v_traceState_64_; lean_object* v_env_65_; lean_object* v_nextMacroScope_66_; lean_object* v_ngen_67_; lean_object* v_auxDeclNGen_68_; lean_object* v_cache_69_; lean_object* v_recordedDeps_70_; lean_object* v_messages_71_; lean_object* v_infoState_72_; lean_object* v_snapshotTasks_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_92_; 
v___x_60_ = lean_st_ref_get(v___y_58_);
v_traceState_61_ = lean_ctor_get(v___x_60_, 4);
lean_inc_ref(v_traceState_61_);
lean_dec(v___x_60_);
v_traces_62_ = lean_ctor_get(v_traceState_61_, 0);
lean_inc_ref(v_traces_62_);
lean_dec_ref(v_traceState_61_);
v___x_63_ = lean_st_ref_take(v___y_58_);
v_traceState_64_ = lean_ctor_get(v___x_63_, 4);
v_env_65_ = lean_ctor_get(v___x_63_, 0);
v_nextMacroScope_66_ = lean_ctor_get(v___x_63_, 1);
v_ngen_67_ = lean_ctor_get(v___x_63_, 2);
v_auxDeclNGen_68_ = lean_ctor_get(v___x_63_, 3);
v_cache_69_ = lean_ctor_get(v___x_63_, 5);
v_recordedDeps_70_ = lean_ctor_get(v___x_63_, 6);
v_messages_71_ = lean_ctor_get(v___x_63_, 7);
v_infoState_72_ = lean_ctor_get(v___x_63_, 8);
v_snapshotTasks_73_ = lean_ctor_get(v___x_63_, 9);
v_isSharedCheck_92_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_92_ == 0)
{
v___x_75_ = v___x_63_;
v_isShared_76_ = v_isSharedCheck_92_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_snapshotTasks_73_);
lean_inc(v_infoState_72_);
lean_inc(v_messages_71_);
lean_inc(v_recordedDeps_70_);
lean_inc(v_cache_69_);
lean_inc(v_traceState_64_);
lean_inc(v_auxDeclNGen_68_);
lean_inc(v_ngen_67_);
lean_inc(v_nextMacroScope_66_);
lean_inc(v_env_65_);
lean_dec(v___x_63_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_92_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
uint64_t v_tid_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_90_; 
v_tid_77_ = lean_ctor_get_uint64(v_traceState_64_, sizeof(void*)*1);
v_isSharedCheck_90_ = !lean_is_exclusive(v_traceState_64_);
if (v_isSharedCheck_90_ == 0)
{
lean_object* v_unused_91_; 
v_unused_91_ = lean_ctor_get(v_traceState_64_, 0);
lean_dec(v_unused_91_);
v___x_79_ = v_traceState_64_;
v_isShared_80_ = v_isSharedCheck_90_;
goto v_resetjp_78_;
}
else
{
lean_dec(v_traceState_64_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_90_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_81_; lean_object* v___x_83_; 
v___x_81_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__1);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 0, v___x_81_);
v___x_83_ = v___x_79_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v___x_81_);
lean_ctor_set_uint64(v_reuseFailAlloc_89_, sizeof(void*)*1, v_tid_77_);
v___x_83_ = v_reuseFailAlloc_89_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
lean_object* v___x_85_; 
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 4, v___x_83_);
v___x_85_ = v___x_75_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_env_65_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v_nextMacroScope_66_);
lean_ctor_set(v_reuseFailAlloc_88_, 2, v_ngen_67_);
lean_ctor_set(v_reuseFailAlloc_88_, 3, v_auxDeclNGen_68_);
lean_ctor_set(v_reuseFailAlloc_88_, 4, v___x_83_);
lean_ctor_set(v_reuseFailAlloc_88_, 5, v_cache_69_);
lean_ctor_set(v_reuseFailAlloc_88_, 6, v_recordedDeps_70_);
lean_ctor_set(v_reuseFailAlloc_88_, 7, v_messages_71_);
lean_ctor_set(v_reuseFailAlloc_88_, 8, v_infoState_72_);
lean_ctor_set(v_reuseFailAlloc_88_, 9, v_snapshotTasks_73_);
v___x_85_ = v_reuseFailAlloc_88_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = lean_st_ref_put(v___y_58_, v___x_85_);
v___x_87_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_87_, 0, v_traces_62_);
return v___x_87_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_58_ = stack[0].m_obj;
lean_object* v_res_93_;
v_res_93_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___y_58_);
stack->m_obj
 = v_res_93_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___boxed(lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___y_94_);
lean_dec(v___y_94_);
return v_res_96_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4(lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___y_100_);
return v___x_102_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_97_ = stack[0].m_obj;
lean_object* v___y_98_ = stack[1].m_obj;
lean_object* v___y_99_ = stack[2].m_obj;
lean_object* v___y_100_ = stack[3].m_obj;
lean_object* v_res_103_;
v_res_103_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4(v___y_97_, v___y_98_, v___y_99_, v___y_100_);
stack->m_obj
 = v_res_103_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___boxed(lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4(v___y_104_, v___y_105_, v___y_106_, v___y_107_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_106_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
return v_res_109_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(lean_object* v_opts_110_, lean_object* v_opt_111_){
_start:
{
lean_object* v_name_112_; lean_object* v_defValue_113_; lean_object* v_map_114_; lean_object* v___x_115_; 
v_name_112_ = lean_ctor_get(v_opt_111_, 0);
v_defValue_113_ = lean_ctor_get(v_opt_111_, 1);
v_map_114_ = lean_ctor_get(v_opts_110_, 0);
v___x_115_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_114_, v_name_112_);
if (lean_obj_tag(v___x_115_) == 0)
{
uint8_t v___x_116_; 
v___x_116_ = lean_unbox(v_defValue_113_);
return v___x_116_;
}
else
{
lean_object* v_val_117_; 
v_val_117_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_val_117_);
lean_dec_ref_known(v___x_115_, 1);
if (lean_obj_tag(v_val_117_) == 1)
{
uint8_t v_v_118_; 
v_v_118_ = lean_ctor_get_uint8(v_val_117_, 0);
lean_dec_ref_known(v_val_117_, 0);
return v_v_118_;
}
else
{
uint8_t v___x_119_; 
lean_dec(v_val_117_);
v___x_119_ = lean_unbox(v_defValue_113_);
return v___x_119_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_110_ = stack[0].m_obj;
lean_object* v_opt_111_ = stack[1].m_obj;
uint8_t v_res_120_;
v_res_120_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_opts_110_, v_opt_111_);
stack->m_num = v_res_120_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5___boxed(lean_object* v_opts_121_, lean_object* v_opt_122_){
_start:
{
uint8_t v_res_123_; lean_object* v_r_124_; 
v_res_123_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_opts_121_, v_opt_122_);
lean_dec_ref(v_opt_122_);
lean_dec_ref(v_opts_121_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__1(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0));
v___x_127_ = l_Lean_stringToMessageData(v___x_126_);
return v___x_127_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0(lean_object* v_x_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__1);
v___x_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_128_ = stack[0].m_obj;
lean_object* v___y_129_ = stack[1].m_obj;
lean_object* v___y_130_ = stack[2].m_obj;
lean_object* v___y_131_ = stack[3].m_obj;
lean_object* v___y_132_ = stack[4].m_obj;
lean_object* v_res_136_;
v_res_136_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0(v_x_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_);
stack->m_obj
 = v_res_136_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___boxed(lean_object* v_x_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0(v_x_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec_ref(v_x_137_);
return v_res_143_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1_spec__2(lean_object* v_a_144_, lean_object* v_as_145_, size_t v_i_146_, size_t v_stop_147_){
_start:
{
uint8_t v___x_148_; 
v___x_148_ = lean_usize_dec_eq(v_i_146_, v_stop_147_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_149_ = lean_array_uget_borrowed(v_as_145_, v_i_146_);
v___x_150_ = lean_name_eq(v_a_144_, v___x_149_);
if (v___x_150_ == 0)
{
size_t v___x_151_; size_t v___x_152_; 
v___x_151_ = ((size_t)1ULL);
v___x_152_ = lean_usize_add(v_i_146_, v___x_151_);
v_i_146_ = v___x_152_;
goto _start;
}
else
{
return v___x_150_;
}
}
else
{
uint8_t v___x_154_; 
v___x_154_ = 0;
return v___x_154_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_144_ = stack[0].m_obj;
lean_object* v_as_145_ = stack[1].m_obj;
size_t v_i_146_ = stack[2].m_num;
size_t v_stop_147_ = stack[3].m_num;
uint8_t v_res_155_;
v_res_155_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1_spec__2(v_a_144_, v_as_145_, v_i_146_, v_stop_147_);
stack->m_num = v_res_155_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1_spec__2___boxed(lean_object* v_a_156_, lean_object* v_as_157_, lean_object* v_i_158_, lean_object* v_stop_159_){
_start:
{
size_t v_i_boxed_160_; size_t v_stop_boxed_161_; uint8_t v_res_162_; lean_object* v_r_163_; 
v_i_boxed_160_ = lean_unbox_usize(v_i_158_);
lean_dec(v_i_158_);
v_stop_boxed_161_ = lean_unbox_usize(v_stop_159_);
lean_dec(v_stop_159_);
v_res_162_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1_spec__2(v_a_156_, v_as_157_, v_i_boxed_160_, v_stop_boxed_161_);
lean_dec_ref(v_as_157_);
lean_dec(v_a_156_);
v_r_163_ = lean_box(v_res_162_);
return v_r_163_;
}
}
uint8_t l_Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1(lean_object* v_as_164_, lean_object* v_a_165_){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_166_ = lean_unsigned_to_nat(0u);
v___x_167_ = lean_array_get_size(v_as_164_);
v___x_168_ = lean_nat_dec_lt(v___x_166_, v___x_167_);
if (v___x_168_ == 0)
{
return v___x_168_;
}
else
{
if (v___x_168_ == 0)
{
return v___x_168_;
}
else
{
size_t v___x_169_; size_t v___x_170_; uint8_t v___x_171_; 
v___x_169_ = ((size_t)0ULL);
v___x_170_ = lean_usize_of_nat(v___x_167_);
v___x_171_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1_spec__2(v_a_165_, v_as_164_, v___x_169_, v___x_170_);
return v___x_171_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_164_ = stack[0].m_obj;
lean_object* v_a_165_ = stack[1].m_obj;
uint8_t v_res_172_;
v_res_172_ = l_Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1(v_as_164_, v_a_165_);
stack->m_num = v_res_172_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1___boxed(lean_object* v_as_173_, lean_object* v_a_174_){
_start:
{
uint8_t v_res_175_; lean_object* v_r_176_; 
v_res_175_ = l_Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1(v_as_173_, v_a_174_);
lean_dec(v_a_174_);
lean_dec_ref(v_as_173_);
v_r_176_ = lean_box(v_res_175_);
return v_r_176_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_instMonadEIO___redArg();
return v___x_177_;
}
}
lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0(lean_object* v_msg_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v_toApplicative_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_251_; 
v___x_188_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__0);
v___x_189_ = l_StateRefT_x27_instMonad___redArg(v___x_188_);
v_toApplicative_190_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_251_ == 0)
{
lean_object* v_unused_252_; 
v_unused_252_ = lean_ctor_get(v___x_189_, 1);
lean_dec(v_unused_252_);
v___x_192_ = v___x_189_;
v_isShared_193_ = v_isSharedCheck_251_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_toApplicative_190_);
lean_dec(v___x_189_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_251_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v_toFunctor_194_; lean_object* v_toSeq_195_; lean_object* v_toSeqLeft_196_; lean_object* v_toSeqRight_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_249_; 
v_toFunctor_194_ = lean_ctor_get(v_toApplicative_190_, 0);
v_toSeq_195_ = lean_ctor_get(v_toApplicative_190_, 2);
v_toSeqLeft_196_ = lean_ctor_get(v_toApplicative_190_, 3);
v_toSeqRight_197_ = lean_ctor_get(v_toApplicative_190_, 4);
v_isSharedCheck_249_ = !lean_is_exclusive(v_toApplicative_190_);
if (v_isSharedCheck_249_ == 0)
{
lean_object* v_unused_250_; 
v_unused_250_ = lean_ctor_get(v_toApplicative_190_, 1);
lean_dec(v_unused_250_);
v___x_199_ = v_toApplicative_190_;
v_isShared_200_ = v_isSharedCheck_249_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_toSeqRight_197_);
lean_inc(v_toSeqLeft_196_);
lean_inc(v_toSeq_195_);
lean_inc(v_toFunctor_194_);
lean_dec(v_toApplicative_190_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_249_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___f_201_; lean_object* v___f_202_; lean_object* v___f_203_; lean_object* v___f_204_; lean_object* v___x_205_; lean_object* v___f_206_; lean_object* v___f_207_; lean_object* v___f_208_; lean_object* v___x_210_; 
v___f_201_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__1));
v___f_202_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_194_);
v___f_203_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_203_, 0, v_toFunctor_194_);
v___f_204_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_204_, 0, v_toFunctor_194_);
v___x_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_205_, 0, v___f_203_);
lean_ctor_set(v___x_205_, 1, v___f_204_);
v___f_206_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_206_, 0, v_toSeqRight_197_);
v___f_207_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_207_, 0, v_toSeqLeft_196_);
v___f_208_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_208_, 0, v_toSeq_195_);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 4, v___f_206_);
lean_ctor_set(v___x_199_, 3, v___f_207_);
lean_ctor_set(v___x_199_, 2, v___f_208_);
lean_ctor_set(v___x_199_, 1, v___f_201_);
lean_ctor_set(v___x_199_, 0, v___x_205_);
v___x_210_ = v___x_199_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_205_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v___f_201_);
lean_ctor_set(v_reuseFailAlloc_248_, 2, v___f_208_);
lean_ctor_set(v_reuseFailAlloc_248_, 3, v___f_207_);
lean_ctor_set(v_reuseFailAlloc_248_, 4, v___f_206_);
v___x_210_ = v_reuseFailAlloc_248_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
lean_object* v___x_212_; 
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 1, v___f_202_);
lean_ctor_set(v___x_192_, 0, v___x_210_);
v___x_212_ = v___x_192_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_210_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v___f_202_);
v___x_212_ = v_reuseFailAlloc_247_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_213_; lean_object* v_toApplicative_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_245_; 
v___x_213_ = l_StateRefT_x27_instMonad___redArg(v___x_212_);
v_toApplicative_214_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_245_ == 0)
{
lean_object* v_unused_246_; 
v_unused_246_ = lean_ctor_get(v___x_213_, 1);
lean_dec(v_unused_246_);
v___x_216_ = v___x_213_;
v_isShared_217_ = v_isSharedCheck_245_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_toApplicative_214_);
lean_dec(v___x_213_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_245_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v_toFunctor_218_; lean_object* v_toSeq_219_; lean_object* v_toSeqLeft_220_; lean_object* v_toSeqRight_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_243_; 
v_toFunctor_218_ = lean_ctor_get(v_toApplicative_214_, 0);
v_toSeq_219_ = lean_ctor_get(v_toApplicative_214_, 2);
v_toSeqLeft_220_ = lean_ctor_get(v_toApplicative_214_, 3);
v_toSeqRight_221_ = lean_ctor_get(v_toApplicative_214_, 4);
v_isSharedCheck_243_ = !lean_is_exclusive(v_toApplicative_214_);
if (v_isSharedCheck_243_ == 0)
{
lean_object* v_unused_244_; 
v_unused_244_ = lean_ctor_get(v_toApplicative_214_, 1);
lean_dec(v_unused_244_);
v___x_223_ = v_toApplicative_214_;
v_isShared_224_ = v_isSharedCheck_243_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_toSeqRight_221_);
lean_inc(v_toSeqLeft_220_);
lean_inc(v_toSeq_219_);
lean_inc(v_toFunctor_218_);
lean_dec(v_toApplicative_214_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_243_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___f_225_; lean_object* v___f_226_; lean_object* v___f_227_; lean_object* v___f_228_; lean_object* v___x_229_; lean_object* v___f_230_; lean_object* v___f_231_; lean_object* v___f_232_; lean_object* v___x_234_; 
v___f_225_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__3));
v___f_226_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__4));
lean_inc_ref(v_toFunctor_218_);
v___f_227_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_227_, 0, v_toFunctor_218_);
v___f_228_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_228_, 0, v_toFunctor_218_);
v___x_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_229_, 0, v___f_227_);
lean_ctor_set(v___x_229_, 1, v___f_228_);
v___f_230_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_230_, 0, v_toSeqRight_221_);
v___f_231_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_231_, 0, v_toSeqLeft_220_);
v___f_232_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_232_, 0, v_toSeq_219_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 4, v___f_230_);
lean_ctor_set(v___x_223_, 3, v___f_231_);
lean_ctor_set(v___x_223_, 2, v___f_232_);
lean_ctor_set(v___x_223_, 1, v___f_225_);
lean_ctor_set(v___x_223_, 0, v___x_229_);
v___x_234_ = v___x_223_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v___f_225_);
lean_ctor_set(v_reuseFailAlloc_242_, 2, v___f_232_);
lean_ctor_set(v_reuseFailAlloc_242_, 3, v___f_231_);
lean_ctor_set(v_reuseFailAlloc_242_, 4, v___f_230_);
v___x_234_ = v_reuseFailAlloc_242_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
lean_object* v___x_236_; 
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 1, v___f_226_);
lean_ctor_set(v___x_216_, 0, v___x_234_);
v___x_236_ = v___x_216_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v___f_226_);
v___x_236_ = v_reuseFailAlloc_241_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_10567__overap_239_; lean_object* v___x_240_; 
v___x_237_ = lean_box(0);
v___x_238_ = l_instInhabitedOfMonad___redArg(v___x_236_, v___x_237_);
v___x_10567__overap_239_ = lean_panic_fn_borrowed(v___x_238_, v_msg_182_);
lean_dec(v___x_238_);
lean_inc(v___y_186_);
lean_inc_ref(v___y_185_);
lean_inc(v___y_184_);
lean_inc_ref(v___y_183_);
v___x_240_ = lean_apply_5(v___x_10567__overap_239_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, lean_box(0));
return v___x_240_;
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
LEAN_EXPORT void l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_182_ = stack[0].m_obj;
lean_object* v___y_183_ = stack[1].m_obj;
lean_object* v___y_184_ = stack[2].m_obj;
lean_object* v___y_185_ = stack[3].m_obj;
lean_object* v___y_186_ = stack[4].m_obj;
lean_object* v_res_253_;
v_res_253_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0(v_msg_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
stack->m_obj
 = v_res_253_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___boxed(lean_object* v_msg_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0(v_msg_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
return v_res_260_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(lean_object* v_msgData_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v___x_267_; lean_object* v_env_268_; uint8_t v___x_269_; lean_object* v_env_270_; lean_object* v___x_271_; lean_object* v_toCold_272_; lean_object* v_mctx_273_; lean_object* v_lctx_274_; lean_object* v_options_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_267_ = lean_st_ref_get(v___y_265_);
v_env_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc_ref(v_env_268_);
lean_dec(v___x_267_);
v___x_269_ = 0;
v_env_270_ = l_Lean_Environment_setRecordingDeps(v_env_268_, v___x_269_);
v___x_271_ = lean_st_ref_get(v___y_263_);
v_toCold_272_ = lean_ctor_get(v___y_264_, 0);
v_mctx_273_ = lean_ctor_get(v___x_271_, 0);
lean_inc_ref(v_mctx_273_);
lean_dec(v___x_271_);
v_lctx_274_ = lean_ctor_get(v___y_262_, 2);
v_options_275_ = lean_ctor_get(v_toCold_272_, 2);
lean_inc_ref(v_options_275_);
lean_inc_ref(v_lctx_274_);
v___x_276_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_276_, 0, v_env_270_);
lean_ctor_set(v___x_276_, 1, v_mctx_273_);
lean_ctor_set(v___x_276_, 2, v_lctx_274_);
lean_ctor_set(v___x_276_, 3, v_options_275_);
v___x_277_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
lean_ctor_set(v___x_277_, 1, v_msgData_261_);
v___x_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
return v___x_278_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_261_ = stack[0].m_obj;
lean_object* v___y_262_ = stack[1].m_obj;
lean_object* v___y_263_ = stack[2].m_obj;
lean_object* v___y_264_ = stack[3].m_obj;
lean_object* v___y_265_ = stack[4].m_obj;
lean_object* v_res_279_;
v_res_279_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msgData_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
stack->m_obj
 = v_res_279_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5___boxed(lean_object* v_msgData_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msgData_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
return v_res_286_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(lean_object* v_msg_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v_ref_293_; lean_object* v___x_294_; lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_303_; 
v_ref_293_ = lean_ctor_get(v___y_290_, 2);
v___x_294_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msg_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
v_a_295_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_303_ == 0)
{
v___x_297_ = v___x_294_;
v_isShared_298_ = v_isSharedCheck_303_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v___x_294_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_303_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_299_; lean_object* v___x_301_; 
lean_inc(v_ref_293_);
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v_ref_293_);
lean_ctor_set(v___x_299_, 1, v_a_295_);
if (v_isShared_298_ == 0)
{
lean_ctor_set_tag(v___x_297_, 1);
lean_ctor_set(v___x_297_, 0, v___x_299_);
v___x_301_ = v___x_297_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_299_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_287_ = stack[0].m_obj;
lean_object* v___y_288_ = stack[1].m_obj;
lean_object* v___y_289_ = stack[2].m_obj;
lean_object* v___y_290_ = stack[3].m_obj;
lean_object* v___y_291_ = stack[4].m_obj;
lean_object* v_res_304_;
v_res_304_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v_msg_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
stack->m_obj
 = v_res_304_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg___boxed(lean_object* v_msg_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v_msg_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
return v_res_311_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__1(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__0));
v___x_314_ = l_Lean_stringToMessageData(v___x_313_);
return v___x_314_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__3(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__2));
v___x_317_ = l_Lean_stringToMessageData(v___x_316_);
return v___x_317_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__7(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_321_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__6));
v___x_322_ = lean_unsigned_to_nat(11u);
v___x_323_ = lean_unsigned_to_nat(122u);
v___x_324_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__5));
v___x_325_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__4));
v___x_326_ = l_mkPanicMessageWithDecl(v___x_325_, v___x_324_, v___x_323_, v___x_322_, v___x_321_);
return v___x_326_;
}
}
lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0(lean_object* v_constName_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v___x_341_; lean_object* v_env_342_; uint8_t v___x_343_; lean_object* v___x_344_; 
v___x_341_ = lean_st_ref_get(v___y_331_);
v_env_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc_ref(v_env_342_);
lean_dec(v___x_341_);
v___x_343_ = 0;
lean_inc(v_constName_327_);
v___x_344_ = l_Lean_Environment_findAsync_x3f(v_env_342_, v_constName_327_, v___x_343_);
if (lean_obj_tag(v___x_344_) == 1)
{
lean_object* v_val_345_; uint8_t v_kind_346_; 
v_val_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_val_345_);
lean_dec_ref_known(v___x_344_, 1);
v_kind_346_ = lean_ctor_get_uint8(v_val_345_, sizeof(void*)*3);
if (v_kind_346_ == 6)
{
lean_object* v___x_347_; 
v___x_347_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_345_);
if (lean_obj_tag(v___x_347_) == 6)
{
lean_object* v_val_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
lean_dec(v_constName_327_);
v_val_348_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_347_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_val_348_);
lean_dec(v___x_347_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
lean_ctor_set_tag(v___x_350_, 0);
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_val_348_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
else
{
lean_object* v___x_356_; lean_object* v___x_357_; 
lean_dec_ref(v___x_347_);
v___x_356_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__7);
v___x_357_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0(v___x_356_, v___y_328_, v___y_329_, v___y_330_, v___y_331_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_366_; 
v_a_358_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_366_ == 0)
{
v___x_360_ = v___x_357_;
v_isShared_361_ = v_isSharedCheck_366_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_357_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_366_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
if (lean_obj_tag(v_a_358_) == 0)
{
lean_del_object(v___x_360_);
goto v___jp_333_;
}
else
{
lean_object* v_val_362_; lean_object* v___x_364_; 
lean_dec(v_constName_327_);
v_val_362_ = lean_ctor_get(v_a_358_, 0);
lean_inc(v_val_362_);
lean_dec_ref_known(v_a_358_, 1);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 0, v_val_362_);
v___x_364_ = v___x_360_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_val_362_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
else
{
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_374_; 
lean_dec(v_constName_327_);
v_a_367_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_374_ == 0)
{
v___x_369_ = v___x_357_;
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_357_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_a_367_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
}
else
{
lean_dec(v_val_345_);
goto v___jp_333_;
}
}
else
{
lean_dec(v___x_344_);
goto v___jp_333_;
}
v___jp_333_:
{
lean_object* v___x_334_; uint8_t v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_334_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__1);
v___x_335_ = 0;
v___x_336_ = l_Lean_MessageData_ofConstName(v_constName_327_, v___x_335_);
v___x_337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_334_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___x_338_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__3);
v___x_339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_337_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
v___x_340_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_339_, v___y_328_, v___y_329_, v___y_330_, v___y_331_);
return v___x_340_;
}
}
}
LEAN_EXPORT void l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_327_ = stack[0].m_obj;
lean_object* v___y_328_ = stack[1].m_obj;
lean_object* v___y_329_ = stack[2].m_obj;
lean_object* v___y_330_ = stack[3].m_obj;
lean_object* v___y_331_ = stack[4].m_obj;
lean_object* v_res_375_;
v_res_375_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0(v_constName_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_);
stack->m_obj
 = v_res_375_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___boxed(lean_object* v_constName_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0(v_constName_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
return v_res_382_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_reduceSparseCasesOn_spec__2(size_t v_sz_383_, size_t v_i_384_, lean_object* v_bs_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
uint8_t v___x_391_; 
v___x_391_ = lean_usize_dec_lt(v_i_384_, v_sz_383_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; 
v___x_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_392_, 0, v_bs_385_);
return v___x_392_;
}
else
{
lean_object* v_v_393_; lean_object* v___x_394_; lean_object* v_bs_x27_395_; lean_object* v___x_396_; 
v_v_393_ = lean_array_uget(v_bs_385_, v_i_384_);
v___x_394_ = lean_unsigned_to_nat(0u);
v_bs_x27_395_ = lean_array_uset(v_bs_385_, v_i_384_, v___x_394_);
v___x_396_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0(v_v_393_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v_a_397_; lean_object* v_cidx_398_; size_t v___x_399_; size_t v___x_400_; lean_object* v___x_401_; 
v_a_397_ = lean_ctor_get(v___x_396_, 0);
lean_inc(v_a_397_);
lean_dec_ref_known(v___x_396_, 1);
v_cidx_398_ = lean_ctor_get(v_a_397_, 2);
lean_inc(v_cidx_398_);
lean_dec(v_a_397_);
v___x_399_ = ((size_t)1ULL);
v___x_400_ = lean_usize_add(v_i_384_, v___x_399_);
v___x_401_ = lean_array_uset(v_bs_x27_395_, v_i_384_, v_cidx_398_);
v_i_384_ = v___x_400_;
v_bs_385_ = v___x_401_;
goto _start;
}
else
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
lean_dec_ref(v_bs_x27_395_);
v_a_403_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v___x_396_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_396_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_403_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_reduceSparseCasesOn_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_383_ = stack[0].m_num;
size_t v_i_384_ = stack[1].m_num;
lean_object* v_bs_385_ = stack[2].m_obj;
lean_object* v___y_386_ = stack[3].m_obj;
lean_object* v___y_387_ = stack[4].m_obj;
lean_object* v___y_388_ = stack[5].m_obj;
lean_object* v___y_389_ = stack[6].m_obj;
lean_object* v_res_411_;
v_res_411_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_reduceSparseCasesOn_spec__2(v_sz_383_, v_i_384_, v_bs_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
stack->m_obj
 = v_res_411_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_reduceSparseCasesOn_spec__2___boxed(lean_object* v_sz_412_, lean_object* v_i_413_, lean_object* v_bs_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
size_t v_sz_boxed_420_; size_t v_i_boxed_421_; lean_object* v_res_422_; 
v_sz_boxed_420_ = lean_unbox_usize(v_sz_412_);
lean_dec(v_sz_412_);
v_i_boxed_421_ = lean_unbox_usize(v_i_413_);
lean_dec(v_i_413_);
v_res_422_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_reduceSparseCasesOn_spec__2(v_sz_boxed_420_, v_i_boxed_421_, v_bs_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
return v_res_422_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0(void){
_start:
{
lean_object* v___x_423_; lean_object* v_dummy_424_; 
v___x_423_ = lean_box(0);
v_dummy_424_ = l_Lean_Expr_sort___override(v___x_423_);
return v_dummy_424_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__2(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1));
v___x_427_ = l_Lean_stringToMessageData(v___x_426_);
return v___x_427_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(lean_object* v___x_428_, lean_object* v_x_429_, lean_object* v_majorPos_430_, lean_object* v_insterestingCtors_431_, lean_object* v_declName_432_, lean_object* v_snd_433_, lean_object* v_arity_434_, lean_object* v_mvarId_435_, lean_object* v___f_436_, lean_object* v_____r_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = lean_array_get_borrowed(v___x_428_, v_x_429_, v_majorPos_430_);
lean_inc(v___x_443_);
v___x_444_ = l_Lean_Meta_isConstructorApp_x27_x3f(v___x_443_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_a_445_);
lean_dec_ref_known(v___x_444_, 1);
if (lean_obj_tag(v_a_445_) == 1)
{
lean_object* v_val_446_; lean_object* v_toConstantVal_447_; lean_object* v_cidx_448_; lean_object* v_name_449_; uint8_t v___x_450_; 
v_val_446_ = lean_ctor_get(v_a_445_, 0);
lean_inc(v_val_446_);
lean_dec_ref_known(v_a_445_, 1);
v_toConstantVal_447_ = lean_ctor_get(v_val_446_, 0);
lean_inc_ref(v_toConstantVal_447_);
v_cidx_448_ = lean_ctor_get(v_val_446_, 2);
lean_inc(v_cidx_448_);
lean_dec(v_val_446_);
v_name_449_ = lean_ctor_get(v_toConstantVal_447_, 0);
lean_inc(v_name_449_);
lean_dec_ref(v_toConstantVal_447_);
v___x_450_ = l_Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1(v_insterestingCtors_431_, v_name_449_);
lean_dec(v_name_449_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; 
lean_dec_ref(v___f_436_);
v___x_451_ = l_Lean_Meta_getSparseCasesOnEq(v_declName_432_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_a_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v_dummy_456_; lean_object* v_nargs_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; size_t v_sz_466_; size_t v___x_467_; lean_object* v___x_468_; 
v_a_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_a_452_);
lean_dec_ref_known(v___x_451_, 1);
v___x_453_ = l_Lean_Expr_getAppFn(v_snd_433_);
v___x_454_ = l_Lean_Expr_constLevels_x21(v___x_453_);
lean_dec_ref(v___x_453_);
v___x_455_ = l_Lean_mkConst(v_a_452_, v___x_454_);
v_dummy_456_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0);
v_nargs_457_ = l_Lean_Expr_getAppNumArgs(v_snd_433_);
lean_inc(v_nargs_457_);
v___x_458_ = lean_mk_array(v_nargs_457_, v_dummy_456_);
v___x_459_ = lean_unsigned_to_nat(1u);
v___x_460_ = lean_nat_sub(v_nargs_457_, v___x_459_);
lean_dec(v_nargs_457_);
v___x_461_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_snd_433_, v___x_458_, v___x_460_);
v___x_462_ = lean_unsigned_to_nat(0u);
v___x_463_ = l_Array_toSubarray___redArg(v___x_461_, v___x_462_, v_arity_434_);
v___x_464_ = l_Subarray_copy___redArg(v___x_463_);
v___x_465_ = l_Lean_mkAppN(v___x_455_, v___x_464_);
lean_dec_ref(v___x_464_);
v_sz_466_ = lean_array_size(v_insterestingCtors_431_);
v___x_467_ = ((size_t)0ULL);
v___x_468_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_reduceSparseCasesOn_spec__2(v_sz_466_, v___x_467_, v_insterestingCtors_431_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_a_469_);
lean_dec_ref_known(v___x_468_, 1);
v___x_470_ = l_Lean_mkRawNatLit(v_cidx_448_);
v___x_471_ = l_Lean_mkHasNotBitProof(v___x_470_, v_a_469_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
lean_dec(v_a_469_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_a_472_);
lean_dec_ref_known(v___x_471_, 1);
v___x_473_ = l_Lean_Expr_app___override(v___x_465_, v_a_472_);
v___x_474_ = l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq(v_mvarId_435_, v___x_473_, v___x_450_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_484_; 
v_a_475_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_484_ == 0)
{
v___x_477_ = v___x_474_;
v_isShared_478_ = v_isSharedCheck_484_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_474_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_484_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_482_; 
v___x_479_ = lean_mk_empty_array_with_capacity(v___x_459_);
v___x_480_ = lean_array_push(v___x_479_, v_a_475_);
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 0, v___x_480_);
v___x_482_ = v___x_477_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_480_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
else
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
v_a_485_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_474_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_474_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
else
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
lean_dec_ref(v___x_465_);
lean_dec(v_mvarId_435_);
v_a_493_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_500_ == 0)
{
v___x_495_ = v___x_471_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_471_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_493_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
else
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
lean_dec_ref(v___x_465_);
lean_dec(v_cidx_448_);
lean_dec(v_mvarId_435_);
v_a_501_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_508_ == 0)
{
v___x_503_ = v___x_468_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_468_);
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
else
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
lean_dec(v_cidx_448_);
lean_dec(v_mvarId_435_);
lean_dec(v_arity_434_);
lean_dec_ref(v_snd_433_);
lean_dec_ref(v_insterestingCtors_431_);
v_a_509_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v___x_451_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_451_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_509_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
else
{
lean_object* v___x_517_; 
lean_dec(v_cidx_448_);
lean_dec(v_arity_434_);
lean_dec_ref(v_snd_433_);
lean_dec(v_declName_432_);
lean_dec_ref(v_insterestingCtors_431_);
v___x_517_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_435_, v___f_436_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_528_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_528_ == 0)
{
v___x_520_ = v___x_517_;
v_isShared_521_ = v_isSharedCheck_528_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_517_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_528_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_522_ = lean_unsigned_to_nat(1u);
v___x_523_ = lean_mk_empty_array_with_capacity(v___x_522_);
v___x_524_ = lean_array_push(v___x_523_, v_a_518_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_524_);
v___x_526_ = v___x_520_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
else
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
v_a_529_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_536_ == 0)
{
v___x_531_ = v___x_517_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_517_);
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
else
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
lean_dec(v_a_445_);
lean_dec_ref(v___f_436_);
lean_dec(v_mvarId_435_);
lean_dec(v_arity_434_);
lean_dec_ref(v_snd_433_);
lean_dec(v_declName_432_);
lean_dec_ref(v_insterestingCtors_431_);
v___x_537_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__2);
lean_inc(v___x_443_);
v___x_538_ = l_Lean_indentExpr(v___x_443_);
v___x_539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_537_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_539_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
return v___x_540_;
}
}
else
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_dec_ref(v___f_436_);
lean_dec(v_mvarId_435_);
lean_dec(v_arity_434_);
lean_dec_ref(v_snd_433_);
lean_dec(v_declName_432_);
lean_dec_ref(v_insterestingCtors_431_);
v_a_541_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_444_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_444_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_428_ = stack[0].m_obj;
lean_object* v_x_429_ = stack[1].m_obj;
lean_object* v_majorPos_430_ = stack[2].m_obj;
lean_object* v_insterestingCtors_431_ = stack[3].m_obj;
lean_object* v_declName_432_ = stack[4].m_obj;
lean_object* v_snd_433_ = stack[5].m_obj;
lean_object* v_arity_434_ = stack[6].m_obj;
lean_object* v_mvarId_435_ = stack[7].m_obj;
lean_object* v___f_436_ = stack[8].m_obj;
lean_object* v_____r_437_ = stack[9].m_obj;
lean_object* v___y_438_ = stack[10].m_obj;
lean_object* v___y_439_ = stack[11].m_obj;
lean_object* v___y_440_ = stack[12].m_obj;
lean_object* v___y_441_ = stack[13].m_obj;
lean_object* v_res_549_;
v_res_549_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(v___x_428_, v_x_429_, v_majorPos_430_, v_insterestingCtors_431_, v_declName_432_, v_snd_433_, v_arity_434_, v_mvarId_435_, v___f_436_, v_____r_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
stack->m_obj
 = v_res_549_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___boxed(lean_object* v___x_550_, lean_object* v_x_551_, lean_object* v_majorPos_552_, lean_object* v_insterestingCtors_553_, lean_object* v_declName_554_, lean_object* v_snd_555_, lean_object* v_arity_556_, lean_object* v_mvarId_557_, lean_object* v___f_558_, lean_object* v_____r_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(v___x_550_, v_x_551_, v_majorPos_552_, v_insterestingCtors_553_, v_declName_554_, v_snd_555_, v_arity_556_, v_mvarId_557_, v___f_558_, v_____r_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v_majorPos_552_);
lean_dec_ref(v_x_551_);
lean_dec_ref(v___x_550_);
return v_res_565_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__0));
v___x_568_ = l_Lean_stringToMessageData(v___x_567_);
return v___x_568_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2(uint8_t v___x_569_, lean_object* v___f_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
if (v___x_569_ == 0)
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_box(0);
lean_inc(v___y_574_);
lean_inc_ref(v___y_573_);
lean_inc(v___y_572_);
lean_inc_ref(v___y_571_);
v___x_577_ = lean_apply_6(v___f_570_, v___x_576_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, lean_box(0));
return v___x_577_;
}
else
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_dec_ref(v___f_570_);
v___x_578_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1);
v___x_579_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_578_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
v_a_580_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_579_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_579_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_569_ = stack[0].m_num;
lean_object* v___f_570_ = stack[1].m_obj;
lean_object* v___y_571_ = stack[2].m_obj;
lean_object* v___y_572_ = stack[3].m_obj;
lean_object* v___y_573_ = stack[4].m_obj;
lean_object* v___y_574_ = stack[5].m_obj;
lean_object* v_res_588_;
v_res_588_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2(v___x_569_, v___f_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
stack->m_obj
 = v_res_588_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___boxed(lean_object* v___x_589_, lean_object* v___f_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
uint8_t v___x_14746__boxed_596_; lean_object* v_res_597_; 
v___x_14746__boxed_596_ = lean_unbox(v___x_589_);
v_res_597_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2(v___x_14746__boxed_596_, v___f_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
return v_res_597_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11(lean_object* v_e_598_){
_start:
{
if (lean_obj_tag(v_e_598_) == 0)
{
uint8_t v___x_599_; 
v___x_599_ = 2;
return v___x_599_;
}
else
{
uint8_t v___x_600_; 
v___x_600_ = 0;
return v___x_600_;
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_598_ = stack[0].m_obj;
uint8_t v_res_601_;
v_res_601_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11(v_e_598_);
stack->m_num = v_res_601_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11___boxed(lean_object* v_e_602_){
_start:
{
uint8_t v_res_603_; lean_object* v_r_604_; 
v_res_603_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11(v_e_602_);
lean_dec_ref(v_e_602_);
v_r_604_ = lean_box(v_res_603_);
return v_r_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12(lean_object* v_opts_605_, lean_object* v_opt_606_){
_start:
{
lean_object* v_name_607_; lean_object* v_defValue_608_; lean_object* v_map_609_; lean_object* v___x_610_; 
v_name_607_ = lean_ctor_get(v_opt_606_, 0);
v_defValue_608_ = lean_ctor_get(v_opt_606_, 1);
v_map_609_ = lean_ctor_get(v_opts_605_, 0);
v___x_610_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_609_, v_name_607_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_inc(v_defValue_608_);
return v_defValue_608_;
}
else
{
lean_object* v_val_611_; 
v_val_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_val_611_);
lean_dec_ref_known(v___x_610_, 1);
if (lean_obj_tag(v_val_611_) == 3)
{
lean_object* v_v_612_; 
v_v_612_ = lean_ctor_get(v_val_611_, 0);
lean_inc(v_v_612_);
lean_dec_ref_known(v_val_611_, 1);
return v_v_612_;
}
else
{
lean_dec(v_val_611_);
lean_inc(v_defValue_608_);
return v_defValue_608_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12___boxed(lean_object* v_opts_613_, lean_object* v_opt_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12(v_opts_613_, v_opt_614_);
lean_dec_ref(v_opt_614_);
lean_dec_ref(v_opts_613_);
return v_res_615_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg(lean_object* v_x_616_){
_start:
{
if (lean_obj_tag(v_x_616_) == 0)
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
v_a_618_ = lean_ctor_get(v_x_616_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v_x_616_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v_x_616_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v_x_616_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
lean_ctor_set_tag(v___x_620_, 1);
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
else
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
v_a_626_ = lean_ctor_get(v_x_616_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v_x_616_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v_x_616_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v_x_616_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
lean_ctor_set_tag(v___x_628_, 0);
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_626_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_616_ = stack[0].m_obj;
lean_object* v_res_634_;
v_res_634_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg(v_x_616_);
stack->m_obj
 = v_res_634_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg___boxed(lean_object* v_x_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg(v_x_635_);
return v_res_637_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9_spec__10(size_t v_sz_638_, size_t v_i_639_, lean_object* v_bs_640_){
_start:
{
uint8_t v___x_641_; 
v___x_641_ = lean_usize_dec_lt(v_i_639_, v_sz_638_);
if (v___x_641_ == 0)
{
return v_bs_640_;
}
else
{
lean_object* v_v_642_; lean_object* v_msg_643_; lean_object* v___x_644_; lean_object* v_bs_x27_645_; size_t v___x_646_; size_t v___x_647_; lean_object* v___x_648_; 
v_v_642_ = lean_array_uget_borrowed(v_bs_640_, v_i_639_);
v_msg_643_ = lean_ctor_get(v_v_642_, 1);
lean_inc_ref(v_msg_643_);
v___x_644_ = lean_unsigned_to_nat(0u);
v_bs_x27_645_ = lean_array_uset(v_bs_640_, v_i_639_, v___x_644_);
v___x_646_ = ((size_t)1ULL);
v___x_647_ = lean_usize_add(v_i_639_, v___x_646_);
v___x_648_ = lean_array_uset(v_bs_x27_645_, v_i_639_, v_msg_643_);
v_i_639_ = v___x_647_;
v_bs_640_ = v___x_648_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9_spec__10_0interp(lean_interpreter_value* stack)
{
size_t v_sz_638_ = stack[0].m_num;
size_t v_i_639_ = stack[1].m_num;
lean_object* v_bs_640_ = stack[2].m_obj;
lean_object* v_res_650_;
v_res_650_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9_spec__10(v_sz_638_, v_i_639_, v_bs_640_);
stack->m_obj
 = v_res_650_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9_spec__10___boxed(lean_object* v_sz_651_, lean_object* v_i_652_, lean_object* v_bs_653_){
_start:
{
size_t v_sz_boxed_654_; size_t v_i_boxed_655_; lean_object* v_res_656_; 
v_sz_boxed_654_ = lean_unbox_usize(v_sz_651_);
lean_dec(v_sz_651_);
v_i_boxed_655_ = lean_unbox_usize(v_i_652_);
lean_dec(v_i_652_);
v_res_656_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9_spec__10(v_sz_boxed_654_, v_i_boxed_655_, v_bs_653_);
return v_res_656_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9(lean_object* v_oldTraces_657_, lean_object* v_data_658_, lean_object* v_ref_659_, lean_object* v_msg_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_toCold_666_; lean_object* v_currRecDepth_667_; lean_object* v_ref_668_; uint16_t v_optionFlags_669_; uint8_t v_suppressElabErrors_670_; uint8_t v_isRecordingDeps_671_; lean_object* v_ref_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v_traceState_675_; lean_object* v_traces_676_; lean_object* v___x_677_; size_t v_sz_678_; size_t v___x_679_; lean_object* v___x_680_; lean_object* v_msg_681_; lean_object* v___x_682_; lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_721_; 
v_toCold_666_ = lean_ctor_get(v___y_663_, 0);
v_currRecDepth_667_ = lean_ctor_get(v___y_663_, 1);
v_ref_668_ = lean_ctor_get(v___y_663_, 2);
v_optionFlags_669_ = lean_ctor_get_uint16(v___y_663_, sizeof(void*)*3);
v_suppressElabErrors_670_ = lean_ctor_get_uint8(v___y_663_, sizeof(void*)*3 + 2);
v_isRecordingDeps_671_ = lean_ctor_get_uint8(v___y_663_, sizeof(void*)*3 + 3);
v_ref_672_ = l_Lean_replaceRef(v_ref_659_, v_ref_668_);
lean_inc(v_currRecDepth_667_);
lean_inc_ref(v_toCold_666_);
v___x_673_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_673_, 0, v_toCold_666_);
lean_ctor_set(v___x_673_, 1, v_currRecDepth_667_);
lean_ctor_set(v___x_673_, 2, v_ref_672_);
lean_ctor_set_uint16(v___x_673_, sizeof(void*)*3, v_optionFlags_669_);
lean_ctor_set_uint8(v___x_673_, sizeof(void*)*3 + 2, v_suppressElabErrors_670_);
lean_ctor_set_uint8(v___x_673_, sizeof(void*)*3 + 3, v_isRecordingDeps_671_);
v___x_674_ = lean_st_ref_get(v___y_664_);
v_traceState_675_ = lean_ctor_get(v___x_674_, 4);
lean_inc_ref(v_traceState_675_);
lean_dec(v___x_674_);
v_traces_676_ = lean_ctor_get(v_traceState_675_, 0);
lean_inc_ref(v_traces_676_);
lean_dec_ref(v_traceState_675_);
v___x_677_ = l_Lean_PersistentArray_toArray___redArg(v_traces_676_);
lean_dec_ref(v_traces_676_);
v_sz_678_ = lean_array_size(v___x_677_);
v___x_679_ = ((size_t)0ULL);
v___x_680_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9_spec__10(v_sz_678_, v___x_679_, v___x_677_);
v_msg_681_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_681_, 0, v_data_658_);
lean_ctor_set(v_msg_681_, 1, v_msg_660_);
lean_ctor_set(v_msg_681_, 2, v___x_680_);
v___x_682_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msg_681_, v___y_661_, v___y_662_, v___x_673_, v___y_664_);
lean_dec_ref_known(v___x_673_, 3);
v_a_683_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_721_ == 0)
{
v___x_685_ = v___x_682_;
v_isShared_686_ = v_isSharedCheck_721_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_682_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_721_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; lean_object* v_traceState_688_; lean_object* v_env_689_; lean_object* v_nextMacroScope_690_; lean_object* v_ngen_691_; lean_object* v_auxDeclNGen_692_; lean_object* v_cache_693_; lean_object* v_recordedDeps_694_; lean_object* v_messages_695_; lean_object* v_infoState_696_; lean_object* v_snapshotTasks_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_720_; 
v___x_687_ = lean_st_ref_take(v___y_664_);
v_traceState_688_ = lean_ctor_get(v___x_687_, 4);
v_env_689_ = lean_ctor_get(v___x_687_, 0);
v_nextMacroScope_690_ = lean_ctor_get(v___x_687_, 1);
v_ngen_691_ = lean_ctor_get(v___x_687_, 2);
v_auxDeclNGen_692_ = lean_ctor_get(v___x_687_, 3);
v_cache_693_ = lean_ctor_get(v___x_687_, 5);
v_recordedDeps_694_ = lean_ctor_get(v___x_687_, 6);
v_messages_695_ = lean_ctor_get(v___x_687_, 7);
v_infoState_696_ = lean_ctor_get(v___x_687_, 8);
v_snapshotTasks_697_ = lean_ctor_get(v___x_687_, 9);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_720_ == 0)
{
v___x_699_ = v___x_687_;
v_isShared_700_ = v_isSharedCheck_720_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_snapshotTasks_697_);
lean_inc(v_infoState_696_);
lean_inc(v_messages_695_);
lean_inc(v_recordedDeps_694_);
lean_inc(v_cache_693_);
lean_inc(v_traceState_688_);
lean_inc(v_auxDeclNGen_692_);
lean_inc(v_ngen_691_);
lean_inc(v_nextMacroScope_690_);
lean_inc(v_env_689_);
lean_dec(v___x_687_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_720_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
uint64_t v_tid_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_718_; 
v_tid_701_ = lean_ctor_get_uint64(v_traceState_688_, sizeof(void*)*1);
v_isSharedCheck_718_ = !lean_is_exclusive(v_traceState_688_);
if (v_isSharedCheck_718_ == 0)
{
lean_object* v_unused_719_; 
v_unused_719_ = lean_ctor_get(v_traceState_688_, 0);
lean_dec(v_unused_719_);
v___x_703_ = v_traceState_688_;
v_isShared_704_ = v_isSharedCheck_718_;
goto v_resetjp_702_;
}
else
{
lean_dec(v_traceState_688_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_718_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_705_ = lean_box(0);
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v_ref_659_);
lean_ctor_set(v___x_706_, 1, v_a_683_);
v___x_707_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_657_, v___x_706_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_707_);
v___x_709_ = v___x_703_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_707_);
lean_ctor_set_uint64(v_reuseFailAlloc_717_, sizeof(void*)*1, v_tid_701_);
v___x_709_ = v_reuseFailAlloc_717_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
lean_object* v___x_711_; 
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 4, v___x_709_);
v___x_711_ = v___x_699_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_env_689_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_nextMacroScope_690_);
lean_ctor_set(v_reuseFailAlloc_716_, 2, v_ngen_691_);
lean_ctor_set(v_reuseFailAlloc_716_, 3, v_auxDeclNGen_692_);
lean_ctor_set(v_reuseFailAlloc_716_, 4, v___x_709_);
lean_ctor_set(v_reuseFailAlloc_716_, 5, v_cache_693_);
lean_ctor_set(v_reuseFailAlloc_716_, 6, v_recordedDeps_694_);
lean_ctor_set(v_reuseFailAlloc_716_, 7, v_messages_695_);
lean_ctor_set(v_reuseFailAlloc_716_, 8, v_infoState_696_);
lean_ctor_set(v_reuseFailAlloc_716_, 9, v_snapshotTasks_697_);
v___x_711_ = v_reuseFailAlloc_716_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_712_ = lean_st_ref_put(v___y_664_, v___x_711_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 0, v___x_705_);
v___x_714_ = v___x_685_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_705_);
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
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_657_ = stack[0].m_obj;
lean_object* v_data_658_ = stack[1].m_obj;
lean_object* v_ref_659_ = stack[2].m_obj;
lean_object* v_msg_660_ = stack[3].m_obj;
lean_object* v___y_661_ = stack[4].m_obj;
lean_object* v___y_662_ = stack[5].m_obj;
lean_object* v___y_663_ = stack[6].m_obj;
lean_object* v___y_664_ = stack[7].m_obj;
lean_object* v_res_722_;
v_res_722_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9(v_oldTraces_657_, v_data_658_, v_ref_659_, v_msg_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
stack->m_obj
 = v_res_722_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9___boxed(lean_object* v_oldTraces_723_, lean_object* v_data_724_, lean_object* v_ref_725_, lean_object* v_msg_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9(v_oldTraces_723_, v_data_724_, v_ref_725_, v_msg_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
return v_res_732_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0(void){
_start:
{
lean_object* v___x_733_; double v___x_734_; 
v___x_733_ = lean_unsigned_to_nat(0u);
v___x_734_ = lean_float_of_nat(v___x_733_);
return v___x_734_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2(void){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__1));
v___x_737_ = l_Lean_stringToMessageData(v___x_736_);
return v___x_737_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__3(void){
_start:
{
lean_object* v___x_738_; double v___x_739_; 
v___x_738_ = lean_unsigned_to_nat(1000u);
v___x_739_ = lean_float_of_nat(v___x_738_);
return v___x_739_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(lean_object* v_cls_740_, uint8_t v_collapsed_741_, lean_object* v_tag_742_, lean_object* v_opts_743_, uint8_t v_clsEnabled_744_, lean_object* v_oldTraces_745_, lean_object* v_msg_746_, lean_object* v_resStartStop_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v_fst_753_; lean_object* v_snd_754_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v_data_758_; lean_object* v_fst_769_; lean_object* v_snd_770_; lean_object* v___x_771_; uint8_t v___x_772_; lean_object* v___y_774_; lean_object* v_a_775_; uint8_t v___y_790_; double v___y_822_; 
v_fst_753_ = lean_ctor_get(v_resStartStop_747_, 0);
lean_inc(v_fst_753_);
v_snd_754_ = lean_ctor_get(v_resStartStop_747_, 1);
lean_inc(v_snd_754_);
lean_dec_ref(v_resStartStop_747_);
v_fst_769_ = lean_ctor_get(v_snd_754_, 0);
lean_inc(v_fst_769_);
v_snd_770_ = lean_ctor_get(v_snd_754_, 1);
lean_inc(v_snd_770_);
lean_dec(v_snd_754_);
v___x_771_ = l_Lean_trace_profiler;
v___x_772_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_opts_743_, v___x_771_);
if (v___x_772_ == 0)
{
v___y_790_ = v___x_772_;
goto v___jp_789_;
}
else
{
lean_object* v___x_827_; uint8_t v___x_828_; 
v___x_827_ = l_Lean_trace_profiler_useHeartbeats;
v___x_828_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_opts_743_, v___x_827_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; lean_object* v___x_830_; double v___x_831_; double v___x_832_; double v___x_833_; 
v___x_829_ = l_Lean_trace_profiler_threshold;
v___x_830_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12(v_opts_743_, v___x_829_);
v___x_831_ = lean_float_of_nat(v___x_830_);
v___x_832_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__3);
v___x_833_ = lean_float_div(v___x_831_, v___x_832_);
v___y_822_ = v___x_833_;
goto v___jp_821_;
}
else
{
lean_object* v___x_834_; lean_object* v___x_835_; double v___x_836_; 
v___x_834_ = l_Lean_trace_profiler_threshold;
v___x_835_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12(v_opts_743_, v___x_834_);
v___x_836_ = lean_float_of_nat(v___x_835_);
v___y_822_ = v___x_836_;
goto v___jp_821_;
}
}
v___jp_755_:
{
lean_object* v___x_759_; 
lean_inc(v___y_757_);
v___x_759_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9(v_oldTraces_745_, v_data_758_, v___y_757_, v___y_756_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v___x_760_; 
lean_dec_ref_known(v___x_759_, 1);
v___x_760_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg(v_fst_753_);
return v___x_760_;
}
else
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_dec(v_fst_753_);
v_a_761_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_759_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_759_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
v___jp_773_:
{
uint8_t v_result_776_; lean_object* v___x_777_; lean_object* v___x_778_; double v___x_779_; lean_object* v_data_780_; 
v_result_776_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11(v_fst_753_);
v___x_777_ = lean_box(v_result_776_);
v___x_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
v___x_779_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0);
lean_inc_ref(v_tag_742_);
lean_inc_ref(v___x_778_);
lean_inc(v_cls_740_);
v_data_780_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_780_, 0, v_cls_740_);
lean_ctor_set(v_data_780_, 1, v___x_778_);
lean_ctor_set(v_data_780_, 2, v_tag_742_);
lean_ctor_set_float(v_data_780_, sizeof(void*)*3, v___x_779_);
lean_ctor_set_float(v_data_780_, sizeof(void*)*3 + 8, v___x_779_);
lean_ctor_set_uint8(v_data_780_, sizeof(void*)*3 + 16, v_collapsed_741_);
if (v___x_772_ == 0)
{
lean_dec_ref_known(v___x_778_, 1);
lean_dec(v_snd_770_);
lean_dec(v_fst_769_);
lean_dec_ref(v_tag_742_);
lean_dec(v_cls_740_);
v___y_756_ = v_a_775_;
v___y_757_ = v___y_774_;
v_data_758_ = v_data_780_;
goto v___jp_755_;
}
else
{
lean_object* v_data_781_; double v___x_782_; double v___x_783_; 
lean_dec_ref_known(v_data_780_, 3);
v_data_781_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_781_, 0, v_cls_740_);
lean_ctor_set(v_data_781_, 1, v___x_778_);
lean_ctor_set(v_data_781_, 2, v_tag_742_);
v___x_782_ = lean_unbox_float(v_fst_769_);
lean_dec(v_fst_769_);
lean_ctor_set_float(v_data_781_, sizeof(void*)*3, v___x_782_);
v___x_783_ = lean_unbox_float(v_snd_770_);
lean_dec(v_snd_770_);
lean_ctor_set_float(v_data_781_, sizeof(void*)*3 + 8, v___x_783_);
lean_ctor_set_uint8(v_data_781_, sizeof(void*)*3 + 16, v_collapsed_741_);
v___y_756_ = v_a_775_;
v___y_757_ = v___y_774_;
v_data_758_ = v_data_781_;
goto v___jp_755_;
}
}
v___jp_784_:
{
lean_object* v_ref_785_; lean_object* v___x_786_; 
v_ref_785_ = lean_ctor_get(v___y_750_, 2);
lean_inc(v___y_751_);
lean_inc_ref(v___y_750_);
lean_inc(v___y_749_);
lean_inc_ref(v___y_748_);
lean_inc(v_fst_753_);
v___x_786_ = lean_apply_6(v_msg_746_, v_fst_753_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, lean_box(0));
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_a_787_);
lean_dec_ref_known(v___x_786_, 1);
v___y_774_ = v_ref_785_;
v_a_775_ = v_a_787_;
goto v___jp_773_;
}
else
{
lean_object* v___x_788_; 
lean_dec_ref_known(v___x_786_, 1);
v___x_788_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2);
v___y_774_ = v_ref_785_;
v_a_775_ = v___x_788_;
goto v___jp_773_;
}
}
v___jp_789_:
{
if (v_clsEnabled_744_ == 0)
{
if (v___y_790_ == 0)
{
lean_object* v___x_791_; lean_object* v_traceState_792_; lean_object* v_env_793_; lean_object* v_nextMacroScope_794_; lean_object* v_ngen_795_; lean_object* v_auxDeclNGen_796_; lean_object* v_cache_797_; lean_object* v_recordedDeps_798_; lean_object* v_messages_799_; lean_object* v_infoState_800_; lean_object* v_snapshotTasks_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_820_; 
lean_dec(v_snd_770_);
lean_dec(v_fst_769_);
lean_dec_ref(v_msg_746_);
lean_dec_ref(v_tag_742_);
lean_dec(v_cls_740_);
v___x_791_ = lean_st_ref_take(v___y_751_);
v_traceState_792_ = lean_ctor_get(v___x_791_, 4);
v_env_793_ = lean_ctor_get(v___x_791_, 0);
v_nextMacroScope_794_ = lean_ctor_get(v___x_791_, 1);
v_ngen_795_ = lean_ctor_get(v___x_791_, 2);
v_auxDeclNGen_796_ = lean_ctor_get(v___x_791_, 3);
v_cache_797_ = lean_ctor_get(v___x_791_, 5);
v_recordedDeps_798_ = lean_ctor_get(v___x_791_, 6);
v_messages_799_ = lean_ctor_get(v___x_791_, 7);
v_infoState_800_ = lean_ctor_get(v___x_791_, 8);
v_snapshotTasks_801_ = lean_ctor_get(v___x_791_, 9);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_820_ == 0)
{
v___x_803_ = v___x_791_;
v_isShared_804_ = v_isSharedCheck_820_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_snapshotTasks_801_);
lean_inc(v_infoState_800_);
lean_inc(v_messages_799_);
lean_inc(v_recordedDeps_798_);
lean_inc(v_cache_797_);
lean_inc(v_traceState_792_);
lean_inc(v_auxDeclNGen_796_);
lean_inc(v_ngen_795_);
lean_inc(v_nextMacroScope_794_);
lean_inc(v_env_793_);
lean_dec(v___x_791_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_820_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
uint64_t v_tid_805_; lean_object* v_traces_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_819_; 
v_tid_805_ = lean_ctor_get_uint64(v_traceState_792_, sizeof(void*)*1);
v_traces_806_ = lean_ctor_get(v_traceState_792_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v_traceState_792_);
if (v_isSharedCheck_819_ == 0)
{
v___x_808_ = v_traceState_792_;
v_isShared_809_ = v_isSharedCheck_819_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_traces_806_);
lean_dec(v_traceState_792_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_819_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_810_; lean_object* v___x_812_; 
v___x_810_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_745_, v_traces_806_);
lean_dec_ref(v_traces_806_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v___x_810_);
v___x_812_ = v___x_808_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_810_);
lean_ctor_set_uint64(v_reuseFailAlloc_818_, sizeof(void*)*1, v_tid_805_);
v___x_812_ = v_reuseFailAlloc_818_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_814_; 
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 4, v___x_812_);
v___x_814_ = v___x_803_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_env_793_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v_nextMacroScope_794_);
lean_ctor_set(v_reuseFailAlloc_817_, 2, v_ngen_795_);
lean_ctor_set(v_reuseFailAlloc_817_, 3, v_auxDeclNGen_796_);
lean_ctor_set(v_reuseFailAlloc_817_, 4, v___x_812_);
lean_ctor_set(v_reuseFailAlloc_817_, 5, v_cache_797_);
lean_ctor_set(v_reuseFailAlloc_817_, 6, v_recordedDeps_798_);
lean_ctor_set(v_reuseFailAlloc_817_, 7, v_messages_799_);
lean_ctor_set(v_reuseFailAlloc_817_, 8, v_infoState_800_);
lean_ctor_set(v_reuseFailAlloc_817_, 9, v_snapshotTasks_801_);
v___x_814_ = v_reuseFailAlloc_817_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = lean_st_ref_put(v___y_751_, v___x_814_);
v___x_816_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg(v_fst_753_);
return v___x_816_;
}
}
}
}
}
else
{
goto v___jp_784_;
}
}
else
{
goto v___jp_784_;
}
}
v___jp_821_:
{
double v___x_823_; double v___x_824_; double v___x_825_; uint8_t v___x_826_; 
v___x_823_ = lean_unbox_float(v_snd_770_);
v___x_824_ = lean_unbox_float(v_fst_769_);
v___x_825_ = lean_float_sub(v___x_823_, v___x_824_);
v___x_826_ = lean_float_decLt(v___y_822_, v___x_825_);
v___y_790_ = v___x_826_;
goto v___jp_789_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_740_ = stack[0].m_obj;
uint8_t v_collapsed_741_ = stack[1].m_num;
lean_object* v_tag_742_ = stack[2].m_obj;
lean_object* v_opts_743_ = stack[3].m_obj;
uint8_t v_clsEnabled_744_ = stack[4].m_num;
lean_object* v_oldTraces_745_ = stack[5].m_obj;
lean_object* v_msg_746_ = stack[6].m_obj;
lean_object* v_resStartStop_747_ = stack[7].m_obj;
lean_object* v___y_748_ = stack[8].m_obj;
lean_object* v___y_749_ = stack[9].m_obj;
lean_object* v___y_750_ = stack[10].m_obj;
lean_object* v___y_751_ = stack[11].m_obj;
lean_object* v_res_837_;
v_res_837_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v_cls_740_, v_collapsed_741_, v_tag_742_, v_opts_743_, v_clsEnabled_744_, v_oldTraces_745_, v_msg_746_, v_resStartStop_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
stack->m_obj
 = v_res_837_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___boxed(lean_object* v_cls_838_, lean_object* v_collapsed_839_, lean_object* v_tag_840_, lean_object* v_opts_841_, lean_object* v_clsEnabled_842_, lean_object* v_oldTraces_843_, lean_object* v_msg_844_, lean_object* v_resStartStop_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
uint8_t v_collapsed_boxed_851_; uint8_t v_clsEnabled_boxed_852_; lean_object* v_res_853_; 
v_collapsed_boxed_851_ = lean_unbox(v_collapsed_839_);
v_clsEnabled_boxed_852_ = lean_unbox(v_clsEnabled_842_);
v_res_853_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v_cls_838_, v_collapsed_boxed_851_, v_tag_840_, v_opts_841_, v_clsEnabled_boxed_852_, v_oldTraces_843_, v_msg_844_, v_resStartStop_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec_ref(v_opts_841_);
return v_res_853_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9(void){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_867_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5));
v___x_868_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__8));
v___x_869_ = l_Lean_Name_append(v___x_868_, v___x_867_);
return v___x_869_;
}
}
static double _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10(void){
_start:
{
lean_object* v___x_870_; double v___x_871_; 
v___x_870_ = lean_unsigned_to_nat(1000000000u);
v___x_871_ = lean_float_of_nat(v___x_870_);
return v___x_871_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__11));
v___x_874_ = l_Lean_stringToMessageData(v___x_873_);
return v___x_874_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__13));
v___x_877_ = l_Lean_stringToMessageData(v___x_876_);
return v___x_877_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7(lean_object* v_snd_878_, lean_object* v_mvarId_879_, lean_object* v_x_880_, lean_object* v_x_881_, lean_object* v_x_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
if (lean_obj_tag(v_x_880_) == 5)
{
lean_object* v_fn_888_; lean_object* v_arg_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v_fn_888_ = lean_ctor_get(v_x_880_, 0);
lean_inc_ref(v_fn_888_);
v_arg_889_ = lean_ctor_get(v_x_880_, 1);
lean_inc_ref(v_arg_889_);
lean_dec_ref_known(v_x_880_, 2);
v___x_890_ = lean_array_set(v_x_881_, v_x_882_, v_arg_889_);
v___x_891_ = lean_unsigned_to_nat(1u);
v___x_892_ = lean_nat_sub(v_x_882_, v___x_891_);
lean_dec(v_x_882_);
v_x_880_ = v_fn_888_;
v_x_881_ = v___x_890_;
v_x_882_ = v___x_892_;
goto _start;
}
else
{
lean_dec(v_x_882_);
if (lean_obj_tag(v_x_880_) == 4)
{
lean_object* v_declName_894_; lean_object* v___f_895_; lean_object* v___f_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v_declName_894_ = lean_ctor_get(v_x_880_, 0);
lean_inc_n(v_declName_894_, 2);
lean_dec_ref_known(v_x_880_, 2);
v___f_895_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0));
v___f_896_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1));
v___x_897_ = l_Lean_instInhabitedExpr;
v___x_898_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_declName_894_, v___y_886_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v_a_899_; 
v_a_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_a_899_);
lean_dec_ref_known(v___x_898_, 1);
if (lean_obj_tag(v_a_899_) == 1)
{
lean_object* v_val_900_; lean_object* v_toCold_901_; lean_object* v_options_902_; lean_object* v_majorPos_903_; lean_object* v_arity_904_; lean_object* v_insterestingCtors_905_; lean_object* v_inheritedTraceOptions_906_; uint8_t v_hasTrace_907_; lean_object* v___f_908_; lean_object* v___x_909_; uint8_t v___x_910_; 
v_val_900_ = lean_ctor_get(v_a_899_, 0);
lean_inc(v_val_900_);
lean_dec_ref_known(v_a_899_, 1);
v_toCold_901_ = lean_ctor_get(v___y_885_, 0);
v_options_902_ = lean_ctor_get(v_toCold_901_, 2);
v_majorPos_903_ = lean_ctor_get(v_val_900_, 1);
lean_inc(v_majorPos_903_);
v_arity_904_ = lean_ctor_get(v_val_900_, 2);
lean_inc_n(v_arity_904_, 2);
v_insterestingCtors_905_ = lean_ctor_get(v_val_900_, 3);
lean_inc_ref(v_insterestingCtors_905_);
lean_dec(v_val_900_);
v_inheritedTraceOptions_906_ = lean_ctor_get(v_toCold_901_, 11);
v_hasTrace_907_ = lean_ctor_get_uint8(v_options_902_, sizeof(void*)*1);
lean_inc_ref(v_x_881_);
v___f_908_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___boxed), 15, 9);
lean_closure_set(v___f_908_, 0, v___x_897_);
lean_closure_set(v___f_908_, 1, v_x_881_);
lean_closure_set(v___f_908_, 2, v_majorPos_903_);
lean_closure_set(v___f_908_, 3, v_insterestingCtors_905_);
lean_closure_set(v___f_908_, 4, v_declName_894_);
lean_closure_set(v___f_908_, 5, v_snd_878_);
lean_closure_set(v___f_908_, 6, v_arity_904_);
lean_closure_set(v___f_908_, 7, v_mvarId_879_);
lean_closure_set(v___f_908_, 8, v___f_895_);
v___x_909_ = lean_array_get_size(v_x_881_);
lean_dec_ref(v_x_881_);
v___x_910_ = lean_nat_dec_lt(v___x_909_, v_arity_904_);
lean_dec(v_arity_904_);
if (v_hasTrace_907_ == 0)
{
lean_object* v___x_911_; 
v___x_911_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2(v___x_910_, v___f_908_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
return v___x_911_;
}
else
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; uint8_t v___x_915_; lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v_a_919_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v_a_934_; 
v___x_912_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5));
v___x_913_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__6));
v___x_914_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9);
v___x_915_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_906_, v_options_902_, v___x_914_);
if (v___x_915_ == 0)
{
lean_object* v___x_984_; uint8_t v___x_985_; 
v___x_984_ = l_Lean_trace_profiler;
v___x_985_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_options_902_, v___x_984_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; 
v___x_986_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2(v___x_910_, v___f_908_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
return v___x_986_;
}
else
{
goto v___jp_943_;
}
}
else
{
goto v___jp_943_;
}
v___jp_916_:
{
lean_object* v___x_920_; double v___x_921_; double v___x_922_; double v___x_923_; double v___x_924_; double v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_920_ = lean_io_mono_nanos_now();
v___x_921_ = lean_float_of_nat(v___y_917_);
v___x_922_ = lean_float_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10);
v___x_923_ = lean_float_div(v___x_921_, v___x_922_);
v___x_924_ = lean_float_of_nat(v___x_920_);
v___x_925_ = lean_float_div(v___x_924_, v___x_922_);
v___x_926_ = lean_box_float(v___x_923_);
v___x_927_ = lean_box_float(v___x_925_);
v___x_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_926_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v___x_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_929_, 0, v_a_919_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_930_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_912_, v_hasTrace_907_, v___x_913_, v_options_902_, v___x_915_, v___y_918_, v___f_896_, v___x_929_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
return v___x_930_;
}
v___jp_931_:
{
lean_object* v___x_935_; double v___x_936_; double v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_935_ = lean_io_get_num_heartbeats();
v___x_936_ = lean_float_of_nat(v___y_933_);
v___x_937_ = lean_float_of_nat(v___x_935_);
v___x_938_ = lean_box_float(v___x_936_);
v___x_939_ = lean_box_float(v___x_937_);
v___x_940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_938_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
v___x_941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_941_, 0, v_a_934_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_912_, v_hasTrace_907_, v___x_913_, v_options_902_, v___x_915_, v___y_932_, v___f_896_, v___x_941_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
return v___x_942_;
}
v___jp_943_:
{
lean_object* v___x_944_; lean_object* v_a_945_; lean_object* v___x_946_; uint8_t v___x_947_; 
v___x_944_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___y_886_);
v_a_945_ = lean_ctor_get(v___x_944_, 0);
lean_inc(v_a_945_);
lean_dec_ref(v___x_944_);
v___x_946_ = l_Lean_trace_profiler_useHeartbeats;
v___x_947_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_options_902_, v___x_946_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = lean_io_mono_nanos_now();
v___x_949_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2(v___x_910_, v___f_908_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
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
v___y_917_ = v___x_948_;
v___y_918_ = v_a_945_;
v_a_919_ = v___x_955_;
goto v___jp_916_;
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
v___y_917_ = v___x_948_;
v___y_918_ = v_a_945_;
v_a_919_ = v___x_963_;
goto v___jp_916_;
}
}
}
}
else
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = lean_io_get_num_heartbeats();
v___x_967_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2(v___x_910_, v___f_908_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_975_ == 0)
{
v___x_970_ = v___x_967_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_967_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
lean_ctor_set_tag(v___x_970_, 1);
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_968_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
v___y_932_ = v_a_945_;
v___y_933_ = v___x_966_;
v_a_934_ = v___x_973_;
goto v___jp_931_;
}
}
}
else
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
v_a_976_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v___x_967_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_967_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set_tag(v___x_978_, 0);
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_976_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
v___y_932_ = v_a_945_;
v___y_933_ = v___x_966_;
v_a_934_ = v___x_981_;
goto v___jp_931_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_987_; lean_object* v___x_988_; 
lean_dec(v_a_899_);
lean_dec(v_declName_894_);
lean_dec_ref(v_x_881_);
lean_dec(v_mvarId_879_);
lean_dec_ref(v_snd_878_);
v___x_987_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12);
v___x_988_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_987_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
return v___x_988_;
}
}
else
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
lean_dec(v_declName_894_);
lean_dec_ref(v_x_881_);
lean_dec(v_mvarId_879_);
lean_dec_ref(v_snd_878_);
v_a_989_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_898_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_898_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
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
return v___x_994_;
}
}
}
}
else
{
lean_object* v___x_997_; lean_object* v___x_998_; 
lean_dec_ref(v_x_881_);
lean_dec_ref(v_x_880_);
lean_dec(v_mvarId_879_);
lean_dec_ref(v_snd_878_);
v___x_997_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14);
v___x_998_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_997_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
return v___x_998_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_878_ = stack[0].m_obj;
lean_object* v_mvarId_879_ = stack[1].m_obj;
lean_object* v_x_880_ = stack[2].m_obj;
lean_object* v_x_881_ = stack[3].m_obj;
lean_object* v_x_882_ = stack[4].m_obj;
lean_object* v___y_883_ = stack[5].m_obj;
lean_object* v___y_884_ = stack[6].m_obj;
lean_object* v___y_885_ = stack[7].m_obj;
lean_object* v___y_886_ = stack[8].m_obj;
lean_object* v_res_999_;
v_res_999_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7(v_snd_878_, v_mvarId_879_, v_x_880_, v_x_881_, v_x_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
stack->m_obj
 = v_res_999_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___boxed(lean_object* v_snd_1000_, lean_object* v_mvarId_1001_, lean_object* v_x_1002_, lean_object* v_x_1003_, lean_object* v_x_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7(v_snd_1000_, v_mvarId_1001_, v_x_1002_, v_x_1003_, v_x_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
return v_res_1010_;
}
}
static lean_object* _init_l_Lean_Meta_reduceSparseCasesOn___closed__1(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = ((lean_object*)(l_Lean_Meta_reduceSparseCasesOn___closed__0));
v___x_1013_ = l_Lean_stringToMessageData(v___x_1012_);
return v___x_1013_;
}
}
lean_object* l_Lean_Meta_reduceSparseCasesOn(lean_object* v_mvarId_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v___x_1020_; 
lean_inc(v_mvarId_1014_);
v___x_1020_ = l_Lean_MVarId_getType(v_mvarId_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1022_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
lean_dec_ref_known(v___x_1020_, 1);
v___x_1022_ = l_Lean_Meta_matchEqHEqLHS_x3f(v_a_1021_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_a_1023_);
lean_dec_ref_known(v___x_1022_, 1);
if (lean_obj_tag(v_a_1023_) == 1)
{
lean_object* v_val_1024_; lean_object* v_snd_1025_; lean_object* v_dummy_1026_; lean_object* v_nargs_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v_val_1024_ = lean_ctor_get(v_a_1023_, 0);
lean_inc(v_val_1024_);
lean_dec_ref_known(v_a_1023_, 1);
v_snd_1025_ = lean_ctor_get(v_val_1024_, 1);
lean_inc_n(v_snd_1025_, 2);
lean_dec(v_val_1024_);
v_dummy_1026_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0);
v_nargs_1027_ = l_Lean_Expr_getAppNumArgs(v_snd_1025_);
lean_inc(v_nargs_1027_);
v___x_1028_ = lean_mk_array(v_nargs_1027_, v_dummy_1026_);
v___x_1029_ = lean_unsigned_to_nat(1u);
v___x_1030_ = lean_nat_sub(v_nargs_1027_, v___x_1029_);
lean_dec(v_nargs_1027_);
v___x_1031_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7(v_snd_1025_, v_mvarId_1014_, v_snd_1025_, v___x_1028_, v___x_1030_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
return v___x_1031_;
}
else
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
lean_dec(v_a_1023_);
lean_dec(v_mvarId_1014_);
v___x_1032_ = lean_obj_once(&l_Lean_Meta_reduceSparseCasesOn___closed__1, &l_Lean_Meta_reduceSparseCasesOn___closed__1_once, _init_l_Lean_Meta_reduceSparseCasesOn___closed__1);
v___x_1033_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1032_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
return v___x_1033_;
}
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_dec(v_mvarId_1014_);
v_a_1034_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_1022_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1022_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec(v_mvarId_1014_);
v_a_1042_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1020_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1020_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_reduceSparseCasesOn_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1014_ = stack[0].m_obj;
lean_object* v_a_1015_ = stack[1].m_obj;
lean_object* v_a_1016_ = stack[2].m_obj;
lean_object* v_a_1017_ = stack[3].m_obj;
lean_object* v_a_1018_ = stack[4].m_obj;
lean_object* v_res_1050_;
v_res_1050_ = l_Lean_Meta_reduceSparseCasesOn(v_mvarId_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
stack->m_obj
 = v_res_1050_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceSparseCasesOn___boxed(lean_object* v_mvarId_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_Lean_Meta_reduceSparseCasesOn(v_mvarId_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
return v_res_1057_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3(lean_object* v_00_u03b1_1058_, lean_object* v_msg_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v_msg_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
return v___x_1065_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1059_ = stack[1].m_obj;
lean_object* v___y_1060_ = stack[2].m_obj;
lean_object* v___y_1061_ = stack[3].m_obj;
lean_object* v___y_1062_ = stack[4].m_obj;
lean_object* v___y_1063_ = stack[5].m_obj;
lean_object* v_res_1066_;
v_res_1066_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3(lean_box(0), v_msg_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
stack->m_obj
 = v_res_1066_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___boxed(lean_object* v_00_u03b1_1067_, lean_object* v_msg_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3(v_00_u03b1_1067_, v_msg_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
return v_res_1074_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10(lean_object* v_00_u03b1_1075_, lean_object* v_x_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg(v_x_1076_);
return v___x_1082_;
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1076_ = stack[1].m_obj;
lean_object* v___y_1077_ = stack[2].m_obj;
lean_object* v___y_1078_ = stack[3].m_obj;
lean_object* v___y_1079_ = stack[4].m_obj;
lean_object* v___y_1080_ = stack[5].m_obj;
lean_object* v_res_1083_;
v_res_1083_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10(lean_box(0), v_x_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
stack->m_obj
 = v_res_1083_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___boxed(lean_object* v_00_u03b1_1084_, lean_object* v_x_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10(v_00_u03b1_1084_, v_x_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
return v_res_1091_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(lean_object* v_mvarId_1092_, lean_object* v_x_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1092_, v_x_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1099_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1099_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
v_a_1108_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1099_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1099_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1092_ = stack[0].m_obj;
lean_object* v_x_1093_ = stack[1].m_obj;
lean_object* v___y_1094_ = stack[2].m_obj;
lean_object* v___y_1095_ = stack[3].m_obj;
lean_object* v___y_1096_ = stack[4].m_obj;
lean_object* v___y_1097_ = stack[5].m_obj;
lean_object* v_res_1116_;
v_res_1116_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1092_, v_x_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
stack->m_obj
 = v_res_1116_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg___boxed(lean_object* v_mvarId_1117_, lean_object* v_x_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1117_, v_x_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
return v_res_1124_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2(lean_object* v_00_u03b1_1125_, lean_object* v_mvarId_1126_, lean_object* v_x_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1126_, v_x_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
return v___x_1133_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1126_ = stack[1].m_obj;
lean_object* v_x_1127_ = stack[2].m_obj;
lean_object* v___y_1128_ = stack[3].m_obj;
lean_object* v___y_1129_ = stack[4].m_obj;
lean_object* v___y_1130_ = stack[5].m_obj;
lean_object* v___y_1131_ = stack[6].m_obj;
lean_object* v_res_1134_;
v_res_1134_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2(lean_box(0), v_mvarId_1126_, v_x_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
stack->m_obj
 = v_res_1134_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___boxed(lean_object* v_00_u03b1_1135_, lean_object* v_mvarId_1136_, lean_object* v_x_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2(v_00_u03b1_1135_, v_mvarId_1136_, v_x_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_splitSparseCasesOn_spec__1(lean_object* v_a_1144_, lean_object* v_a_1145_){
_start:
{
if (lean_obj_tag(v_a_1144_) == 0)
{
lean_object* v___x_1146_; 
v___x_1146_ = l_List_reverse___redArg(v_a_1145_);
return v___x_1146_;
}
else
{
lean_object* v_head_1147_; lean_object* v_tail_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1157_; 
v_head_1147_ = lean_ctor_get(v_a_1144_, 0);
v_tail_1148_ = lean_ctor_get(v_a_1144_, 1);
v_isSharedCheck_1157_ = !lean_is_exclusive(v_a_1144_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1150_ = v_a_1144_;
v_isShared_1151_ = v_isSharedCheck_1157_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_tail_1148_);
lean_inc(v_head_1147_);
lean_dec(v_a_1144_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1157_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1152_; lean_object* v___x_1154_; 
v___x_1152_ = l_Lean_MessageData_ofExpr(v_head_1147_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 1, v_a_1145_);
lean_ctor_set(v___x_1150_, 0, v___x_1152_);
v___x_1154_ = v___x_1150_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1152_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v_a_1145_);
v___x_1154_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
v_a_1144_ = v_tail_1148_;
v_a_1145_ = v___x_1154_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__0));
v___x_1160_ = l_Lean_stringToMessageData(v___x_1159_);
return v___x_1160_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0(uint8_t v___y_1161_, lean_object* v_mvarId_1162_, lean_object* v___f_1163_, lean_object* v_declName_1164_, lean_object* v_val_1165_, lean_object* v___x_1166_, lean_object* v_fields_1167_, uint8_t v___x_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v___y_1177_; lean_object* v___y_1178_; 
if (v___y_1161_ == 0)
{
lean_object* v___x_1230_; 
lean_dec_ref(v_fields_1167_);
lean_dec_ref(v_val_1165_);
lean_dec(v_declName_1164_);
v___x_1230_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_1162_, v___f_1163_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
return v___x_1230_;
}
else
{
lean_object* v___x_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; 
lean_dec_ref(v___f_1163_);
v___x_1231_ = lean_array_get_size(v_fields_1167_);
v___x_1232_ = lean_unsigned_to_nat(1u);
v___x_1233_ = lean_nat_dec_eq(v___x_1231_, v___x_1232_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1234_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1);
lean_inc_ref(v_fields_1167_);
v___x_1235_ = lean_array_to_list(v_fields_1167_);
v___x_1236_ = lean_box(0);
v___x_1237_ = l_List_mapTR_loop___at___00Lean_Meta_splitSparseCasesOn_spec__1(v___x_1235_, v___x_1236_);
v___x_1238_ = l_Lean_MessageData_ofList(v___x_1237_);
v___x_1239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1234_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
v___x_1240_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1239_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_dec_ref_known(v___x_1240_, 1);
v___y_1175_ = v___y_1169_;
v___y_1176_ = v___y_1170_;
v___y_1177_ = v___y_1171_;
v___y_1178_ = v___y_1172_;
goto v___jp_1174_;
}
else
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
lean_dec_ref(v_fields_1167_);
lean_dec_ref(v_val_1165_);
lean_dec(v_declName_1164_);
lean_dec(v_mvarId_1162_);
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1240_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1240_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
else
{
v___y_1175_ = v___y_1169_;
v___y_1176_ = v___y_1170_;
v___y_1177_ = v___y_1171_;
v___y_1178_ = v___y_1172_;
goto v___jp_1174_;
}
}
v___jp_1174_:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_Lean_Meta_getSparseCasesOnEq(v_declName_1164_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v_a_1180_; lean_object* v___x_1181_; 
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
lean_inc(v_a_1180_);
lean_dec_ref_known(v___x_1179_, 1);
lean_inc(v_mvarId_1162_);
v___x_1181_ = l_Lean_MVarId_getType(v_mvarId_1162_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1183_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_a_1182_);
lean_dec_ref_known(v___x_1181_, 1);
v___x_1183_ = l_Lean_Meta_matchEqHEqLHS_x3f(v_a_1182_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_a_1184_);
lean_dec_ref_known(v___x_1183_, 1);
if (lean_obj_tag(v_a_1184_) == 1)
{
lean_object* v_val_1185_; lean_object* v_snd_1186_; lean_object* v_arity_1187_; lean_object* v___x_1188_; lean_object* v_nargs_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v_dummy_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v_val_1185_ = lean_ctor_get(v_a_1184_, 0);
lean_inc(v_val_1185_);
lean_dec_ref_known(v_a_1184_, 1);
v_snd_1186_ = lean_ctor_get(v_val_1185_, 1);
lean_inc(v_snd_1186_);
lean_dec(v_val_1185_);
v_arity_1187_ = lean_ctor_get(v_val_1165_, 2);
lean_inc(v_arity_1187_);
lean_dec_ref(v_val_1165_);
v___x_1188_ = l_Lean_Expr_getAppFn(v_snd_1186_);
v_nargs_1189_ = l_Lean_Expr_getAppNumArgs(v_snd_1186_);
v___x_1190_ = l_Lean_Expr_constLevels_x21(v___x_1188_);
lean_dec_ref(v___x_1188_);
v___x_1191_ = l_Lean_mkConst(v_a_1180_, v___x_1190_);
v_dummy_1192_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0);
lean_inc(v_nargs_1189_);
v___x_1193_ = lean_mk_array(v_nargs_1189_, v_dummy_1192_);
v___x_1194_ = lean_unsigned_to_nat(1u);
v___x_1195_ = lean_nat_sub(v_nargs_1189_, v___x_1194_);
lean_dec(v_nargs_1189_);
v___x_1196_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_snd_1186_, v___x_1193_, v___x_1195_);
v___x_1197_ = lean_unsigned_to_nat(0u);
v___x_1198_ = l_Array_toSubarray___redArg(v___x_1196_, v___x_1197_, v_arity_1187_);
v___x_1199_ = l_Subarray_copy___redArg(v___x_1198_);
v___x_1200_ = l_Lean_mkAppN(v___x_1191_, v___x_1199_);
lean_dec_ref(v___x_1199_);
v___x_1201_ = lean_array_get(v___x_1166_, v_fields_1167_, v___x_1197_);
lean_dec_ref(v_fields_1167_);
v___x_1202_ = l_Lean_Expr_app___override(v___x_1200_, v___x_1201_);
v___x_1203_ = l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq(v_mvarId_1162_, v___x_1202_, v___x_1168_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
return v___x_1203_;
}
else
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
lean_dec(v_a_1184_);
lean_dec(v_a_1180_);
lean_dec_ref(v_fields_1167_);
lean_dec_ref(v_val_1165_);
lean_dec(v_mvarId_1162_);
v___x_1204_ = lean_obj_once(&l_Lean_Meta_reduceSparseCasesOn___closed__1, &l_Lean_Meta_reduceSparseCasesOn___closed__1_once, _init_l_Lean_Meta_reduceSparseCasesOn___closed__1);
v___x_1205_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1204_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
return v___x_1205_;
}
}
else
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
lean_dec(v_a_1180_);
lean_dec_ref(v_fields_1167_);
lean_dec_ref(v_val_1165_);
lean_dec(v_mvarId_1162_);
v_a_1206_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1183_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1183_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
else
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
lean_dec(v_a_1180_);
lean_dec_ref(v_fields_1167_);
lean_dec_ref(v_val_1165_);
lean_dec(v_mvarId_1162_);
v_a_1214_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1181_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1181_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
else
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
lean_dec_ref(v_fields_1167_);
lean_dec_ref(v_val_1165_);
lean_dec(v_mvarId_1162_);
v_a_1222_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1224_ = v___x_1179_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1179_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_a_1222_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_1161_ = stack[0].m_num;
lean_object* v_mvarId_1162_ = stack[1].m_obj;
lean_object* v___f_1163_ = stack[2].m_obj;
lean_object* v_declName_1164_ = stack[3].m_obj;
lean_object* v_val_1165_ = stack[4].m_obj;
lean_object* v___x_1166_ = stack[5].m_obj;
lean_object* v_fields_1167_ = stack[6].m_obj;
uint8_t v___x_1168_ = stack[7].m_num;
lean_object* v___y_1169_ = stack[8].m_obj;
lean_object* v___y_1170_ = stack[9].m_obj;
lean_object* v___y_1171_ = stack[10].m_obj;
lean_object* v___y_1172_ = stack[11].m_obj;
lean_object* v_res_1249_;
v_res_1249_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0(v___y_1161_, v_mvarId_1162_, v___f_1163_, v_declName_1164_, v_val_1165_, v___x_1166_, v_fields_1167_, v___x_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
stack->m_obj
 = v_res_1249_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed(lean_object* v___y_1250_, lean_object* v_mvarId_1251_, lean_object* v___f_1252_, lean_object* v_declName_1253_, lean_object* v_val_1254_, lean_object* v___x_1255_, lean_object* v_fields_1256_, lean_object* v___x_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
uint8_t v___y_31469__boxed_1263_; uint8_t v___x_31474__boxed_1264_; lean_object* v_res_1265_; 
v___y_31469__boxed_1263_ = lean_unbox(v___y_1250_);
v___x_31474__boxed_1264_ = lean_unbox(v___x_1257_);
v_res_1265_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0(v___y_31469__boxed_1263_, v_mvarId_1251_, v___f_1252_, v_declName_1253_, v_val_1254_, v___x_1255_, v_fields_1256_, v___x_31474__boxed_1264_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec_ref(v___x_1255_);
return v_res_1265_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(lean_object* v_declName_1266_, lean_object* v_val_1267_, uint8_t v___x_1268_, size_t v_sz_1269_, size_t v_i_1270_, lean_object* v_bs_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
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
lean_dec_ref_known(v_ctorName_1281_, 1);
v___y_1289_ = v___x_1268_;
goto v___jp_1288_;
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
lean_dec_ref_known(v___x_1293_, 1);
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1266_ = stack[0].m_obj;
lean_object* v_val_1267_ = stack[1].m_obj;
uint8_t v___x_1268_ = stack[2].m_num;
size_t v_sz_1269_ = stack[3].m_num;
size_t v_i_1270_ = stack[4].m_num;
lean_object* v_bs_1271_ = stack[5].m_obj;
lean_object* v___y_1272_ = stack[6].m_obj;
lean_object* v___y_1273_ = stack[7].m_obj;
lean_object* v___y_1274_ = stack[8].m_obj;
lean_object* v___y_1275_ = stack[9].m_obj;
lean_object* v_res_1307_;
v_res_1307_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(v_declName_1266_, v_val_1267_, v___x_1268_, v_sz_1269_, v_i_1270_, v_bs_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
stack->m_obj
 = v_res_1307_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___boxed(lean_object* v_declName_1308_, lean_object* v_val_1309_, lean_object* v___x_1310_, lean_object* v_sz_1311_, lean_object* v_i_1312_, lean_object* v_bs_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
uint8_t v___x_31750__boxed_1319_; size_t v_sz_boxed_1320_; size_t v_i_boxed_1321_; lean_object* v_res_1322_; 
v___x_31750__boxed_1319_ = lean_unbox(v___x_1310_);
v_sz_boxed_1320_ = lean_unbox_usize(v_sz_1311_);
lean_dec(v_sz_1311_);
v_i_boxed_1321_ = lean_unbox_usize(v_i_1312_);
lean_dec(v_i_1312_);
v_res_1322_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(v_declName_1308_, v_val_1309_, v___x_31750__boxed_1319_, v_sz_boxed_1320_, v_i_boxed_1321_, v_bs_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
return v_res_1322_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(lean_object* v___x_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v_toCold_1329_; lean_object* v_options_1330_; uint8_t v_hasTrace_1331_; 
v_toCold_1329_ = lean_ctor_get(v___y_1326_, 0);
v_options_1330_ = lean_ctor_get(v_toCold_1329_, 2);
v_hasTrace_1331_ = lean_ctor_get_uint8(v_options_1330_, sizeof(void*)*1);
if (v_hasTrace_1331_ == 0)
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
lean_dec(v___x_1323_);
v___x_1332_ = lean_box(v_hasTrace_1331_);
v___x_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
return v___x_1333_;
}
else
{
lean_object* v_inheritedTraceOptions_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; uint8_t v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v_inheritedTraceOptions_1334_ = lean_ctor_get(v_toCold_1329_, 11);
v___x_1335_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__8));
v___x_1336_ = l_Lean_Name_append(v___x_1335_, v___x_1323_);
v___x_1337_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1334_, v_options_1330_, v___x_1336_);
lean_dec(v___x_1336_);
v___x_1338_ = lean_box(v___x_1337_);
v___x_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1338_);
return v___x_1339_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1323_ = stack[0].m_obj;
lean_object* v___y_1324_ = stack[1].m_obj;
lean_object* v___y_1325_ = stack[2].m_obj;
lean_object* v___y_1326_ = stack[3].m_obj;
lean_object* v___y_1327_ = stack[4].m_obj;
lean_object* v_res_1340_;
v_res_1340_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(v___x_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
stack->m_obj
 = v_res_1340_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___boxed(lean_object* v___x_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(v___x_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
return v_res_1347_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(lean_object* v_cls_1350_, lean_object* v_msg_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v_ref_1357_; lean_object* v___x_1358_; lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1404_; 
v_ref_1357_ = lean_ctor_get(v___y_1354_, 2);
v___x_1358_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msg_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1361_ = v___x_1358_;
v_isShared_1362_ = v_isSharedCheck_1404_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1358_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1404_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1363_; lean_object* v_traceState_1364_; lean_object* v_env_1365_; lean_object* v_nextMacroScope_1366_; lean_object* v_ngen_1367_; lean_object* v_auxDeclNGen_1368_; lean_object* v_cache_1369_; lean_object* v_recordedDeps_1370_; lean_object* v_messages_1371_; lean_object* v_infoState_1372_; lean_object* v_snapshotTasks_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1403_; 
v___x_1363_ = lean_st_ref_take(v___y_1355_);
v_traceState_1364_ = lean_ctor_get(v___x_1363_, 4);
v_env_1365_ = lean_ctor_get(v___x_1363_, 0);
v_nextMacroScope_1366_ = lean_ctor_get(v___x_1363_, 1);
v_ngen_1367_ = lean_ctor_get(v___x_1363_, 2);
v_auxDeclNGen_1368_ = lean_ctor_get(v___x_1363_, 3);
v_cache_1369_ = lean_ctor_get(v___x_1363_, 5);
v_recordedDeps_1370_ = lean_ctor_get(v___x_1363_, 6);
v_messages_1371_ = lean_ctor_get(v___x_1363_, 7);
v_infoState_1372_ = lean_ctor_get(v___x_1363_, 8);
v_snapshotTasks_1373_ = lean_ctor_get(v___x_1363_, 9);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1375_ = v___x_1363_;
v_isShared_1376_ = v_isSharedCheck_1403_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_snapshotTasks_1373_);
lean_inc(v_infoState_1372_);
lean_inc(v_messages_1371_);
lean_inc(v_recordedDeps_1370_);
lean_inc(v_cache_1369_);
lean_inc(v_traceState_1364_);
lean_inc(v_auxDeclNGen_1368_);
lean_inc(v_ngen_1367_);
lean_inc(v_nextMacroScope_1366_);
lean_inc(v_env_1365_);
lean_dec(v___x_1363_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1403_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
uint64_t v_tid_1377_; lean_object* v_traces_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1402_; 
v_tid_1377_ = lean_ctor_get_uint64(v_traceState_1364_, sizeof(void*)*1);
v_traces_1378_ = lean_ctor_get(v_traceState_1364_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v_traceState_1364_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1380_ = v_traceState_1364_;
v_isShared_1381_ = v_isSharedCheck_1402_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_traces_1378_);
lean_dec(v_traceState_1364_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1402_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; double v___x_1384_; uint8_t v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1393_; 
v___x_1382_ = lean_box(0);
v___x_1383_ = lean_box(0);
v___x_1384_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0);
v___x_1385_ = 0;
v___x_1386_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__6));
v___x_1387_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1387_, 0, v_cls_1350_);
lean_ctor_set(v___x_1387_, 1, v___x_1383_);
lean_ctor_set(v___x_1387_, 2, v___x_1386_);
lean_ctor_set_float(v___x_1387_, sizeof(void*)*3, v___x_1384_);
lean_ctor_set_float(v___x_1387_, sizeof(void*)*3 + 8, v___x_1384_);
lean_ctor_set_uint8(v___x_1387_, sizeof(void*)*3 + 16, v___x_1385_);
v___x_1388_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___closed__0));
v___x_1389_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1387_);
lean_ctor_set(v___x_1389_, 1, v_a_1359_);
lean_ctor_set(v___x_1389_, 2, v___x_1388_);
lean_inc(v_ref_1357_);
v___x_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1390_, 0, v_ref_1357_);
lean_ctor_set(v___x_1390_, 1, v___x_1389_);
v___x_1391_ = l_Lean_PersistentArray_push___redArg(v_traces_1378_, v___x_1390_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 0, v___x_1391_);
v___x_1393_ = v___x_1380_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1391_);
lean_ctor_set_uint64(v_reuseFailAlloc_1401_, sizeof(void*)*1, v_tid_1377_);
v___x_1393_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
lean_object* v___x_1395_; 
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 4, v___x_1393_);
v___x_1395_ = v___x_1375_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_env_1365_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v_nextMacroScope_1366_);
lean_ctor_set(v_reuseFailAlloc_1400_, 2, v_ngen_1367_);
lean_ctor_set(v_reuseFailAlloc_1400_, 3, v_auxDeclNGen_1368_);
lean_ctor_set(v_reuseFailAlloc_1400_, 4, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1400_, 5, v_cache_1369_);
lean_ctor_set(v_reuseFailAlloc_1400_, 6, v_recordedDeps_1370_);
lean_ctor_set(v_reuseFailAlloc_1400_, 7, v_messages_1371_);
lean_ctor_set(v_reuseFailAlloc_1400_, 8, v_infoState_1372_);
lean_ctor_set(v_reuseFailAlloc_1400_, 9, v_snapshotTasks_1373_);
v___x_1395_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1396_ = lean_st_ref_put(v___y_1355_, v___x_1395_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 0, v___x_1382_);
v___x_1398_ = v___x_1361_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1382_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1350_ = stack[0].m_obj;
lean_object* v_msg_1351_ = stack[1].m_obj;
lean_object* v___y_1352_ = stack[2].m_obj;
lean_object* v___y_1353_ = stack[3].m_obj;
lean_object* v___y_1354_ = stack[4].m_obj;
lean_object* v___y_1355_ = stack[5].m_obj;
lean_object* v_res_1405_;
v_res_1405_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v_cls_1350_, v_msg_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
stack->m_obj
 = v_res_1405_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___boxed(lean_object* v_cls_1406_, lean_object* v_msg_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v_cls_1406_, v_msg_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
return v_res_1413_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(lean_object* v_declName_1414_, lean_object* v_val_1415_, uint8_t v___x_1416_, size_t v_sz_1417_, size_t v_i_1418_, lean_object* v_bs_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
uint8_t v___x_1425_; 
v___x_1425_ = lean_usize_dec_lt(v_i_1418_, v_sz_1417_);
if (v___x_1425_ == 0)
{
lean_object* v___x_1426_; 
lean_dec_ref(v_val_1415_);
lean_dec(v_declName_1414_);
v___x_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1426_, 0, v_bs_1419_);
return v___x_1426_;
}
else
{
lean_object* v_v_1427_; lean_object* v_toInductionSubgoal_1428_; lean_object* v_ctorName_1429_; lean_object* v_mvarId_1430_; lean_object* v_fields_1431_; lean_object* v___f_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; lean_object* v___x_1435_; lean_object* v_bs_x27_1436_; uint8_t v___y_1438_; 
v_v_1427_ = lean_array_uget_borrowed(v_bs_1419_, v_i_1418_);
v_toInductionSubgoal_1428_ = lean_ctor_get(v_v_1427_, 0);
v_ctorName_1429_ = lean_ctor_get(v_v_1427_, 1);
lean_inc(v_ctorName_1429_);
v_mvarId_1430_ = lean_ctor_get(v_toInductionSubgoal_1428_, 0);
lean_inc(v_mvarId_1430_);
v_fields_1431_ = lean_ctor_get(v_toInductionSubgoal_1428_, 1);
lean_inc_ref(v_fields_1431_);
v___f_1432_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0));
v___x_1433_ = l_Lean_instInhabitedExpr;
v___x_1434_ = 0;
v___x_1435_ = lean_unsigned_to_nat(0u);
v_bs_x27_1436_ = lean_array_uset(v_bs_1419_, v_i_1418_, v___x_1435_);
if (lean_obj_tag(v_ctorName_1429_) == 0)
{
v___y_1438_ = v___x_1416_;
goto v___jp_1437_;
}
else
{
lean_dec_ref_known(v_ctorName_1429_, 1);
v___y_1438_ = v___x_1434_;
goto v___jp_1437_;
}
v___jp_1437_:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___y_1441_; lean_object* v___x_1442_; 
v___x_1439_ = lean_box(v___y_1438_);
v___x_1440_ = lean_box(v___x_1434_);
lean_inc_ref(v_val_1415_);
lean_inc(v_declName_1414_);
lean_inc(v_mvarId_1430_);
v___y_1441_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed), 13, 8);
lean_closure_set(v___y_1441_, 0, v___x_1439_);
lean_closure_set(v___y_1441_, 1, v_mvarId_1430_);
lean_closure_set(v___y_1441_, 2, v___f_1432_);
lean_closure_set(v___y_1441_, 3, v_declName_1414_);
lean_closure_set(v___y_1441_, 4, v_val_1415_);
lean_closure_set(v___y_1441_, 5, v___x_1433_);
lean_closure_set(v___y_1441_, 6, v_fields_1431_);
lean_closure_set(v___y_1441_, 7, v___x_1440_);
v___x_1442_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1430_, v___y_1441_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; size_t v___x_1444_; size_t v___x_1445_; lean_object* v___x_1446_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
lean_inc(v_a_1443_);
lean_dec_ref_known(v___x_1442_, 1);
v___x_1444_ = ((size_t)1ULL);
v___x_1445_ = lean_usize_add(v_i_1418_, v___x_1444_);
v___x_1446_ = lean_array_uset(v_bs_x27_1436_, v_i_1418_, v_a_1443_);
v_i_1418_ = v___x_1445_;
v_bs_1419_ = v___x_1446_;
goto _start;
}
else
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
lean_dec_ref(v_bs_x27_1436_);
lean_dec_ref(v_val_1415_);
lean_dec(v_declName_1414_);
v_a_1448_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1442_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1442_);
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
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1414_ = stack[0].m_obj;
lean_object* v_val_1415_ = stack[1].m_obj;
uint8_t v___x_1416_ = stack[2].m_num;
size_t v_sz_1417_ = stack[3].m_num;
size_t v_i_1418_ = stack[4].m_num;
lean_object* v_bs_1419_ = stack[5].m_obj;
lean_object* v___y_1420_ = stack[6].m_obj;
lean_object* v___y_1421_ = stack[7].m_obj;
lean_object* v___y_1422_ = stack[8].m_obj;
lean_object* v___y_1423_ = stack[9].m_obj;
lean_object* v_res_1456_;
v_res_1456_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(v_declName_1414_, v_val_1415_, v___x_1416_, v_sz_1417_, v_i_1418_, v_bs_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
stack->m_obj
 = v_res_1456_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4___boxed(lean_object* v_declName_1457_, lean_object* v_val_1458_, lean_object* v___x_1459_, lean_object* v_sz_1460_, lean_object* v_i_1461_, lean_object* v_bs_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
uint8_t v___x_32061__boxed_1468_; size_t v_sz_boxed_1469_; size_t v_i_boxed_1470_; lean_object* v_res_1471_; 
v___x_32061__boxed_1468_ = lean_unbox(v___x_1459_);
v_sz_boxed_1469_ = lean_unbox_usize(v_sz_1460_);
lean_dec(v_sz_1460_);
v_i_boxed_1470_ = lean_unbox_usize(v_i_1461_);
lean_dec(v_i_1461_);
v_res_1471_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(v_declName_1457_, v_val_1458_, v___x_32061__boxed_1468_, v_sz_boxed_1469_, v_i_boxed_1470_, v_bs_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
return v_res_1471_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1475_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__1));
v___x_1476_ = l_Lean_stringToMessageData(v___x_1475_);
return v___x_1476_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(lean_object* v_val_1477_, lean_object* v___x_1478_, lean_object* v_x_1479_, lean_object* v_mvarId_1480_, lean_object* v_declName_1481_, uint8_t v___x_1482_, lean_object* v_____r_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v_majorPos_1514_; lean_object* v_arity_1515_; lean_object* v_insterestingCtors_1516_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___x_1536_; uint8_t v___x_1537_; 
v_majorPos_1514_ = lean_ctor_get(v_val_1477_, 1);
v_arity_1515_ = lean_ctor_get(v_val_1477_, 2);
v_insterestingCtors_1516_ = lean_ctor_get(v_val_1477_, 3);
v___x_1536_ = lean_array_get_size(v_x_1479_);
v___x_1537_ = lean_nat_dec_lt(v___x_1536_, v_arity_1515_);
if (v___x_1537_ == 0)
{
v___y_1518_ = v___y_1484_;
v___y_1519_ = v___y_1485_;
v___y_1520_ = v___y_1486_;
v___y_1521_ = v___y_1487_;
goto v___jp_1517_;
}
else
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1547_; 
lean_dec(v_declName_1481_);
lean_dec(v_mvarId_1480_);
lean_dec_ref(v_val_1477_);
v___x_1538_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1);
v___x_1539_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1538_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1542_ = v___x_1539_;
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1539_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1545_; 
if (v_isShared_1543_ == 0)
{
v___x_1545_ = v___x_1542_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_a_1540_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
v___jp_1489_:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; uint8_t v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1496_ = lean_array_get_borrowed(v___x_1478_, v_x_1479_, v___y_1490_);
lean_dec(v___y_1490_);
v___x_1497_ = l_Lean_Expr_fvarId_x21(v___x_1496_);
v___x_1498_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__0));
v___x_1499_ = 0;
v___x_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1500_, 0, v___y_1491_);
v___x_1501_ = l_Lean_MVarId_cases(v_mvarId_1480_, v___x_1497_, v___x_1498_, v___x_1499_, v___x_1500_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v_a_1502_; size_t v_sz_1503_; size_t v___x_1504_; lean_object* v___x_1505_; 
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
lean_inc(v_a_1502_);
lean_dec_ref_known(v___x_1501_, 1);
v_sz_1503_ = lean_array_size(v_a_1502_);
v___x_1504_ = ((size_t)0ULL);
v___x_1505_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(v_declName_1481_, v_val_1477_, v___x_1482_, v_sz_1503_, v___x_1504_, v_a_1502_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
return v___x_1505_;
}
else
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
lean_dec(v_declName_1481_);
lean_dec_ref(v_val_1477_);
v_a_1506_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1508_ = v___x_1501_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1501_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1509_ == 0)
{
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1506_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
v___jp_1517_:
{
lean_object* v___x_1522_; uint8_t v___x_1523_; 
v___x_1522_ = lean_array_get_borrowed(v___x_1478_, v_x_1479_, v_majorPos_1514_);
v___x_1523_ = l_Lean_Expr_isFVar(v___x_1522_);
if (v___x_1523_ == 0)
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
lean_dec(v_declName_1481_);
lean_dec(v_mvarId_1480_);
lean_dec_ref(v_val_1477_);
v___x_1524_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__2);
lean_inc(v___x_1522_);
v___x_1525_ = l_Lean_indentExpr(v___x_1522_);
v___x_1526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1524_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
v___x_1527_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1526_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___x_1527_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1527_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_a_1528_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
else
{
lean_inc_ref(v_insterestingCtors_1516_);
lean_inc(v_majorPos_1514_);
v___y_1490_ = v_majorPos_1514_;
v___y_1491_ = v_insterestingCtors_1516_;
v___y_1492_ = v___y_1518_;
v___y_1493_ = v___y_1519_;
v___y_1494_ = v___y_1520_;
v___y_1495_ = v___y_1521_;
goto v___jp_1489_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1477_ = stack[0].m_obj;
lean_object* v___x_1478_ = stack[1].m_obj;
lean_object* v_x_1479_ = stack[2].m_obj;
lean_object* v_mvarId_1480_ = stack[3].m_obj;
lean_object* v_declName_1481_ = stack[4].m_obj;
uint8_t v___x_1482_ = stack[5].m_num;
lean_object* v_____r_1483_ = stack[6].m_obj;
lean_object* v___y_1484_ = stack[7].m_obj;
lean_object* v___y_1485_ = stack[8].m_obj;
lean_object* v___y_1486_ = stack[9].m_obj;
lean_object* v___y_1487_ = stack[10].m_obj;
lean_object* v_res_1548_;
v_res_1548_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(v_val_1477_, v___x_1478_, v_x_1479_, v_mvarId_1480_, v_declName_1481_, v___x_1482_, v_____r_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
stack->m_obj
 = v_res_1548_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___boxed(lean_object* v_val_1549_, lean_object* v___x_1550_, lean_object* v_x_1551_, lean_object* v_mvarId_1552_, lean_object* v_declName_1553_, lean_object* v___x_1554_, lean_object* v_____r_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
uint8_t v___x_32192__boxed_1561_; lean_object* v_res_1562_; 
v___x_32192__boxed_1561_ = lean_unbox(v___x_1554_);
v_res_1562_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(v_val_1549_, v___x_1550_, v_x_1551_, v_mvarId_1552_, v_declName_1553_, v___x_32192__boxed_1561_, v_____r_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec_ref(v_x_1551_);
lean_dec_ref(v___x_1550_);
return v_res_1562_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5(lean_object* v_declName_1563_, lean_object* v_val_1564_, uint8_t v___x_1565_, uint8_t v___x_1566_, size_t v_sz_1567_, size_t v_i_1568_, lean_object* v_bs_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
uint8_t v___x_1575_; 
v___x_1575_ = lean_usize_dec_lt(v_i_1568_, v_sz_1567_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1576_; 
lean_dec_ref(v_val_1564_);
lean_dec(v_declName_1563_);
v___x_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1576_, 0, v_bs_1569_);
return v___x_1576_;
}
else
{
lean_object* v_v_1577_; lean_object* v_toInductionSubgoal_1578_; lean_object* v_ctorName_1579_; lean_object* v_mvarId_1580_; lean_object* v_fields_1581_; lean_object* v___f_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v_bs_x27_1585_; uint8_t v___y_1587_; 
v_v_1577_ = lean_array_uget_borrowed(v_bs_1569_, v_i_1568_);
v_toInductionSubgoal_1578_ = lean_ctor_get(v_v_1577_, 0);
v_ctorName_1579_ = lean_ctor_get(v_v_1577_, 1);
lean_inc(v_ctorName_1579_);
v_mvarId_1580_ = lean_ctor_get(v_toInductionSubgoal_1578_, 0);
lean_inc(v_mvarId_1580_);
v_fields_1581_ = lean_ctor_get(v_toInductionSubgoal_1578_, 1);
lean_inc_ref(v_fields_1581_);
v___f_1582_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0));
v___x_1583_ = l_Lean_instInhabitedExpr;
v___x_1584_ = lean_unsigned_to_nat(0u);
v_bs_x27_1585_ = lean_array_uset(v_bs_1569_, v_i_1568_, v___x_1584_);
if (lean_obj_tag(v_ctorName_1579_) == 0)
{
v___y_1587_ = v___x_1566_;
goto v___jp_1586_;
}
else
{
lean_dec_ref_known(v_ctorName_1579_, 1);
v___y_1587_ = v___x_1565_;
goto v___jp_1586_;
}
v___jp_1586_:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___y_1590_; lean_object* v___x_1591_; 
v___x_1588_ = lean_box(v___y_1587_);
v___x_1589_ = lean_box(v___x_1565_);
lean_inc_ref(v_val_1564_);
lean_inc(v_declName_1563_);
lean_inc(v_mvarId_1580_);
v___y_1590_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed), 13, 8);
lean_closure_set(v___y_1590_, 0, v___x_1588_);
lean_closure_set(v___y_1590_, 1, v_mvarId_1580_);
lean_closure_set(v___y_1590_, 2, v___f_1582_);
lean_closure_set(v___y_1590_, 3, v_declName_1563_);
lean_closure_set(v___y_1590_, 4, v_val_1564_);
lean_closure_set(v___y_1590_, 5, v___x_1583_);
lean_closure_set(v___y_1590_, 6, v_fields_1581_);
lean_closure_set(v___y_1590_, 7, v___x_1589_);
v___x_1591_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1580_, v___y_1590_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_a_1592_; size_t v___x_1593_; size_t v___x_1594_; lean_object* v___x_1595_; 
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_a_1592_);
lean_dec_ref_known(v___x_1591_, 1);
v___x_1593_ = ((size_t)1ULL);
v___x_1594_ = lean_usize_add(v_i_1568_, v___x_1593_);
v___x_1595_ = lean_array_uset(v_bs_x27_1585_, v_i_1568_, v_a_1592_);
v_i_1568_ = v___x_1594_;
v_bs_1569_ = v___x_1595_;
goto _start;
}
else
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
lean_dec_ref(v_bs_x27_1585_);
lean_dec_ref(v_val_1564_);
lean_dec(v_declName_1563_);
v_a_1597_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v___x_1591_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1591_);
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
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1563_ = stack[0].m_obj;
lean_object* v_val_1564_ = stack[1].m_obj;
uint8_t v___x_1565_ = stack[2].m_num;
uint8_t v___x_1566_ = stack[3].m_num;
size_t v_sz_1567_ = stack[4].m_num;
size_t v_i_1568_ = stack[5].m_num;
lean_object* v_bs_1569_ = stack[6].m_obj;
lean_object* v___y_1570_ = stack[7].m_obj;
lean_object* v___y_1571_ = stack[8].m_obj;
lean_object* v___y_1572_ = stack[9].m_obj;
lean_object* v___y_1573_ = stack[10].m_obj;
lean_object* v_res_1605_;
v_res_1605_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5(v_declName_1563_, v_val_1564_, v___x_1565_, v___x_1566_, v_sz_1567_, v_i_1568_, v_bs_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
stack->m_obj
 = v_res_1605_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5___boxed(lean_object* v_declName_1606_, lean_object* v_val_1607_, lean_object* v___x_1608_, lean_object* v___x_1609_, lean_object* v_sz_1610_, lean_object* v_i_1611_, lean_object* v_bs_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
uint8_t v___x_32423__boxed_1618_; uint8_t v___x_32424__boxed_1619_; size_t v_sz_boxed_1620_; size_t v_i_boxed_1621_; lean_object* v_res_1622_; 
v___x_32423__boxed_1618_ = lean_unbox(v___x_1608_);
v___x_32424__boxed_1619_ = lean_unbox(v___x_1609_);
v_sz_boxed_1620_ = lean_unbox_usize(v_sz_1610_);
lean_dec(v_sz_1610_);
v_i_boxed_1621_ = lean_unbox_usize(v_i_1611_);
lean_dec(v_i_1611_);
v_res_1622_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5(v_declName_1606_, v_val_1607_, v___x_32423__boxed_1618_, v___x_32424__boxed_1619_, v_sz_boxed_1620_, v_i_boxed_1621_, v_bs_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
return v_res_1622_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(lean_object* v_val_1623_, lean_object* v___x_1624_, lean_object* v_x_1625_, lean_object* v_mvarId_1626_, uint8_t v___x_1627_, lean_object* v_declName_1628_, uint8_t v_hasTrace_1629_, lean_object* v_____r_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v_majorPos_1660_; lean_object* v_arity_1661_; lean_object* v_insterestingCtors_1662_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___x_1682_; uint8_t v___x_1683_; 
v_majorPos_1660_ = lean_ctor_get(v_val_1623_, 1);
v_arity_1661_ = lean_ctor_get(v_val_1623_, 2);
v_insterestingCtors_1662_ = lean_ctor_get(v_val_1623_, 3);
v___x_1682_ = lean_array_get_size(v_x_1625_);
v___x_1683_ = lean_nat_dec_lt(v___x_1682_, v_arity_1661_);
if (v___x_1683_ == 0)
{
v___y_1664_ = v___y_1631_;
v___y_1665_ = v___y_1632_;
v___y_1666_ = v___y_1633_;
v___y_1667_ = v___y_1634_;
goto v___jp_1663_;
}
else
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_dec(v_declName_1628_);
lean_dec(v_mvarId_1626_);
lean_dec_ref(v_val_1623_);
v___x_1684_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1);
v___x_1685_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1684_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1685_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1685_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
v___jp_1636_:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1643_ = lean_array_get_borrowed(v___x_1624_, v_x_1625_, v___y_1637_);
lean_dec(v___y_1637_);
v___x_1644_ = l_Lean_Expr_fvarId_x21(v___x_1643_);
v___x_1645_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__0));
v___x_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1646_, 0, v___y_1638_);
v___x_1647_ = l_Lean_MVarId_cases(v_mvarId_1626_, v___x_1644_, v___x_1645_, v___x_1627_, v___x_1646_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; size_t v_sz_1649_; size_t v___x_1650_; lean_object* v___x_1651_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_a_1648_);
lean_dec_ref_known(v___x_1647_, 1);
v_sz_1649_ = lean_array_size(v_a_1648_);
v___x_1650_ = ((size_t)0ULL);
v___x_1651_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5(v_declName_1628_, v_val_1623_, v___x_1627_, v_hasTrace_1629_, v_sz_1649_, v___x_1650_, v_a_1648_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
return v___x_1651_;
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec(v_declName_1628_);
lean_dec_ref(v_val_1623_);
v_a_1652_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1647_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1647_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
v___jp_1663_:
{
lean_object* v___x_1668_; uint8_t v___x_1669_; 
v___x_1668_ = lean_array_get_borrowed(v___x_1624_, v_x_1625_, v_majorPos_1660_);
v___x_1669_ = l_Lean_Expr_isFVar(v___x_1668_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
lean_dec(v_declName_1628_);
lean_dec(v_mvarId_1626_);
lean_dec_ref(v_val_1623_);
v___x_1670_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__2);
lean_inc(v___x_1668_);
v___x_1671_ = l_Lean_indentExpr(v___x_1668_);
v___x_1672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1670_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
v___x_1673_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1672_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v___x_1673_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1673_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1674_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
else
{
lean_inc_ref(v_insterestingCtors_1662_);
lean_inc(v_majorPos_1660_);
v___y_1637_ = v_majorPos_1660_;
v___y_1638_ = v_insterestingCtors_1662_;
v___y_1639_ = v___y_1664_;
v___y_1640_ = v___y_1665_;
v___y_1641_ = v___y_1666_;
v___y_1642_ = v___y_1667_;
goto v___jp_1636_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1623_ = stack[0].m_obj;
lean_object* v___x_1624_ = stack[1].m_obj;
lean_object* v_x_1625_ = stack[2].m_obj;
lean_object* v_mvarId_1626_ = stack[3].m_obj;
uint8_t v___x_1627_ = stack[4].m_num;
lean_object* v_declName_1628_ = stack[5].m_obj;
uint8_t v_hasTrace_1629_ = stack[6].m_num;
lean_object* v_____r_1630_ = stack[7].m_obj;
lean_object* v___y_1631_ = stack[8].m_obj;
lean_object* v___y_1632_ = stack[9].m_obj;
lean_object* v___y_1633_ = stack[10].m_obj;
lean_object* v___y_1634_ = stack[11].m_obj;
lean_object* v_res_1694_;
v_res_1694_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v_val_1623_, v___x_1624_, v_x_1625_, v_mvarId_1626_, v___x_1627_, v_declName_1628_, v_hasTrace_1629_, v_____r_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
stack->m_obj
 = v_res_1694_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0___boxed(lean_object* v_val_1695_, lean_object* v___x_1696_, lean_object* v_x_1697_, lean_object* v_mvarId_1698_, lean_object* v___x_1699_, lean_object* v_declName_1700_, lean_object* v_hasTrace_1701_, lean_object* v_____r_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
uint8_t v___x_32550__boxed_1708_; uint8_t v_hasTrace_boxed_1709_; lean_object* v_res_1710_; 
v___x_32550__boxed_1708_ = lean_unbox(v___x_1699_);
v_hasTrace_boxed_1709_ = lean_unbox(v_hasTrace_1701_);
v_res_1710_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v_val_1695_, v___x_1696_, v_x_1697_, v_mvarId_1698_, v___x_32550__boxed_1708_, v_declName_1700_, v_hasTrace_boxed_1709_, v_____r_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec_ref(v_x_1697_);
lean_dec_ref(v___x_1696_);
return v_res_1710_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1(void){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1712_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__0));
v___x_1713_ = l_Lean_stringToMessageData(v___x_1712_);
return v___x_1713_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3(void){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1715_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__2));
v___x_1716_ = l_Lean_stringToMessageData(v___x_1715_);
return v___x_1716_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6(lean_object* v_mvarId_1717_, lean_object* v_x_1718_, lean_object* v_x_1719_, lean_object* v_x_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
if (lean_obj_tag(v_x_1718_) == 5)
{
lean_object* v_fn_1726_; lean_object* v_arg_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v_fn_1726_ = lean_ctor_get(v_x_1718_, 0);
lean_inc_ref(v_fn_1726_);
v_arg_1727_ = lean_ctor_get(v_x_1718_, 1);
lean_inc_ref(v_arg_1727_);
lean_dec_ref_known(v_x_1718_, 2);
v___x_1728_ = lean_array_set(v_x_1719_, v_x_1720_, v_arg_1727_);
v___x_1729_ = lean_unsigned_to_nat(1u);
v___x_1730_ = lean_nat_sub(v_x_1720_, v___x_1729_);
lean_dec(v_x_1720_);
v_x_1718_ = v_fn_1726_;
v_x_1719_ = v___x_1728_;
v_x_1720_ = v___x_1730_;
goto _start;
}
else
{
lean_dec(v_x_1720_);
if (lean_obj_tag(v_x_1718_) == 4)
{
lean_object* v_declName_1732_; lean_object* v___f_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v_declName_1732_ = lean_ctor_get(v_x_1718_, 0);
lean_inc_n(v_declName_1732_, 2);
lean_dec_ref_known(v_x_1718_, 2);
v___f_1733_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1));
v___x_1734_ = l_Lean_instInhabitedExpr;
v___x_1735_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_declName_1732_, v___y_1724_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1736_);
lean_dec_ref_known(v___x_1735_, 1);
if (lean_obj_tag(v_a_1736_) == 1)
{
lean_object* v_toCold_1737_; lean_object* v_options_1738_; lean_object* v_val_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_2047_; 
v_toCold_1737_ = lean_ctor_get(v___y_1723_, 0);
v_options_1738_ = lean_ctor_get(v_toCold_1737_, 2);
v_val_1739_ = lean_ctor_get(v_a_1736_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v_a_1736_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_1741_ = v_a_1736_;
v_isShared_1742_ = v_isSharedCheck_2047_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_val_1739_);
lean_dec(v_a_1736_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_2047_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v_inheritedTraceOptions_1743_; uint8_t v_hasTrace_1744_; lean_object* v___x_1745_; lean_object* v___y_1747_; lean_object* v___y_1748_; uint8_t v___y_1749_; lean_object* v___y_1782_; lean_object* v_a_1783_; lean_object* v___y_1787_; lean_object* v___y_1790_; lean_object* v___y_1791_; uint8_t v___y_1792_; lean_object* v___y_1825_; lean_object* v_a_1826_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; 
v_inheritedTraceOptions_1743_ = lean_ctor_get(v_toCold_1737_, 11);
v_hasTrace_1744_ = lean_ctor_get_uint8(v_options_1738_, sizeof(void*)*1);
v___x_1745_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5));
if (v_hasTrace_1744_ == 0)
{
lean_object* v_majorPos_1856_; lean_object* v_arity_1857_; lean_object* v_insterestingCtors_1858_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___x_1878_; uint8_t v___x_1879_; 
v_majorPos_1856_ = lean_ctor_get(v_val_1739_, 1);
v_arity_1857_ = lean_ctor_get(v_val_1739_, 2);
v_insterestingCtors_1858_ = lean_ctor_get(v_val_1739_, 3);
v___x_1878_ = lean_array_get_size(v_x_1719_);
v___x_1879_ = lean_nat_dec_lt(v___x_1878_, v_arity_1857_);
if (v___x_1879_ == 0)
{
v___y_1860_ = v___y_1721_;
v___y_1861_ = v___y_1722_;
v___y_1862_ = v___y_1723_;
v___y_1863_ = v___y_1724_;
goto v___jp_1859_;
}
else
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
lean_del_object(v___x_1741_);
lean_dec(v_val_1739_);
lean_dec(v_declName_1732_);
lean_dec_ref(v_x_1719_);
lean_dec(v_mvarId_1717_);
v___x_1880_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1);
v___x_1881_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1880_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1881_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1881_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
lean_inc(v_a_1882_);
if (v_isShared_1885_ == 0)
{
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
v___y_1825_ = v___x_1887_;
v_a_1826_ = v_a_1882_;
goto v___jp_1824_;
}
}
}
v___jp_1859_:
{
lean_object* v___x_1864_; uint8_t v___x_1865_; 
v___x_1864_ = lean_array_get_borrowed(v___x_1734_, v_x_1719_, v_majorPos_1856_);
v___x_1865_ = l_Lean_Expr_isFVar(v___x_1864_);
if (v___x_1865_ == 0)
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
lean_inc(v___x_1864_);
lean_del_object(v___x_1741_);
lean_dec(v_val_1739_);
lean_dec(v_declName_1732_);
lean_dec_ref(v_x_1719_);
lean_dec(v_mvarId_1717_);
v___x_1866_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__2);
v___x_1867_ = l_Lean_indentExpr(v___x_1864_);
v___x_1868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1866_);
lean_ctor_set(v___x_1868_, 1, v___x_1867_);
v___x_1869_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1868_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1869_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1869_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
lean_inc(v_a_1870_);
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
v___y_1825_ = v___x_1875_;
v_a_1826_ = v_a_1870_;
goto v___jp_1824_;
}
}
}
else
{
lean_inc(v_majorPos_1856_);
lean_inc_ref(v_insterestingCtors_1858_);
v___y_1830_ = v_insterestingCtors_1858_;
v___y_1831_ = v_majorPos_1856_;
v___y_1832_ = v___y_1860_;
v___y_1833_ = v___y_1861_;
v___y_1834_ = v___y_1862_;
v___y_1835_ = v___y_1863_;
goto v___jp_1829_;
}
}
}
else
{
lean_object* v___x_1890_; lean_object* v___x_1891_; uint8_t v___x_1892_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v_a_1896_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v_a_1911_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; uint8_t v___y_1917_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v_a_1930_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v_a_1949_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v_a_1961_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; uint8_t v___y_1967_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v_a_1980_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; 
lean_del_object(v___x_1741_);
v___x_1890_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__6));
v___x_1891_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9);
v___x_1892_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1743_, v_options_1738_, v___x_1891_);
if (v___x_1892_ == 0)
{
lean_object* v___x_2029_; uint8_t v___x_2030_; 
v___x_2029_ = l_Lean_trace_profiler;
v___x_2030_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_options_1738_, v___x_2029_);
if (v___x_2030_ == 0)
{
if (v___x_1892_ == 0)
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2031_ = lean_box(0);
v___x_2032_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v_val_1739_, v___x_1734_, v_x_1719_, v_mvarId_1717_, v___x_2030_, v_declName_1732_, v_hasTrace_1744_, v___x_2031_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
lean_dec_ref(v_x_1719_);
v___y_1787_ = v___x_2032_;
goto v___jp_1786_;
}
else
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2033_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3);
lean_inc(v_mvarId_1717_);
v___x_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2034_, 0, v_mvarId_1717_);
v___x_2035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2033_);
lean_ctor_set(v___x_2035_, 1, v___x_2034_);
v___x_2036_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1745_, v___x_2035_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v___x_2038_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_a_2037_);
lean_dec_ref_known(v___x_2036_, 1);
v___x_2038_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v_val_1739_, v___x_1734_, v_x_1719_, v_mvarId_1717_, v___x_2030_, v_declName_1732_, v_hasTrace_1744_, v_a_2037_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
lean_dec_ref(v_x_1719_);
v___y_1787_ = v___x_2038_;
goto v___jp_1786_;
}
else
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
lean_dec(v_val_1739_);
lean_dec(v_declName_1732_);
lean_dec_ref(v_x_1719_);
lean_dec(v_mvarId_1717_);
v_a_2039_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2041_ = v___x_2036_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2036_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
lean_inc(v_a_2039_);
if (v_isShared_2042_ == 0)
{
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
v___y_1782_ = v___x_2044_;
v_a_1783_ = v_a_2039_;
goto v___jp_1781_;
}
}
}
}
}
else
{
goto v___jp_1996_;
}
}
else
{
goto v___jp_1996_;
}
v___jp_1893_:
{
lean_object* v___x_1897_; double v___x_1898_; double v___x_1899_; double v___x_1900_; double v___x_1901_; double v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1897_ = lean_io_mono_nanos_now();
v___x_1898_ = lean_float_of_nat(v___y_1894_);
v___x_1899_ = lean_float_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10);
v___x_1900_ = lean_float_div(v___x_1898_, v___x_1899_);
v___x_1901_ = lean_float_of_nat(v___x_1897_);
v___x_1902_ = lean_float_div(v___x_1901_, v___x_1899_);
v___x_1903_ = lean_box_float(v___x_1900_);
v___x_1904_ = lean_box_float(v___x_1902_);
v___x_1905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1903_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
v___x_1906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1906_, 0, v_a_1896_);
lean_ctor_set(v___x_1906_, 1, v___x_1905_);
v___x_1907_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_1745_, v_hasTrace_1744_, v___x_1890_, v_options_1738_, v___x_1892_, v___y_1895_, v___f_1733_, v___x_1906_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
return v___x_1907_;
}
v___jp_1908_:
{
lean_object* v___x_1912_; 
v___x_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1912_, 0, v_a_1911_);
v___y_1894_ = v___y_1909_;
v___y_1895_ = v___y_1910_;
v_a_1896_ = v___x_1912_;
goto v___jp_1893_;
}
v___jp_1913_:
{
if (v___y_1917_ == 0)
{
lean_object* v___x_1918_; lean_object* v_a_1919_; uint8_t v___x_1920_; 
v___x_1918_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(v___x_1745_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_a_1919_);
lean_dec_ref(v___x_1918_);
v___x_1920_ = lean_unbox(v_a_1919_);
lean_dec(v_a_1919_);
if (v___x_1920_ == 0)
{
v___y_1909_ = v___y_1914_;
v___y_1910_ = v___y_1916_;
v_a_1911_ = v___y_1915_;
goto v___jp_1908_;
}
else
{
lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1921_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1);
lean_inc_ref(v___y_1915_);
v___x_1922_ = l_Lean_Exception_toMessageData(v___y_1915_);
v___x_1923_ = l_Lean_indentD(v___x_1922_);
v___x_1924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1921_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
v___x_1925_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1745_, v___x_1924_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_dec_ref_known(v___x_1925_, 1);
v___y_1909_ = v___y_1914_;
v___y_1910_ = v___y_1916_;
v_a_1911_ = v___y_1915_;
goto v___jp_1908_;
}
else
{
lean_object* v_a_1926_; 
lean_dec_ref(v___y_1915_);
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1926_);
lean_dec_ref_known(v___x_1925_, 1);
v___y_1909_ = v___y_1914_;
v___y_1910_ = v___y_1916_;
v_a_1911_ = v_a_1926_;
goto v___jp_1908_;
}
}
}
else
{
v___y_1909_ = v___y_1914_;
v___y_1910_ = v___y_1916_;
v_a_1911_ = v___y_1915_;
goto v___jp_1908_;
}
}
v___jp_1927_:
{
uint8_t v___x_1931_; 
v___x_1931_ = l_Lean_Exception_isInterrupt(v_a_1930_);
if (v___x_1931_ == 0)
{
uint8_t v___x_1932_; 
lean_inc_ref(v_a_1930_);
v___x_1932_ = l_Lean_Exception_isRuntime(v_a_1930_);
v___y_1914_ = v___y_1928_;
v___y_1915_ = v_a_1930_;
v___y_1916_ = v___y_1929_;
v___y_1917_ = v___x_1932_;
goto v___jp_1913_;
}
else
{
v___y_1914_ = v___y_1928_;
v___y_1915_ = v_a_1930_;
v___y_1916_ = v___y_1929_;
v___y_1917_ = v___x_1931_;
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
v___y_1894_ = v___y_1934_;
v___y_1895_ = v___y_1935_;
v_a_1896_ = v___x_1942_;
goto v___jp_1893_;
}
}
}
else
{
lean_object* v_a_1945_; 
v_a_1945_ = lean_ctor_get(v___y_1936_, 0);
lean_inc(v_a_1945_);
lean_dec_ref_known(v___y_1936_, 1);
v___y_1928_ = v___y_1934_;
v___y_1929_ = v___y_1935_;
v_a_1930_ = v_a_1945_;
goto v___jp_1927_;
}
}
v___jp_1946_:
{
lean_object* v___x_1950_; double v___x_1951_; double v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1950_ = lean_io_get_num_heartbeats();
v___x_1951_ = lean_float_of_nat(v___y_1947_);
v___x_1952_ = lean_float_of_nat(v___x_1950_);
v___x_1953_ = lean_box_float(v___x_1951_);
v___x_1954_ = lean_box_float(v___x_1952_);
v___x_1955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1953_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
v___x_1956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1956_, 0, v_a_1949_);
lean_ctor_set(v___x_1956_, 1, v___x_1955_);
v___x_1957_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_1745_, v_hasTrace_1744_, v___x_1890_, v_options_1738_, v___x_1892_, v___y_1948_, v___f_1733_, v___x_1956_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
return v___x_1957_;
}
v___jp_1958_:
{
lean_object* v___x_1962_; 
v___x_1962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1962_, 0, v_a_1961_);
v___y_1947_ = v___y_1959_;
v___y_1948_ = v___y_1960_;
v_a_1949_ = v___x_1962_;
goto v___jp_1946_;
}
v___jp_1963_:
{
if (v___y_1967_ == 0)
{
lean_object* v___x_1968_; lean_object* v_a_1969_; uint8_t v___x_1970_; 
v___x_1968_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(v___x_1745_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_a_1969_);
lean_dec_ref(v___x_1968_);
v___x_1970_ = lean_unbox(v_a_1969_);
lean_dec(v_a_1969_);
if (v___x_1970_ == 0)
{
v___y_1959_ = v___y_1964_;
v___y_1960_ = v___y_1966_;
v_a_1961_ = v___y_1965_;
goto v___jp_1958_;
}
else
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1971_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1);
lean_inc_ref(v___y_1965_);
v___x_1972_ = l_Lean_Exception_toMessageData(v___y_1965_);
v___x_1973_ = l_Lean_indentD(v___x_1972_);
v___x_1974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1971_);
lean_ctor_set(v___x_1974_, 1, v___x_1973_);
v___x_1975_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1745_, v___x_1974_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_dec_ref_known(v___x_1975_, 1);
v___y_1959_ = v___y_1964_;
v___y_1960_ = v___y_1966_;
v_a_1961_ = v___y_1965_;
goto v___jp_1958_;
}
else
{
lean_object* v_a_1976_; 
lean_dec_ref(v___y_1965_);
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
lean_inc(v_a_1976_);
lean_dec_ref_known(v___x_1975_, 1);
v___y_1959_ = v___y_1964_;
v___y_1960_ = v___y_1966_;
v_a_1961_ = v_a_1976_;
goto v___jp_1958_;
}
}
}
else
{
v___y_1959_ = v___y_1964_;
v___y_1960_ = v___y_1966_;
v_a_1961_ = v___y_1965_;
goto v___jp_1958_;
}
}
v___jp_1977_:
{
uint8_t v___x_1981_; 
v___x_1981_ = l_Lean_Exception_isInterrupt(v_a_1980_);
if (v___x_1981_ == 0)
{
uint8_t v___x_1982_; 
lean_inc_ref(v_a_1980_);
v___x_1982_ = l_Lean_Exception_isRuntime(v_a_1980_);
v___y_1964_ = v___y_1978_;
v___y_1965_ = v_a_1980_;
v___y_1966_ = v___y_1979_;
v___y_1967_ = v___x_1982_;
goto v___jp_1963_;
}
else
{
v___y_1964_ = v___y_1978_;
v___y_1965_ = v_a_1980_;
v___y_1966_ = v___y_1979_;
v___y_1967_ = v___x_1981_;
goto v___jp_1963_;
}
}
v___jp_1983_:
{
if (lean_obj_tag(v___y_1986_) == 0)
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
v_a_1987_ = lean_ctor_get(v___y_1986_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___y_1986_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___y_1986_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___y_1986_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
lean_ctor_set_tag(v___x_1989_, 1);
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
v___y_1947_ = v___y_1984_;
v___y_1948_ = v___y_1985_;
v_a_1949_ = v___x_1992_;
goto v___jp_1946_;
}
}
}
else
{
lean_object* v_a_1995_; 
v_a_1995_ = lean_ctor_get(v___y_1986_, 0);
lean_inc(v_a_1995_);
lean_dec_ref_known(v___y_1986_, 1);
v___y_1978_ = v___y_1984_;
v___y_1979_ = v___y_1985_;
v_a_1980_ = v_a_1995_;
goto v___jp_1977_;
}
}
v___jp_1996_:
{
lean_object* v___x_1997_; lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2028_; 
v___x_1997_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___y_1724_);
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2000_ = v___x_1997_;
v_isShared_2001_ = v_isSharedCheck_2028_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_dec(v___x_1997_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2028_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2002_; uint8_t v___x_2003_; 
v___x_2002_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2003_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_options_1738_, v___x_2002_);
if (v___x_2003_ == 0)
{
lean_object* v___x_2004_; 
v___x_2004_ = lean_io_mono_nanos_now();
if (v___x_1892_ == 0)
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
lean_del_object(v___x_2000_);
v___x_2005_ = lean_box(0);
v___x_2006_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v_val_1739_, v___x_1734_, v_x_1719_, v_mvarId_1717_, v___x_2003_, v_declName_1732_, v_hasTrace_1744_, v___x_2005_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
lean_dec_ref(v_x_1719_);
v___y_1934_ = v___x_2004_;
v___y_1935_ = v_a_1998_;
v___y_1936_ = v___x_2006_;
goto v___jp_1933_;
}
else
{
lean_object* v___x_2007_; lean_object* v___x_2009_; 
v___x_2007_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3);
lean_inc(v_mvarId_1717_);
if (v_isShared_2001_ == 0)
{
lean_ctor_set_tag(v___x_2000_, 1);
lean_ctor_set(v___x_2000_, 0, v_mvarId_1717_);
v___x_2009_ = v___x_2000_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_mvarId_1717_);
v___x_2009_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2007_);
lean_ctor_set(v___x_2010_, 1, v___x_2009_);
v___x_2011_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1745_, v___x_2010_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_a_2012_; lean_object* v___x_2013_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2012_);
lean_dec_ref_known(v___x_2011_, 1);
v___x_2013_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v_val_1739_, v___x_1734_, v_x_1719_, v_mvarId_1717_, v___x_2003_, v_declName_1732_, v_hasTrace_1744_, v_a_2012_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
lean_dec_ref(v_x_1719_);
v___y_1934_ = v___x_2004_;
v___y_1935_ = v_a_1998_;
v___y_1936_ = v___x_2013_;
goto v___jp_1933_;
}
else
{
lean_object* v_a_2014_; 
lean_dec(v_val_1739_);
lean_dec(v_declName_1732_);
lean_dec_ref(v_x_1719_);
lean_dec(v_mvarId_1717_);
v_a_2014_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2014_);
lean_dec_ref_known(v___x_2011_, 1);
v___y_1928_ = v___x_2004_;
v___y_1929_ = v_a_1998_;
v_a_1930_ = v_a_2014_;
goto v___jp_1927_;
}
}
}
}
else
{
lean_object* v___x_2016_; 
v___x_2016_ = lean_io_get_num_heartbeats();
if (v___x_1892_ == 0)
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
lean_del_object(v___x_2000_);
v___x_2017_ = lean_box(0);
v___x_2018_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(v_val_1739_, v___x_1734_, v_x_1719_, v_mvarId_1717_, v_declName_1732_, v___x_2003_, v___x_2017_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
lean_dec_ref(v_x_1719_);
v___y_1984_ = v___x_2016_;
v___y_1985_ = v_a_1998_;
v___y_1986_ = v___x_2018_;
goto v___jp_1983_;
}
else
{
lean_object* v___x_2019_; lean_object* v___x_2021_; 
v___x_2019_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3);
lean_inc(v_mvarId_1717_);
if (v_isShared_2001_ == 0)
{
lean_ctor_set_tag(v___x_2000_, 1);
lean_ctor_set(v___x_2000_, 0, v_mvarId_1717_);
v___x_2021_ = v___x_2000_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_mvarId_1717_);
v___x_2021_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2019_);
lean_ctor_set(v___x_2022_, 1, v___x_2021_);
v___x_2023_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1745_, v___x_2022_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2025_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2024_);
lean_dec_ref_known(v___x_2023_, 1);
v___x_2025_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(v_val_1739_, v___x_1734_, v_x_1719_, v_mvarId_1717_, v_declName_1732_, v___x_2003_, v_a_2024_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
lean_dec_ref(v_x_1719_);
v___y_1984_ = v___x_2016_;
v___y_1985_ = v_a_1998_;
v___y_1986_ = v___x_2025_;
goto v___jp_1983_;
}
else
{
lean_object* v_a_2026_; 
lean_dec(v_val_1739_);
lean_dec(v_declName_1732_);
lean_dec_ref(v_x_1719_);
lean_dec(v_mvarId_1717_);
v_a_2026_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2026_);
lean_dec_ref_known(v___x_2023_, 1);
v___y_1978_ = v___x_2016_;
v___y_1979_ = v_a_1998_;
v_a_1980_ = v_a_2026_;
goto v___jp_1977_;
}
}
}
}
}
}
}
v___jp_1746_:
{
if (v___y_1749_ == 0)
{
lean_object* v___x_1750_; lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1780_; 
lean_dec_ref(v___y_1747_);
v___x_1750_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(v___x_1745_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1753_ = v___x_1750_;
v_isShared_1754_ = v_isSharedCheck_1780_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1750_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1780_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
uint8_t v___x_1755_; 
v___x_1755_ = lean_unbox(v_a_1751_);
lean_dec(v_a_1751_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1757_; 
if (v_isShared_1754_ == 0)
{
lean_ctor_set_tag(v___x_1753_, 1);
lean_ctor_set(v___x_1753_, 0, v___y_1748_);
v___x_1757_ = v___x_1753_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___y_1748_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
else
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
lean_del_object(v___x_1753_);
v___x_1759_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1);
lean_inc_ref(v___y_1748_);
v___x_1760_ = l_Lean_Exception_toMessageData(v___y_1748_);
v___x_1761_ = l_Lean_indentD(v___x_1760_);
v___x_1762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1759_);
lean_ctor_set(v___x_1762_, 1, v___x_1761_);
v___x_1763_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1745_, v___x_1762_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1770_ == 0)
{
lean_object* v_unused_1771_; 
v_unused_1771_ = lean_ctor_get(v___x_1763_, 0);
lean_dec(v_unused_1771_);
v___x_1765_ = v___x_1763_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_dec(v___x_1763_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
lean_ctor_set_tag(v___x_1765_, 1);
lean_ctor_set(v___x_1765_, 0, v___y_1748_);
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___y_1748_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
else
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
lean_dec_ref(v___y_1748_);
v_a_1772_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v___x_1763_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1763_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_1748_);
return v___y_1747_;
}
}
v___jp_1781_:
{
uint8_t v___x_1784_; 
v___x_1784_ = l_Lean_Exception_isInterrupt(v_a_1783_);
if (v___x_1784_ == 0)
{
uint8_t v___x_1785_; 
lean_inc_ref(v_a_1783_);
v___x_1785_ = l_Lean_Exception_isRuntime(v_a_1783_);
v___y_1747_ = v___y_1782_;
v___y_1748_ = v_a_1783_;
v___y_1749_ = v___x_1785_;
goto v___jp_1746_;
}
else
{
v___y_1747_ = v___y_1782_;
v___y_1748_ = v_a_1783_;
v___y_1749_ = v___x_1784_;
goto v___jp_1746_;
}
}
v___jp_1786_:
{
if (lean_obj_tag(v___y_1787_) == 0)
{
return v___y_1787_;
}
else
{
lean_object* v_a_1788_; 
v_a_1788_ = lean_ctor_get(v___y_1787_, 0);
lean_inc(v_a_1788_);
v___y_1782_ = v___y_1787_;
v_a_1783_ = v_a_1788_;
goto v___jp_1781_;
}
}
v___jp_1789_:
{
if (v___y_1792_ == 0)
{
lean_object* v___x_1793_; lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1823_; 
lean_dec_ref(v___y_1791_);
v___x_1793_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(v___x_1745_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1796_ = v___x_1793_;
v_isShared_1797_ = v_isSharedCheck_1823_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1793_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1823_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
uint8_t v___x_1798_; 
v___x_1798_ = lean_unbox(v_a_1794_);
lean_dec(v_a_1794_);
if (v___x_1798_ == 0)
{
lean_object* v___x_1800_; 
if (v_isShared_1797_ == 0)
{
lean_ctor_set_tag(v___x_1796_, 1);
lean_ctor_set(v___x_1796_, 0, v___y_1790_);
v___x_1800_ = v___x_1796_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v___y_1790_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
else
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
lean_del_object(v___x_1796_);
v___x_1802_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1);
lean_inc_ref(v___y_1790_);
v___x_1803_ = l_Lean_Exception_toMessageData(v___y_1790_);
v___x_1804_ = l_Lean_indentD(v___x_1803_);
v___x_1805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1802_);
lean_ctor_set(v___x_1805_, 1, v___x_1804_);
v___x_1806_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1745_, v___x_1805_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1813_; 
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1813_ == 0)
{
lean_object* v_unused_1814_; 
v_unused_1814_ = lean_ctor_get(v___x_1806_, 0);
lean_dec(v_unused_1814_);
v___x_1808_ = v___x_1806_;
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
else
{
lean_dec(v___x_1806_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1809_ == 0)
{
lean_ctor_set_tag(v___x_1808_, 1);
lean_ctor_set(v___x_1808_, 0, v___y_1790_);
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___y_1790_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
else
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1822_; 
lean_dec_ref(v___y_1790_);
v_a_1815_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1817_ = v___x_1806_;
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1806_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1820_; 
if (v_isShared_1818_ == 0)
{
v___x_1820_ = v___x_1817_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_a_1815_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_1790_);
return v___y_1791_;
}
}
v___jp_1824_:
{
uint8_t v___x_1827_; 
v___x_1827_ = l_Lean_Exception_isInterrupt(v_a_1826_);
if (v___x_1827_ == 0)
{
uint8_t v___x_1828_; 
lean_inc_ref(v_a_1826_);
v___x_1828_ = l_Lean_Exception_isRuntime(v_a_1826_);
v___y_1790_ = v_a_1826_;
v___y_1791_ = v___y_1825_;
v___y_1792_ = v___x_1828_;
goto v___jp_1789_;
}
else
{
v___y_1790_ = v_a_1826_;
v___y_1791_ = v___y_1825_;
v___y_1792_ = v___x_1827_;
goto v___jp_1789_;
}
}
v___jp_1829_:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1840_; 
v___x_1836_ = lean_array_get(v___x_1734_, v_x_1719_, v___y_1831_);
lean_dec(v___y_1831_);
lean_dec_ref(v_x_1719_);
v___x_1837_ = l_Lean_Expr_fvarId_x21(v___x_1836_);
lean_dec(v___x_1836_);
v___x_1838_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___closed__0));
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v___y_1830_);
v___x_1840_ = v___x_1741_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___y_1830_);
v___x_1840_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
lean_object* v___x_1841_; 
v___x_1841_ = l_Lean_MVarId_cases(v_mvarId_1717_, v___x_1837_, v___x_1838_, v_hasTrace_1744_, v___x_1840_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; size_t v_sz_1843_; size_t v___x_1844_; lean_object* v___x_1845_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_a_1842_);
lean_dec_ref_known(v___x_1841_, 1);
v_sz_1843_ = lean_array_size(v_a_1842_);
v___x_1844_ = ((size_t)0ULL);
v___x_1845_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(v_declName_1732_, v_val_1739_, v_hasTrace_1744_, v_sz_1843_, v___x_1844_, v_a_1842_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
if (lean_obj_tag(v___x_1845_) == 0)
{
return v___x_1845_;
}
else
{
lean_object* v_a_1846_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_a_1846_);
v___y_1825_ = v___x_1845_;
v_a_1826_ = v_a_1846_;
goto v___jp_1824_;
}
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
lean_dec(v_val_1739_);
lean_dec(v_declName_1732_);
v_a_1847_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1841_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1841_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
lean_inc(v_a_1847_);
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
v___y_1825_ = v___x_1852_;
v_a_1826_ = v_a_1847_;
goto v___jp_1824_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
lean_dec(v_a_1736_);
lean_dec(v_declName_1732_);
lean_dec_ref(v_x_1719_);
lean_dec(v_mvarId_1717_);
v___x_2048_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12);
v___x_2049_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_2048_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
return v___x_2049_;
}
}
else
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
lean_dec(v_declName_1732_);
lean_dec_ref(v_x_1719_);
lean_dec(v_mvarId_1717_);
v_a_2050_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_1735_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_1735_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2053_ == 0)
{
v___x_2055_ = v___x_2052_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_a_2050_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
}
else
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
lean_dec_ref(v_x_1719_);
lean_dec_ref(v_x_1718_);
lean_dec(v_mvarId_1717_);
v___x_2058_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14);
v___x_2059_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_2058_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
return v___x_2059_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1717_ = stack[0].m_obj;
lean_object* v_x_1718_ = stack[1].m_obj;
lean_object* v_x_1719_ = stack[2].m_obj;
lean_object* v_x_1720_ = stack[3].m_obj;
lean_object* v___y_1721_ = stack[4].m_obj;
lean_object* v___y_1722_ = stack[5].m_obj;
lean_object* v___y_1723_ = stack[6].m_obj;
lean_object* v___y_1724_ = stack[7].m_obj;
lean_object* v_res_2060_;
v_res_2060_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6(v_mvarId_1717_, v_x_1718_, v_x_1719_, v_x_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
stack->m_obj
 = v_res_2060_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___boxed(lean_object* v_mvarId_2061_, lean_object* v_x_2062_, lean_object* v_x_2063_, lean_object* v_x_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6(v_mvarId_2061_, v_x_2062_, v_x_2063_, v_x_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
return v_res_2070_;
}
}
lean_object* l_Lean_Meta_splitSparseCasesOn(lean_object* v_mvarId_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_){
_start:
{
lean_object* v___x_2077_; 
lean_inc(v_mvarId_2071_);
v___x_2077_ = l_Lean_MVarId_getType(v_mvarId_2071_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; lean_object* v___x_2079_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_a_2078_);
lean_dec_ref_known(v___x_2077_, 1);
v___x_2079_ = l_Lean_Meta_matchEqHEqLHS_x3f(v_a_2078_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
lean_inc(v_a_2080_);
lean_dec_ref_known(v___x_2079_, 1);
if (lean_obj_tag(v_a_2080_) == 1)
{
lean_object* v_val_2081_; lean_object* v_snd_2082_; lean_object* v_dummy_2083_; lean_object* v_nargs_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v_val_2081_ = lean_ctor_get(v_a_2080_, 0);
lean_inc(v_val_2081_);
lean_dec_ref_known(v_a_2080_, 1);
v_snd_2082_ = lean_ctor_get(v_val_2081_, 1);
lean_inc(v_snd_2082_);
lean_dec(v_val_2081_);
v_dummy_2083_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0);
v_nargs_2084_ = l_Lean_Expr_getAppNumArgs(v_snd_2082_);
lean_inc(v_nargs_2084_);
v___x_2085_ = lean_mk_array(v_nargs_2084_, v_dummy_2083_);
v___x_2086_ = lean_unsigned_to_nat(1u);
v___x_2087_ = lean_nat_sub(v_nargs_2084_, v___x_2086_);
lean_dec(v_nargs_2084_);
v___x_2088_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6(v_mvarId_2071_, v_snd_2082_, v___x_2085_, v___x_2087_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_);
return v___x_2088_;
}
else
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
lean_dec(v_a_2080_);
lean_dec(v_mvarId_2071_);
v___x_2089_ = lean_obj_once(&l_Lean_Meta_reduceSparseCasesOn___closed__1, &l_Lean_Meta_reduceSparseCasesOn___closed__1_once, _init_l_Lean_Meta_reduceSparseCasesOn___closed__1);
v___x_2090_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_2089_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_);
return v___x_2090_;
}
}
else
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
lean_dec(v_mvarId_2071_);
v_a_2091_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_2079_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2079_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
lean_dec(v_mvarId_2071_);
v_a_2099_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2077_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2077_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_splitSparseCasesOn_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2071_ = stack[0].m_obj;
lean_object* v_a_2072_ = stack[1].m_obj;
lean_object* v_a_2073_ = stack[2].m_obj;
lean_object* v_a_2074_ = stack[3].m_obj;
lean_object* v_a_2075_ = stack[4].m_obj;
lean_object* v_res_2107_;
v_res_2107_ = l_Lean_Meta_splitSparseCasesOn(v_mvarId_2071_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_);
stack->m_obj
 = v_res_2107_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitSparseCasesOn___boxed(lean_object* v_mvarId_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l_Lean_Meta_splitSparseCasesOn(v_mvarId_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_);
lean_dec(v_a_2112_);
lean_dec_ref(v_a_2111_);
lean_dec(v_a_2110_);
lean_dec_ref(v_a_2109_);
return v_res_2114_;
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
