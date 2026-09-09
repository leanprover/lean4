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
double lean_float_of_nat(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSparseCasesOnInfo___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_unfoldDefinition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x27_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_mkHasNotBitProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(lean_object*, lean_object*, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__0_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Major premise is not a free variable:"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__1_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_59_; lean_object* v_traceState_60_; lean_object* v_traces_61_; lean_object* v___x_62_; lean_object* v_traceState_63_; lean_object* v_env_64_; lean_object* v_nextMacroScope_65_; lean_object* v_ngen_66_; lean_object* v_auxDeclNGen_67_; lean_object* v_cache_68_; lean_object* v_messages_69_; lean_object* v_infoState_70_; lean_object* v_snapshotTasks_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_90_; 
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
v_isSharedCheck_90_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_90_ == 0)
{
v___x_73_ = v___x_62_;
v_isShared_74_ = v_isSharedCheck_90_;
goto v_resetjp_72_;
}
else
{
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
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_90_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
uint64_t v_tid_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_88_; 
v_tid_75_ = lean_ctor_get_uint64(v_traceState_63_, sizeof(void*)*1);
v_isSharedCheck_88_ = !lean_is_exclusive(v_traceState_63_);
if (v_isSharedCheck_88_ == 0)
{
lean_object* v_unused_89_; 
v_unused_89_ = lean_ctor_get(v_traceState_63_, 0);
lean_dec(v_unused_89_);
v___x_77_ = v_traceState_63_;
v_isShared_78_ = v_isSharedCheck_88_;
goto v_resetjp_76_;
}
else
{
lean_dec(v_traceState_63_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_88_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_79_; lean_object* v___x_81_; 
v___x_79_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___closed__1);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 0, v___x_79_);
v___x_81_ = v___x_77_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v___x_79_);
lean_ctor_set_uint64(v_reuseFailAlloc_87_, sizeof(void*)*1, v_tid_75_);
v___x_81_ = v_reuseFailAlloc_87_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
lean_object* v___x_83_; 
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 4, v___x_81_);
v___x_83_ = v___x_73_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v_env_64_);
lean_ctor_set(v_reuseFailAlloc_86_, 1, v_nextMacroScope_65_);
lean_ctor_set(v_reuseFailAlloc_86_, 2, v_ngen_66_);
lean_ctor_set(v_reuseFailAlloc_86_, 3, v_auxDeclNGen_67_);
lean_ctor_set(v_reuseFailAlloc_86_, 4, v___x_81_);
lean_ctor_set(v_reuseFailAlloc_86_, 5, v_cache_68_);
lean_ctor_set(v_reuseFailAlloc_86_, 6, v_messages_69_);
lean_ctor_set(v_reuseFailAlloc_86_, 7, v_infoState_70_);
lean_ctor_set(v_reuseFailAlloc_86_, 8, v_snapshotTasks_71_);
v___x_83_ = v_reuseFailAlloc_86_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = lean_st_ref_put(v___y_57_, v___x_83_);
v___x_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_85_, 0, v_traces_61_);
return v___x_85_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg___boxed(lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___y_91_);
lean_dec(v___y_91_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4(lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___y_97_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___boxed(lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4(v___y_100_, v___y_101_, v___y_102_, v___y_103_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
return v_res_105_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(lean_object* v_opts_106_, lean_object* v_opt_107_){
_start:
{
lean_object* v_name_108_; lean_object* v_defValue_109_; lean_object* v_map_110_; lean_object* v___x_111_; 
v_name_108_ = lean_ctor_get(v_opt_107_, 0);
v_defValue_109_ = lean_ctor_get(v_opt_107_, 1);
v_map_110_ = lean_ctor_get(v_opts_106_, 0);
v___x_111_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_110_, v_name_108_);
if (lean_obj_tag(v___x_111_) == 0)
{
uint8_t v___x_112_; 
v___x_112_ = lean_unbox(v_defValue_109_);
return v___x_112_;
}
else
{
lean_object* v_val_113_; 
v_val_113_ = lean_ctor_get(v___x_111_, 0);
lean_inc(v_val_113_);
lean_dec_ref_known(v___x_111_, 1);
if (lean_obj_tag(v_val_113_) == 1)
{
uint8_t v_v_114_; 
v_v_114_ = lean_ctor_get_uint8(v_val_113_, 0);
lean_dec_ref_known(v_val_113_, 0);
return v_v_114_;
}
else
{
uint8_t v___x_115_; 
lean_dec(v_val_113_);
v___x_115_ = lean_unbox(v_defValue_109_);
return v___x_115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5___boxed(lean_object* v_opts_116_, lean_object* v_opt_117_){
_start:
{
uint8_t v_res_118_; lean_object* v_r_119_; 
v_res_118_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_opts_116_, v_opt_117_);
lean_dec_ref(v_opt_117_);
lean_dec_ref(v_opts_116_);
v_r_119_ = lean_box(v_res_118_);
return v_r_119_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1_spec__2(lean_object* v_a_120_, lean_object* v_as_121_, size_t v_i_122_, size_t v_stop_123_){
_start:
{
uint8_t v___x_124_; 
v___x_124_ = lean_usize_dec_eq(v_i_122_, v_stop_123_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_125_ = lean_array_uget_borrowed(v_as_121_, v_i_122_);
v___x_126_ = lean_name_eq(v_a_120_, v___x_125_);
if (v___x_126_ == 0)
{
size_t v___x_127_; size_t v___x_128_; 
v___x_127_ = ((size_t)1ULL);
v___x_128_ = lean_usize_add(v_i_122_, v___x_127_);
v_i_122_ = v___x_128_;
goto _start;
}
else
{
return v___x_126_;
}
}
else
{
uint8_t v___x_130_; 
v___x_130_ = 0;
return v___x_130_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1_spec__2___boxed(lean_object* v_a_131_, lean_object* v_as_132_, lean_object* v_i_133_, lean_object* v_stop_134_){
_start:
{
size_t v_i_boxed_135_; size_t v_stop_boxed_136_; uint8_t v_res_137_; lean_object* v_r_138_; 
v_i_boxed_135_ = lean_unbox_usize(v_i_133_);
lean_dec(v_i_133_);
v_stop_boxed_136_ = lean_unbox_usize(v_stop_134_);
lean_dec(v_stop_134_);
v_res_137_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1_spec__2(v_a_131_, v_as_132_, v_i_boxed_135_, v_stop_boxed_136_);
lean_dec_ref(v_as_132_);
lean_dec(v_a_131_);
v_r_138_ = lean_box(v_res_137_);
return v_r_138_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1(lean_object* v_as_139_, lean_object* v_a_140_){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_141_ = lean_unsigned_to_nat(0u);
v___x_142_ = lean_array_get_size(v_as_139_);
v___x_143_ = lean_nat_dec_lt(v___x_141_, v___x_142_);
if (v___x_143_ == 0)
{
return v___x_143_;
}
else
{
if (v___x_143_ == 0)
{
return v___x_143_;
}
else
{
size_t v___x_144_; size_t v___x_145_; uint8_t v___x_146_; 
v___x_144_ = ((size_t)0ULL);
v___x_145_ = lean_usize_of_nat(v___x_142_);
v___x_146_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1_spec__2(v_a_140_, v_as_139_, v___x_144_, v___x_145_);
return v___x_146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1___boxed(lean_object* v_as_147_, lean_object* v_a_148_){
_start:
{
uint8_t v_res_149_; lean_object* v_r_150_; 
v_res_149_ = l_Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1(v_as_147_, v_a_148_);
lean_dec(v_a_148_);
lean_dec_ref(v_as_147_);
v_r_150_ = lean_box(v_res_149_);
return v_r_150_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_instMonadEIO(lean_box(0));
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0(lean_object* v_msg_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v_toApplicative_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_225_; 
v___x_162_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__0);
v___x_163_ = l_StateRefT_x27_instMonad___redArg(v___x_162_);
v_toApplicative_164_ = lean_ctor_get(v___x_163_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_225_ == 0)
{
lean_object* v_unused_226_; 
v_unused_226_ = lean_ctor_get(v___x_163_, 1);
lean_dec(v_unused_226_);
v___x_166_ = v___x_163_;
v_isShared_167_ = v_isSharedCheck_225_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_toApplicative_164_);
lean_dec(v___x_163_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_225_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v_toFunctor_168_; lean_object* v_toSeq_169_; lean_object* v_toSeqLeft_170_; lean_object* v_toSeqRight_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_223_; 
v_toFunctor_168_ = lean_ctor_get(v_toApplicative_164_, 0);
v_toSeq_169_ = lean_ctor_get(v_toApplicative_164_, 2);
v_toSeqLeft_170_ = lean_ctor_get(v_toApplicative_164_, 3);
v_toSeqRight_171_ = lean_ctor_get(v_toApplicative_164_, 4);
v_isSharedCheck_223_ = !lean_is_exclusive(v_toApplicative_164_);
if (v_isSharedCheck_223_ == 0)
{
lean_object* v_unused_224_; 
v_unused_224_ = lean_ctor_get(v_toApplicative_164_, 1);
lean_dec(v_unused_224_);
v___x_173_ = v_toApplicative_164_;
v_isShared_174_ = v_isSharedCheck_223_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_toSeqRight_171_);
lean_inc(v_toSeqLeft_170_);
lean_inc(v_toSeq_169_);
lean_inc(v_toFunctor_168_);
lean_dec(v_toApplicative_164_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_223_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___f_175_; lean_object* v___f_176_; lean_object* v___f_177_; lean_object* v___f_178_; lean_object* v___x_179_; lean_object* v___f_180_; lean_object* v___f_181_; lean_object* v___f_182_; lean_object* v___x_184_; 
v___f_175_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__1));
v___f_176_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_168_);
v___f_177_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_177_, 0, v_toFunctor_168_);
v___f_178_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_178_, 0, v_toFunctor_168_);
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v___f_177_);
lean_ctor_set(v___x_179_, 1, v___f_178_);
v___f_180_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_180_, 0, v_toSeqRight_171_);
v___f_181_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_181_, 0, v_toSeqLeft_170_);
v___f_182_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_182_, 0, v_toSeq_169_);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 4, v___f_180_);
lean_ctor_set(v___x_173_, 3, v___f_181_);
lean_ctor_set(v___x_173_, 2, v___f_182_);
lean_ctor_set(v___x_173_, 1, v___f_175_);
lean_ctor_set(v___x_173_, 0, v___x_179_);
v___x_184_ = v___x_173_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_179_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v___f_175_);
lean_ctor_set(v_reuseFailAlloc_222_, 2, v___f_182_);
lean_ctor_set(v_reuseFailAlloc_222_, 3, v___f_181_);
lean_ctor_set(v_reuseFailAlloc_222_, 4, v___f_180_);
v___x_184_ = v_reuseFailAlloc_222_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
lean_object* v___x_186_; 
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v___f_176_);
lean_ctor_set(v___x_166_, 0, v___x_184_);
v___x_186_ = v___x_166_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v___x_184_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v___f_176_);
v___x_186_ = v_reuseFailAlloc_221_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
lean_object* v___x_187_; lean_object* v_toApplicative_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_219_; 
v___x_187_ = l_StateRefT_x27_instMonad___redArg(v___x_186_);
v_toApplicative_188_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_219_ == 0)
{
lean_object* v_unused_220_; 
v_unused_220_ = lean_ctor_get(v___x_187_, 1);
lean_dec(v_unused_220_);
v___x_190_ = v___x_187_;
v_isShared_191_ = v_isSharedCheck_219_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_toApplicative_188_);
lean_dec(v___x_187_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_219_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v_toFunctor_192_; lean_object* v_toSeq_193_; lean_object* v_toSeqLeft_194_; lean_object* v_toSeqRight_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_217_; 
v_toFunctor_192_ = lean_ctor_get(v_toApplicative_188_, 0);
v_toSeq_193_ = lean_ctor_get(v_toApplicative_188_, 2);
v_toSeqLeft_194_ = lean_ctor_get(v_toApplicative_188_, 3);
v_toSeqRight_195_ = lean_ctor_get(v_toApplicative_188_, 4);
v_isSharedCheck_217_ = !lean_is_exclusive(v_toApplicative_188_);
if (v_isSharedCheck_217_ == 0)
{
lean_object* v_unused_218_; 
v_unused_218_ = lean_ctor_get(v_toApplicative_188_, 1);
lean_dec(v_unused_218_);
v___x_197_ = v_toApplicative_188_;
v_isShared_198_ = v_isSharedCheck_217_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_toSeqRight_195_);
lean_inc(v_toSeqLeft_194_);
lean_inc(v_toSeq_193_);
lean_inc(v_toFunctor_192_);
lean_dec(v_toApplicative_188_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_217_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___f_199_; lean_object* v___f_200_; lean_object* v___f_201_; lean_object* v___f_202_; lean_object* v___x_203_; lean_object* v___f_204_; lean_object* v___f_205_; lean_object* v___f_206_; lean_object* v___x_208_; 
v___f_199_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__3));
v___f_200_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___closed__4));
lean_inc_ref(v_toFunctor_192_);
v___f_201_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_201_, 0, v_toFunctor_192_);
v___f_202_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_202_, 0, v_toFunctor_192_);
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v___f_201_);
lean_ctor_set(v___x_203_, 1, v___f_202_);
v___f_204_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_204_, 0, v_toSeqRight_195_);
v___f_205_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_205_, 0, v_toSeqLeft_194_);
v___f_206_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_206_, 0, v_toSeq_193_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 4, v___f_204_);
lean_ctor_set(v___x_197_, 3, v___f_205_);
lean_ctor_set(v___x_197_, 2, v___f_206_);
lean_ctor_set(v___x_197_, 1, v___f_199_);
lean_ctor_set(v___x_197_, 0, v___x_203_);
v___x_208_ = v___x_197_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_203_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v___f_199_);
lean_ctor_set(v_reuseFailAlloc_216_, 2, v___f_206_);
lean_ctor_set(v_reuseFailAlloc_216_, 3, v___f_205_);
lean_ctor_set(v_reuseFailAlloc_216_, 4, v___f_204_);
v___x_208_ = v_reuseFailAlloc_216_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
lean_object* v___x_210_; 
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 1, v___f_200_);
lean_ctor_set(v___x_190_, 0, v___x_208_);
v___x_210_ = v___x_190_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_208_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v___f_200_);
v___x_210_ = v_reuseFailAlloc_215_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_10537__overap_213_; lean_object* v___x_214_; 
v___x_211_ = lean_box(0);
v___x_212_ = l_instInhabitedOfMonad___redArg(v___x_210_, v___x_211_);
v___x_10537__overap_213_ = lean_panic_fn_borrowed(v___x_212_, v_msg_156_);
lean_dec(v___x_212_);
lean_inc(v___y_160_);
lean_inc_ref(v___y_159_);
lean_inc(v___y_158_);
lean_inc_ref(v___y_157_);
v___x_214_ = lean_apply_5(v___x_10537__overap_213_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, lean_box(0));
return v___x_214_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0___boxed(lean_object* v_msg_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0(v_msg_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(lean_object* v_msgData_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v___x_240_; lean_object* v_env_241_; lean_object* v___x_242_; lean_object* v_toCold_243_; lean_object* v_mctx_244_; lean_object* v_lctx_245_; lean_object* v_options_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_240_ = lean_st_ref_get(v___y_238_);
v_env_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc_ref(v_env_241_);
lean_dec(v___x_240_);
v___x_242_ = lean_st_ref_get(v___y_236_);
v_toCold_243_ = lean_ctor_get(v___y_237_, 0);
v_mctx_244_ = lean_ctor_get(v___x_242_, 0);
lean_inc_ref(v_mctx_244_);
lean_dec(v___x_242_);
v_lctx_245_ = lean_ctor_get(v___y_235_, 2);
v_options_246_ = lean_ctor_get(v_toCold_243_, 2);
lean_inc_ref(v_options_246_);
lean_inc_ref(v_lctx_245_);
v___x_247_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_247_, 0, v_env_241_);
lean_ctor_set(v___x_247_, 1, v_mctx_244_);
lean_ctor_set(v___x_247_, 2, v_lctx_245_);
lean_ctor_set(v___x_247_, 3, v_options_246_);
v___x_248_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
lean_ctor_set(v___x_248_, 1, v_msgData_234_);
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
v_ref_263_ = lean_ctor_get(v___y_260_, 2);
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
lean_dec_ref_known(v___x_313_, 1);
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
lean_dec_ref_known(v_a_327_, 1);
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
lean_dec_ref_known(v___x_362_, 1);
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
lean_dec_ref_known(v___x_411_, 1);
if (lean_obj_tag(v_a_412_) == 1)
{
lean_object* v_val_413_; lean_object* v_toConstantVal_414_; lean_object* v_cidx_415_; lean_object* v_name_416_; uint8_t v___x_417_; 
v_val_413_ = lean_ctor_get(v_a_412_, 0);
lean_inc(v_val_413_);
lean_dec_ref_known(v_a_412_, 1);
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
lean_dec_ref_known(v___x_418_, 1);
v_sz_420_ = lean_array_size(v_insterestingCtors_398_);
v___x_421_ = ((size_t)0ULL);
v___x_422_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_reduceSparseCasesOn_spec__2(v_sz_420_, v___x_421_, v_insterestingCtors_398_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_a_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v_a_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_a_423_);
lean_dec_ref_known(v___x_422_, 1);
v___x_424_ = l_Lean_mkRawNatLit(v_cidx_415_);
v___x_425_ = l_Lean_mkHasNotBitProof(v___x_424_, v_a_423_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
lean_dec(v_a_423_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_a_426_; lean_object* v___x_427_; lean_object* v_nargs_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v_dummy_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_a_426_);
lean_dec_ref_known(v___x_425_, 1);
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
uint8_t v___x_14226__boxed_561_; lean_object* v_res_562_; 
v___x_14226__boxed_561_ = lean_unbox(v___x_554_);
v_res_562_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(v___x_14226__boxed_561_, v___f_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
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
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11(lean_object* v_e_581_){
_start:
{
if (lean_obj_tag(v_e_581_) == 0)
{
uint8_t v___x_582_; 
v___x_582_ = 2;
return v___x_582_;
}
else
{
uint8_t v___x_583_; 
v___x_583_ = 0;
return v___x_583_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11___boxed(lean_object* v_e_584_){
_start:
{
uint8_t v_res_585_; lean_object* v_r_586_; 
v_res_585_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11(v_e_584_);
lean_dec_ref(v_e_584_);
v_r_586_ = lean_box(v_res_585_);
return v_r_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12(lean_object* v_opts_587_, lean_object* v_opt_588_){
_start:
{
lean_object* v_name_589_; lean_object* v_defValue_590_; lean_object* v_map_591_; lean_object* v___x_592_; 
v_name_589_ = lean_ctor_get(v_opt_588_, 0);
v_defValue_590_ = lean_ctor_get(v_opt_588_, 1);
v_map_591_ = lean_ctor_get(v_opts_587_, 0);
v___x_592_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_591_, v_name_589_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_inc(v_defValue_590_);
return v_defValue_590_;
}
else
{
lean_object* v_val_593_; 
v_val_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_val_593_);
lean_dec_ref_known(v___x_592_, 1);
if (lean_obj_tag(v_val_593_) == 3)
{
lean_object* v_v_594_; 
v_v_594_ = lean_ctor_get(v_val_593_, 0);
lean_inc(v_v_594_);
lean_dec_ref_known(v_val_593_, 1);
return v_v_594_;
}
else
{
lean_dec(v_val_593_);
lean_inc(v_defValue_590_);
return v_defValue_590_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12___boxed(lean_object* v_opts_595_, lean_object* v_opt_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12(v_opts_595_, v_opt_596_);
lean_dec_ref(v_opt_596_);
lean_dec_ref(v_opts_595_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg(lean_object* v_x_598_){
_start:
{
if (lean_obj_tag(v_x_598_) == 0)
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
v_a_600_ = lean_ctor_get(v_x_598_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v_x_598_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v_x_598_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v_x_598_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
lean_ctor_set_tag(v___x_602_, 1);
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
else
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
v_a_608_ = lean_ctor_get(v_x_598_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v_x_598_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v_x_598_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v_x_598_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
lean_ctor_set_tag(v___x_610_, 0);
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_608_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg___boxed(lean_object* v_x_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg(v_x_616_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9_spec__10(size_t v_sz_619_, size_t v_i_620_, lean_object* v_bs_621_){
_start:
{
uint8_t v___x_622_; 
v___x_622_ = lean_usize_dec_lt(v_i_620_, v_sz_619_);
if (v___x_622_ == 0)
{
return v_bs_621_;
}
else
{
lean_object* v_v_623_; lean_object* v_msg_624_; lean_object* v___x_625_; lean_object* v_bs_x27_626_; size_t v___x_627_; size_t v___x_628_; lean_object* v___x_629_; 
v_v_623_ = lean_array_uget_borrowed(v_bs_621_, v_i_620_);
v_msg_624_ = lean_ctor_get(v_v_623_, 1);
lean_inc_ref(v_msg_624_);
v___x_625_ = lean_unsigned_to_nat(0u);
v_bs_x27_626_ = lean_array_uset(v_bs_621_, v_i_620_, v___x_625_);
v___x_627_ = ((size_t)1ULL);
v___x_628_ = lean_usize_add(v_i_620_, v___x_627_);
v___x_629_ = lean_array_uset(v_bs_x27_626_, v_i_620_, v_msg_624_);
v_i_620_ = v___x_628_;
v_bs_621_ = v___x_629_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9_spec__10___boxed(lean_object* v_sz_631_, lean_object* v_i_632_, lean_object* v_bs_633_){
_start:
{
size_t v_sz_boxed_634_; size_t v_i_boxed_635_; lean_object* v_res_636_; 
v_sz_boxed_634_ = lean_unbox_usize(v_sz_631_);
lean_dec(v_sz_631_);
v_i_boxed_635_ = lean_unbox_usize(v_i_632_);
lean_dec(v_i_632_);
v_res_636_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9_spec__10(v_sz_boxed_634_, v_i_boxed_635_, v_bs_633_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9(lean_object* v_oldTraces_637_, lean_object* v_data_638_, lean_object* v_ref_639_, lean_object* v_msg_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v_toCold_646_; lean_object* v_currRecDepth_647_; lean_object* v_ref_648_; uint8_t v_diag_649_; uint8_t v_suppressElabErrors_650_; lean_object* v___x_651_; lean_object* v_traceState_652_; lean_object* v_traces_653_; lean_object* v_ref_654_; lean_object* v___x_655_; lean_object* v___x_656_; size_t v_sz_657_; size_t v___x_658_; lean_object* v___x_659_; lean_object* v_msg_660_; lean_object* v___x_661_; lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_699_; 
v_toCold_646_ = lean_ctor_get(v___y_643_, 0);
v_currRecDepth_647_ = lean_ctor_get(v___y_643_, 1);
v_ref_648_ = lean_ctor_get(v___y_643_, 2);
v_diag_649_ = lean_ctor_get_uint8(v___y_643_, sizeof(void*)*3);
v_suppressElabErrors_650_ = lean_ctor_get_uint8(v___y_643_, sizeof(void*)*3 + 1);
v___x_651_ = lean_st_ref_get(v___y_644_);
v_traceState_652_ = lean_ctor_get(v___x_651_, 4);
lean_inc_ref(v_traceState_652_);
lean_dec(v___x_651_);
v_traces_653_ = lean_ctor_get(v_traceState_652_, 0);
lean_inc_ref(v_traces_653_);
lean_dec_ref(v_traceState_652_);
v_ref_654_ = l_Lean_replaceRef(v_ref_639_, v_ref_648_);
lean_inc(v_currRecDepth_647_);
lean_inc_ref(v_toCold_646_);
v___x_655_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_655_, 0, v_toCold_646_);
lean_ctor_set(v___x_655_, 1, v_currRecDepth_647_);
lean_ctor_set(v___x_655_, 2, v_ref_654_);
lean_ctor_set_uint8(v___x_655_, sizeof(void*)*3, v_diag_649_);
lean_ctor_set_uint8(v___x_655_, sizeof(void*)*3 + 1, v_suppressElabErrors_650_);
v___x_656_ = l_Lean_PersistentArray_toArray___redArg(v_traces_653_);
lean_dec_ref(v_traces_653_);
v_sz_657_ = lean_array_size(v___x_656_);
v___x_658_ = ((size_t)0ULL);
v___x_659_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9_spec__10(v_sz_657_, v___x_658_, v___x_656_);
v_msg_660_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_660_, 0, v_data_638_);
lean_ctor_set(v_msg_660_, 1, v_msg_640_);
lean_ctor_set(v_msg_660_, 2, v___x_659_);
v___x_661_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msg_660_, v___y_641_, v___y_642_, v___x_655_, v___y_644_);
lean_dec_ref_known(v___x_655_, 3);
v_a_662_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_699_ == 0)
{
v___x_664_ = v___x_661_;
v_isShared_665_ = v_isSharedCheck_699_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_661_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_699_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_666_; lean_object* v_traceState_667_; lean_object* v_env_668_; lean_object* v_nextMacroScope_669_; lean_object* v_ngen_670_; lean_object* v_auxDeclNGen_671_; lean_object* v_cache_672_; lean_object* v_messages_673_; lean_object* v_infoState_674_; lean_object* v_snapshotTasks_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_698_; 
v___x_666_ = lean_st_ref_take(v___y_644_);
v_traceState_667_ = lean_ctor_get(v___x_666_, 4);
v_env_668_ = lean_ctor_get(v___x_666_, 0);
v_nextMacroScope_669_ = lean_ctor_get(v___x_666_, 1);
v_ngen_670_ = lean_ctor_get(v___x_666_, 2);
v_auxDeclNGen_671_ = lean_ctor_get(v___x_666_, 3);
v_cache_672_ = lean_ctor_get(v___x_666_, 5);
v_messages_673_ = lean_ctor_get(v___x_666_, 6);
v_infoState_674_ = lean_ctor_get(v___x_666_, 7);
v_snapshotTasks_675_ = lean_ctor_get(v___x_666_, 8);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_698_ == 0)
{
v___x_677_ = v___x_666_;
v_isShared_678_ = v_isSharedCheck_698_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_snapshotTasks_675_);
lean_inc(v_infoState_674_);
lean_inc(v_messages_673_);
lean_inc(v_cache_672_);
lean_inc(v_traceState_667_);
lean_inc(v_auxDeclNGen_671_);
lean_inc(v_ngen_670_);
lean_inc(v_nextMacroScope_669_);
lean_inc(v_env_668_);
lean_dec(v___x_666_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_698_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
uint64_t v_tid_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_696_; 
v_tid_679_ = lean_ctor_get_uint64(v_traceState_667_, sizeof(void*)*1);
v_isSharedCheck_696_ = !lean_is_exclusive(v_traceState_667_);
if (v_isSharedCheck_696_ == 0)
{
lean_object* v_unused_697_; 
v_unused_697_ = lean_ctor_get(v_traceState_667_, 0);
lean_dec(v_unused_697_);
v___x_681_ = v_traceState_667_;
v_isShared_682_ = v_isSharedCheck_696_;
goto v_resetjp_680_;
}
else
{
lean_dec(v_traceState_667_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_696_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_686_; 
v___x_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_683_, 0, v_ref_639_);
lean_ctor_set(v___x_683_, 1, v_a_662_);
v___x_684_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_637_, v___x_683_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v___x_684_);
v___x_686_ = v___x_681_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_684_);
lean_ctor_set_uint64(v_reuseFailAlloc_695_, sizeof(void*)*1, v_tid_679_);
v___x_686_ = v_reuseFailAlloc_695_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
lean_object* v___x_688_; 
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 4, v___x_686_);
v___x_688_ = v___x_677_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_env_668_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_nextMacroScope_669_);
lean_ctor_set(v_reuseFailAlloc_694_, 2, v_ngen_670_);
lean_ctor_set(v_reuseFailAlloc_694_, 3, v_auxDeclNGen_671_);
lean_ctor_set(v_reuseFailAlloc_694_, 4, v___x_686_);
lean_ctor_set(v_reuseFailAlloc_694_, 5, v_cache_672_);
lean_ctor_set(v_reuseFailAlloc_694_, 6, v_messages_673_);
lean_ctor_set(v_reuseFailAlloc_694_, 7, v_infoState_674_);
lean_ctor_set(v_reuseFailAlloc_694_, 8, v_snapshotTasks_675_);
v___x_688_ = v_reuseFailAlloc_694_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_692_; 
v___x_689_ = lean_st_ref_put(v___y_644_, v___x_688_);
v___x_690_ = lean_box(0);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v___x_690_);
v___x_692_ = v___x_664_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_690_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9___boxed(lean_object* v_oldTraces_700_, lean_object* v_data_701_, lean_object* v_ref_702_, lean_object* v_msg_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9(v_oldTraces_700_, v_data_701_, v_ref_702_, v_msg_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
return v_res_709_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0(void){
_start:
{
lean_object* v___x_710_; double v___x_711_; 
v___x_710_ = lean_unsigned_to_nat(0u);
v___x_711_ = lean_float_of_nat(v___x_710_);
return v___x_711_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2(void){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__1));
v___x_714_ = l_Lean_stringToMessageData(v___x_713_);
return v___x_714_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__3(void){
_start:
{
lean_object* v___x_715_; double v___x_716_; 
v___x_715_ = lean_unsigned_to_nat(1000u);
v___x_716_ = lean_float_of_nat(v___x_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(lean_object* v_cls_717_, uint8_t v_collapsed_718_, lean_object* v_tag_719_, lean_object* v_opts_720_, uint8_t v_clsEnabled_721_, lean_object* v_oldTraces_722_, lean_object* v_msg_723_, lean_object* v_resStartStop_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v_fst_730_; lean_object* v_snd_731_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v_data_735_; lean_object* v_fst_746_; lean_object* v_snd_747_; lean_object* v___x_748_; uint8_t v___x_749_; lean_object* v___y_751_; lean_object* v_a_752_; uint8_t v___y_767_; double v___y_798_; 
v_fst_730_ = lean_ctor_get(v_resStartStop_724_, 0);
lean_inc(v_fst_730_);
v_snd_731_ = lean_ctor_get(v_resStartStop_724_, 1);
lean_inc(v_snd_731_);
lean_dec_ref(v_resStartStop_724_);
v_fst_746_ = lean_ctor_get(v_snd_731_, 0);
lean_inc(v_fst_746_);
v_snd_747_ = lean_ctor_get(v_snd_731_, 1);
lean_inc(v_snd_747_);
lean_dec(v_snd_731_);
v___x_748_ = l_Lean_trace_profiler;
v___x_749_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_opts_720_, v___x_748_);
if (v___x_749_ == 0)
{
v___y_767_ = v___x_749_;
goto v___jp_766_;
}
else
{
lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_803_ = l_Lean_trace_profiler_useHeartbeats;
v___x_804_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_opts_720_, v___x_803_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; lean_object* v___x_806_; double v___x_807_; double v___x_808_; double v___x_809_; 
v___x_805_ = l_Lean_trace_profiler_threshold;
v___x_806_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12(v_opts_720_, v___x_805_);
v___x_807_ = lean_float_of_nat(v___x_806_);
v___x_808_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__3);
v___x_809_ = lean_float_div(v___x_807_, v___x_808_);
v___y_798_ = v___x_809_;
goto v___jp_797_;
}
else
{
lean_object* v___x_810_; lean_object* v___x_811_; double v___x_812_; 
v___x_810_ = l_Lean_trace_profiler_threshold;
v___x_811_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12(v_opts_720_, v___x_810_);
v___x_812_ = lean_float_of_nat(v___x_811_);
v___y_798_ = v___x_812_;
goto v___jp_797_;
}
}
v___jp_732_:
{
lean_object* v___x_736_; 
lean_inc(v___y_733_);
v___x_736_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9(v_oldTraces_722_, v_data_735_, v___y_733_, v___y_734_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v___x_737_; 
lean_dec_ref_known(v___x_736_, 1);
v___x_737_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg(v_fst_730_);
return v___x_737_;
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec(v_fst_730_);
v_a_738_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_736_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_736_);
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
v___jp_750_:
{
uint8_t v_result_753_; lean_object* v___x_754_; lean_object* v___x_755_; double v___x_756_; lean_object* v_data_757_; 
v_result_753_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11(v_fst_730_);
v___x_754_ = lean_box(v_result_753_);
v___x_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
v___x_756_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0);
lean_inc_ref(v_tag_719_);
lean_inc_ref(v___x_755_);
lean_inc(v_cls_717_);
v_data_757_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_757_, 0, v_cls_717_);
lean_ctor_set(v_data_757_, 1, v___x_755_);
lean_ctor_set(v_data_757_, 2, v_tag_719_);
lean_ctor_set_float(v_data_757_, sizeof(void*)*3, v___x_756_);
lean_ctor_set_float(v_data_757_, sizeof(void*)*3 + 8, v___x_756_);
lean_ctor_set_uint8(v_data_757_, sizeof(void*)*3 + 16, v_collapsed_718_);
if (v___x_749_ == 0)
{
lean_dec_ref_known(v___x_755_, 1);
lean_dec(v_snd_747_);
lean_dec(v_fst_746_);
lean_dec_ref(v_tag_719_);
lean_dec(v_cls_717_);
v___y_733_ = v___y_751_;
v___y_734_ = v_a_752_;
v_data_735_ = v_data_757_;
goto v___jp_732_;
}
else
{
lean_object* v_data_758_; double v___x_759_; double v___x_760_; 
lean_dec_ref_known(v_data_757_, 3);
v_data_758_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_758_, 0, v_cls_717_);
lean_ctor_set(v_data_758_, 1, v___x_755_);
lean_ctor_set(v_data_758_, 2, v_tag_719_);
v___x_759_ = lean_unbox_float(v_fst_746_);
lean_dec(v_fst_746_);
lean_ctor_set_float(v_data_758_, sizeof(void*)*3, v___x_759_);
v___x_760_ = lean_unbox_float(v_snd_747_);
lean_dec(v_snd_747_);
lean_ctor_set_float(v_data_758_, sizeof(void*)*3 + 8, v___x_760_);
lean_ctor_set_uint8(v_data_758_, sizeof(void*)*3 + 16, v_collapsed_718_);
v___y_733_ = v___y_751_;
v___y_734_ = v_a_752_;
v_data_735_ = v_data_758_;
goto v___jp_732_;
}
}
v___jp_761_:
{
lean_object* v_ref_762_; lean_object* v___x_763_; 
v_ref_762_ = lean_ctor_get(v___y_727_, 2);
lean_inc(v___y_728_);
lean_inc_ref(v___y_727_);
lean_inc(v___y_726_);
lean_inc_ref(v___y_725_);
lean_inc(v_fst_730_);
v___x_763_ = lean_apply_6(v_msg_723_, v_fst_730_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, lean_box(0));
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_763_, 1);
v___y_751_ = v_ref_762_;
v_a_752_ = v_a_764_;
goto v___jp_750_;
}
else
{
lean_object* v___x_765_; 
lean_dec_ref_known(v___x_763_, 1);
v___x_765_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2);
v___y_751_ = v_ref_762_;
v_a_752_ = v___x_765_;
goto v___jp_750_;
}
}
v___jp_766_:
{
if (v_clsEnabled_721_ == 0)
{
if (v___y_767_ == 0)
{
lean_object* v___x_768_; lean_object* v_traceState_769_; lean_object* v_env_770_; lean_object* v_nextMacroScope_771_; lean_object* v_ngen_772_; lean_object* v_auxDeclNGen_773_; lean_object* v_cache_774_; lean_object* v_messages_775_; lean_object* v_infoState_776_; lean_object* v_snapshotTasks_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_796_; 
lean_dec(v_snd_747_);
lean_dec(v_fst_746_);
lean_dec_ref(v_msg_723_);
lean_dec_ref(v_tag_719_);
lean_dec(v_cls_717_);
v___x_768_ = lean_st_ref_take(v___y_728_);
v_traceState_769_ = lean_ctor_get(v___x_768_, 4);
v_env_770_ = lean_ctor_get(v___x_768_, 0);
v_nextMacroScope_771_ = lean_ctor_get(v___x_768_, 1);
v_ngen_772_ = lean_ctor_get(v___x_768_, 2);
v_auxDeclNGen_773_ = lean_ctor_get(v___x_768_, 3);
v_cache_774_ = lean_ctor_get(v___x_768_, 5);
v_messages_775_ = lean_ctor_get(v___x_768_, 6);
v_infoState_776_ = lean_ctor_get(v___x_768_, 7);
v_snapshotTasks_777_ = lean_ctor_get(v___x_768_, 8);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_796_ == 0)
{
v___x_779_ = v___x_768_;
v_isShared_780_ = v_isSharedCheck_796_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_snapshotTasks_777_);
lean_inc(v_infoState_776_);
lean_inc(v_messages_775_);
lean_inc(v_cache_774_);
lean_inc(v_traceState_769_);
lean_inc(v_auxDeclNGen_773_);
lean_inc(v_ngen_772_);
lean_inc(v_nextMacroScope_771_);
lean_inc(v_env_770_);
lean_dec(v___x_768_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_796_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
uint64_t v_tid_781_; lean_object* v_traces_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_795_; 
v_tid_781_ = lean_ctor_get_uint64(v_traceState_769_, sizeof(void*)*1);
v_traces_782_ = lean_ctor_get(v_traceState_769_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v_traceState_769_);
if (v_isSharedCheck_795_ == 0)
{
v___x_784_ = v_traceState_769_;
v_isShared_785_ = v_isSharedCheck_795_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_traces_782_);
lean_dec(v_traceState_769_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_795_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_786_; lean_object* v___x_788_; 
v___x_786_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_722_, v_traces_782_);
lean_dec_ref(v_traces_782_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v___x_786_);
v___x_788_ = v___x_784_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_786_);
lean_ctor_set_uint64(v_reuseFailAlloc_794_, sizeof(void*)*1, v_tid_781_);
v___x_788_ = v_reuseFailAlloc_794_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
lean_object* v___x_790_; 
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 4, v___x_788_);
v___x_790_ = v___x_779_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_env_770_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_nextMacroScope_771_);
lean_ctor_set(v_reuseFailAlloc_793_, 2, v_ngen_772_);
lean_ctor_set(v_reuseFailAlloc_793_, 3, v_auxDeclNGen_773_);
lean_ctor_set(v_reuseFailAlloc_793_, 4, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_793_, 5, v_cache_774_);
lean_ctor_set(v_reuseFailAlloc_793_, 6, v_messages_775_);
lean_ctor_set(v_reuseFailAlloc_793_, 7, v_infoState_776_);
lean_ctor_set(v_reuseFailAlloc_793_, 8, v_snapshotTasks_777_);
v___x_790_ = v_reuseFailAlloc_793_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = lean_st_ref_put(v___y_728_, v___x_790_);
v___x_792_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg(v_fst_730_);
return v___x_792_;
}
}
}
}
}
else
{
goto v___jp_761_;
}
}
else
{
goto v___jp_761_;
}
}
v___jp_797_:
{
double v___x_799_; double v___x_800_; double v___x_801_; uint8_t v___x_802_; 
v___x_799_ = lean_unbox_float(v_snd_747_);
v___x_800_ = lean_unbox_float(v_fst_746_);
v___x_801_ = lean_float_sub(v___x_799_, v___x_800_);
v___x_802_ = lean_float_decLt(v___y_798_, v___x_801_);
v___y_767_ = v___x_802_;
goto v___jp_766_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___boxed(lean_object* v_cls_813_, lean_object* v_collapsed_814_, lean_object* v_tag_815_, lean_object* v_opts_816_, lean_object* v_clsEnabled_817_, lean_object* v_oldTraces_818_, lean_object* v_msg_819_, lean_object* v_resStartStop_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
uint8_t v_collapsed_boxed_826_; uint8_t v_clsEnabled_boxed_827_; lean_object* v_res_828_; 
v_collapsed_boxed_826_ = lean_unbox(v_collapsed_814_);
v_clsEnabled_boxed_827_ = lean_unbox(v_clsEnabled_817_);
v_res_828_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v_cls_813_, v_collapsed_boxed_826_, v_tag_815_, v_opts_816_, v_clsEnabled_boxed_827_, v_oldTraces_818_, v_msg_819_, v_resStartStop_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec_ref(v_opts_816_);
return v_res_828_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9(void){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_842_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5));
v___x_843_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__8));
v___x_844_ = l_Lean_Name_append(v___x_843_, v___x_842_);
return v___x_844_;
}
}
static double _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10(void){
_start:
{
lean_object* v___x_845_; double v___x_846_; 
v___x_845_ = lean_unsigned_to_nat(1000000000u);
v___x_846_ = lean_float_of_nat(v___x_845_);
return v___x_846_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12(void){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__11));
v___x_849_ = l_Lean_stringToMessageData(v___x_848_);
return v___x_849_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14(void){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__13));
v___x_852_ = l_Lean_stringToMessageData(v___x_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7(lean_object* v_snd_853_, lean_object* v_mvarId_854_, lean_object* v_x_855_, lean_object* v_x_856_, lean_object* v_x_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
if (lean_obj_tag(v_x_855_) == 5)
{
lean_object* v_fn_863_; lean_object* v_arg_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v_fn_863_ = lean_ctor_get(v_x_855_, 0);
lean_inc_ref(v_fn_863_);
v_arg_864_ = lean_ctor_get(v_x_855_, 1);
lean_inc_ref(v_arg_864_);
lean_dec_ref_known(v_x_855_, 2);
v___x_865_ = lean_array_set(v_x_856_, v_x_857_, v_arg_864_);
v___x_866_ = lean_unsigned_to_nat(1u);
v___x_867_ = lean_nat_sub(v_x_857_, v___x_866_);
lean_dec(v_x_857_);
v_x_855_ = v_fn_863_;
v_x_856_ = v___x_865_;
v_x_857_ = v___x_867_;
goto _start;
}
else
{
lean_dec(v_x_857_);
if (lean_obj_tag(v_x_855_) == 4)
{
lean_object* v_declName_869_; lean_object* v___x_870_; 
v_declName_869_ = lean_ctor_get(v_x_855_, 0);
lean_inc_n(v_declName_869_, 2);
lean_dec_ref_known(v_x_855_, 2);
v___x_870_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_declName_869_, v___y_861_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_a_871_);
lean_dec_ref_known(v___x_870_, 1);
if (lean_obj_tag(v_a_871_) == 1)
{
lean_object* v_val_872_; lean_object* v_toCold_873_; lean_object* v_options_874_; lean_object* v_majorPos_875_; lean_object* v_arity_876_; lean_object* v_insterestingCtors_877_; lean_object* v_inheritedTraceOptions_878_; uint8_t v_hasTrace_879_; lean_object* v___f_880_; lean_object* v___x_881_; lean_object* v___f_882_; lean_object* v___x_883_; uint8_t v___x_884_; 
v_val_872_ = lean_ctor_get(v_a_871_, 0);
lean_inc(v_val_872_);
lean_dec_ref_known(v_a_871_, 1);
v_toCold_873_ = lean_ctor_get(v___y_860_, 0);
v_options_874_ = lean_ctor_get(v_toCold_873_, 2);
v_majorPos_875_ = lean_ctor_get(v_val_872_, 1);
lean_inc(v_majorPos_875_);
v_arity_876_ = lean_ctor_get(v_val_872_, 2);
lean_inc_n(v_arity_876_, 2);
v_insterestingCtors_877_ = lean_ctor_get(v_val_872_, 3);
lean_inc_ref(v_insterestingCtors_877_);
lean_dec(v_val_872_);
v_inheritedTraceOptions_878_ = lean_ctor_get(v_toCold_873_, 11);
v_hasTrace_879_ = lean_ctor_get_uint8(v_options_874_, sizeof(void*)*1);
v___f_880_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0));
v___x_881_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_x_856_);
v___f_882_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___boxed), 15, 9);
lean_closure_set(v___f_882_, 0, v___x_881_);
lean_closure_set(v___f_882_, 1, v_x_856_);
lean_closure_set(v___f_882_, 2, v_majorPos_875_);
lean_closure_set(v___f_882_, 3, v_insterestingCtors_877_);
lean_closure_set(v___f_882_, 4, v_declName_869_);
lean_closure_set(v___f_882_, 5, v_snd_853_);
lean_closure_set(v___f_882_, 6, v_arity_876_);
lean_closure_set(v___f_882_, 7, v_mvarId_854_);
lean_closure_set(v___f_882_, 8, v___f_880_);
v___x_883_ = lean_array_get_size(v_x_856_);
lean_dec_ref(v_x_856_);
v___x_884_ = lean_nat_dec_lt(v___x_883_, v_arity_876_);
lean_dec(v_arity_876_);
if (v_hasTrace_879_ == 0)
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(v___x_884_, v___f_882_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
return v___x_885_;
}
else
{
lean_object* v___f_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; uint8_t v___x_890_; lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v_a_894_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v_a_909_; 
v___f_886_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1));
v___x_887_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5));
v___x_888_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__6));
v___x_889_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9);
v___x_890_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_878_, v_options_874_, v___x_889_);
if (v___x_890_ == 0)
{
lean_object* v___x_959_; uint8_t v___x_960_; 
v___x_959_ = l_Lean_trace_profiler;
v___x_960_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_options_874_, v___x_959_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; 
v___x_961_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(v___x_884_, v___f_882_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
return v___x_961_;
}
else
{
goto v___jp_918_;
}
}
else
{
goto v___jp_918_;
}
v___jp_891_:
{
lean_object* v___x_895_; double v___x_896_; double v___x_897_; double v___x_898_; double v___x_899_; double v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_895_ = lean_io_mono_nanos_now();
v___x_896_ = lean_float_of_nat(v___y_892_);
v___x_897_ = lean_float_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10);
v___x_898_ = lean_float_div(v___x_896_, v___x_897_);
v___x_899_ = lean_float_of_nat(v___x_895_);
v___x_900_ = lean_float_div(v___x_899_, v___x_897_);
v___x_901_ = lean_box_float(v___x_898_);
v___x_902_ = lean_box_float(v___x_900_);
v___x_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_901_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v_a_894_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_887_, v_hasTrace_879_, v___x_888_, v_options_874_, v___x_890_, v___y_893_, v___f_886_, v___x_904_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
return v___x_905_;
}
v___jp_906_:
{
lean_object* v___x_910_; double v___x_911_; double v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_910_ = lean_io_get_num_heartbeats();
v___x_911_ = lean_float_of_nat(v___y_907_);
v___x_912_ = lean_float_of_nat(v___x_910_);
v___x_913_ = lean_box_float(v___x_911_);
v___x_914_ = lean_box_float(v___x_912_);
v___x_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_913_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v___x_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_916_, 0, v_a_909_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_887_, v_hasTrace_879_, v___x_888_, v_options_874_, v___x_890_, v___y_908_, v___f_886_, v___x_916_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
return v___x_917_;
}
v___jp_918_:
{
lean_object* v___x_919_; lean_object* v_a_920_; lean_object* v___x_921_; uint8_t v___x_922_; 
v___x_919_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___y_861_);
v_a_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_a_920_);
lean_dec_ref(v___x_919_);
v___x_921_ = l_Lean_trace_profiler_useHeartbeats;
v___x_922_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_options_874_, v___x_921_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = lean_io_mono_nanos_now();
v___x_924_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(v___x_884_, v___f_882_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_924_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_924_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
lean_ctor_set_tag(v___x_927_, 1);
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
v___y_892_ = v___x_923_;
v___y_893_ = v_a_920_;
v_a_894_ = v___x_930_;
goto v___jp_891_;
}
}
}
else
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
v_a_933_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_940_ == 0)
{
v___x_935_ = v___x_924_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_924_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
lean_ctor_set_tag(v___x_935_, 0);
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_933_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
v___y_892_ = v___x_923_;
v___y_893_ = v_a_920_;
v_a_894_ = v___x_938_;
goto v___jp_891_;
}
}
}
}
else
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = lean_io_get_num_heartbeats();
v___x_942_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(v___x_884_, v___f_882_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_950_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_950_ == 0)
{
v___x_945_ = v___x_942_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_942_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
lean_ctor_set_tag(v___x_945_, 1);
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_a_943_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
v___y_907_ = v___x_941_;
v___y_908_ = v_a_920_;
v_a_909_ = v___x_948_;
goto v___jp_906_;
}
}
}
else
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
v_a_951_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_958_ == 0)
{
v___x_953_ = v___x_942_;
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_942_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
lean_ctor_set_tag(v___x_953_, 0);
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_951_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
v___y_907_ = v___x_941_;
v___y_908_ = v_a_920_;
v_a_909_ = v___x_956_;
goto v___jp_906_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_962_; lean_object* v___x_963_; 
lean_dec(v_a_871_);
lean_dec(v_declName_869_);
lean_dec_ref(v_x_856_);
lean_dec(v_mvarId_854_);
lean_dec_ref(v_snd_853_);
v___x_962_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12);
v___x_963_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_962_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
return v___x_963_;
}
}
else
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_971_; 
lean_dec(v_declName_869_);
lean_dec_ref(v_x_856_);
lean_dec(v_mvarId_854_);
lean_dec_ref(v_snd_853_);
v_a_964_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_971_ == 0)
{
v___x_966_ = v___x_870_;
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_870_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_969_; 
if (v_isShared_967_ == 0)
{
v___x_969_ = v___x_966_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_a_964_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
else
{
lean_object* v___x_972_; lean_object* v___x_973_; 
lean_dec_ref(v_x_856_);
lean_dec_ref(v_x_855_);
lean_dec(v_mvarId_854_);
lean_dec_ref(v_snd_853_);
v___x_972_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14);
v___x_973_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_972_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
return v___x_973_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___boxed(lean_object* v_snd_974_, lean_object* v_mvarId_975_, lean_object* v_x_976_, lean_object* v_x_977_, lean_object* v_x_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7(v_snd_974_, v_mvarId_975_, v_x_976_, v_x_977_, v_x_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
return v_res_984_;
}
}
static lean_object* _init_l_Lean_Meta_reduceSparseCasesOn___closed__1(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = ((lean_object*)(l_Lean_Meta_reduceSparseCasesOn___closed__0));
v___x_987_ = l_Lean_stringToMessageData(v___x_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceSparseCasesOn(lean_object* v_mvarId_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_){
_start:
{
lean_object* v___x_994_; 
lean_inc(v_mvarId_988_);
v___x_994_ = l_Lean_MVarId_getType(v_mvarId_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v___x_996_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_a_995_);
lean_dec_ref_known(v___x_994_, 1);
v___x_996_ = l_Lean_Meta_matchEqHEqLHS_x3f(v_a_995_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
lean_inc(v_a_997_);
lean_dec_ref_known(v___x_996_, 1);
if (lean_obj_tag(v_a_997_) == 1)
{
lean_object* v_val_998_; lean_object* v_snd_999_; lean_object* v_dummy_1000_; lean_object* v_nargs_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v_val_998_ = lean_ctor_get(v_a_997_, 0);
lean_inc(v_val_998_);
lean_dec_ref_known(v_a_997_, 1);
v_snd_999_ = lean_ctor_get(v_val_998_, 1);
lean_inc_n(v_snd_999_, 2);
lean_dec(v_val_998_);
v_dummy_1000_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0);
v_nargs_1001_ = l_Lean_Expr_getAppNumArgs(v_snd_999_);
lean_inc(v_nargs_1001_);
v___x_1002_ = lean_mk_array(v_nargs_1001_, v_dummy_1000_);
v___x_1003_ = lean_unsigned_to_nat(1u);
v___x_1004_ = lean_nat_sub(v_nargs_1001_, v___x_1003_);
lean_dec(v_nargs_1001_);
v___x_1005_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7(v_snd_999_, v_mvarId_988_, v_snd_999_, v___x_1002_, v___x_1004_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
return v___x_1005_;
}
else
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
lean_dec(v_a_997_);
lean_dec(v_mvarId_988_);
v___x_1006_ = lean_obj_once(&l_Lean_Meta_reduceSparseCasesOn___closed__1, &l_Lean_Meta_reduceSparseCasesOn___closed__1_once, _init_l_Lean_Meta_reduceSparseCasesOn___closed__1);
v___x_1007_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1006_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
return v___x_1007_;
}
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
lean_dec(v_mvarId_988_);
v_a_1008_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_996_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_996_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
lean_dec(v_mvarId_988_);
v_a_1016_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_994_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_994_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceSparseCasesOn___boxed(lean_object* v_mvarId_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Lean_Meta_reduceSparseCasesOn(v_mvarId_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_);
lean_dec(v_a_1028_);
lean_dec_ref(v_a_1027_);
lean_dec(v_a_1026_);
lean_dec_ref(v_a_1025_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3(lean_object* v_00_u03b1_1031_, lean_object* v_msg_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v_msg_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___boxed(lean_object* v_00_u03b1_1039_, lean_object* v_msg_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3(v_00_u03b1_1039_, v_msg_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10(lean_object* v_00_u03b1_1047_, lean_object* v_x_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg(v_x_1048_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___boxed(lean_object* v_00_u03b1_1055_, lean_object* v_x_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10(v_00_u03b1_1055_, v_x_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(lean_object* v_mvarId_1063_, lean_object* v_x_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1063_, v_x_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_1070_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1070_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
v_a_1079_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1070_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1070_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg___boxed(lean_object* v_mvarId_1087_, lean_object* v_x_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1087_, v_x_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2(lean_object* v_00_u03b1_1095_, lean_object* v_mvarId_1096_, lean_object* v_x_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v___x_1103_; 
v___x_1103_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1096_, v_x_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___boxed(lean_object* v_00_u03b1_1104_, lean_object* v_mvarId_1105_, lean_object* v_x_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2(v_00_u03b1_1104_, v_mvarId_1105_, v_x_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_splitSparseCasesOn_spec__1(lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
if (lean_obj_tag(v_a_1113_) == 0)
{
lean_object* v___x_1115_; 
v___x_1115_ = l_List_reverse___redArg(v_a_1114_);
return v___x_1115_;
}
else
{
lean_object* v_head_1116_; lean_object* v_tail_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1126_; 
v_head_1116_ = lean_ctor_get(v_a_1113_, 0);
v_tail_1117_ = lean_ctor_get(v_a_1113_, 1);
v_isSharedCheck_1126_ = !lean_is_exclusive(v_a_1113_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1119_ = v_a_1113_;
v_isShared_1120_ = v_isSharedCheck_1126_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_tail_1117_);
lean_inc(v_head_1116_);
lean_dec(v_a_1113_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1126_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1121_; lean_object* v___x_1123_; 
v___x_1121_ = l_Lean_MessageData_ofExpr(v_head_1116_);
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 1, v_a_1114_);
lean_ctor_set(v___x_1119_, 0, v___x_1121_);
v___x_1123_ = v___x_1119_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1121_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v_a_1114_);
v___x_1123_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
v_a_1113_ = v_tail_1117_;
v_a_1114_ = v___x_1123_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__0));
v___x_1129_ = l_Lean_stringToMessageData(v___x_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0(uint8_t v___y_1130_, lean_object* v_mvarId_1131_, lean_object* v___f_1132_, lean_object* v_declName_1133_, lean_object* v_val_1134_, lean_object* v___x_1135_, lean_object* v_fields_1136_, uint8_t v___x_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; 
if (v___y_1130_ == 0)
{
lean_object* v___x_1199_; 
lean_dec_ref(v_fields_1136_);
lean_dec_ref(v_val_1134_);
lean_dec(v_declName_1133_);
v___x_1199_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_1131_, v___f_1132_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
return v___x_1199_;
}
else
{
lean_object* v___x_1200_; lean_object* v___x_1201_; uint8_t v___x_1202_; 
lean_dec_ref(v___f_1132_);
v___x_1200_ = lean_array_get_size(v_fields_1136_);
v___x_1201_ = lean_unsigned_to_nat(1u);
v___x_1202_ = lean_nat_dec_eq(v___x_1200_, v___x_1201_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1203_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1);
lean_inc_ref(v_fields_1136_);
v___x_1204_ = lean_array_to_list(v_fields_1136_);
v___x_1205_ = lean_box(0);
v___x_1206_ = l_List_mapTR_loop___at___00Lean_Meta_splitSparseCasesOn_spec__1(v___x_1204_, v___x_1205_);
v___x_1207_ = l_Lean_MessageData_ofList(v___x_1206_);
v___x_1208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1203_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
v___x_1209_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1208_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_dec_ref_known(v___x_1209_, 1);
v___y_1144_ = v___y_1138_;
v___y_1145_ = v___y_1139_;
v___y_1146_ = v___y_1140_;
v___y_1147_ = v___y_1141_;
goto v___jp_1143_;
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_dec_ref(v_fields_1136_);
lean_dec_ref(v_val_1134_);
lean_dec(v_declName_1133_);
lean_dec(v_mvarId_1131_);
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1209_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1209_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
else
{
v___y_1144_ = v___y_1138_;
v___y_1145_ = v___y_1139_;
v___y_1146_ = v___y_1140_;
v___y_1147_ = v___y_1141_;
goto v___jp_1143_;
}
}
v___jp_1143_:
{
lean_object* v___x_1148_; 
v___x_1148_ = l_Lean_Meta_getSparseCasesOnEq(v_declName_1133_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; lean_object* v___x_1150_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
lean_inc(v_a_1149_);
lean_dec_ref_known(v___x_1148_, 1);
lean_inc(v_mvarId_1131_);
v___x_1150_ = l_Lean_MVarId_getType(v_mvarId_1131_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_a_1151_; lean_object* v___x_1152_; 
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_a_1151_);
lean_dec_ref_known(v___x_1150_, 1);
v___x_1152_ = l_Lean_Meta_matchEqHEqLHS_x3f(v_a_1151_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v_a_1153_; 
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
lean_inc(v_a_1153_);
lean_dec_ref_known(v___x_1152_, 1);
if (lean_obj_tag(v_a_1153_) == 1)
{
lean_object* v_val_1154_; lean_object* v_snd_1155_; lean_object* v_arity_1156_; lean_object* v___x_1157_; lean_object* v_nargs_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v_dummy_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v_val_1154_ = lean_ctor_get(v_a_1153_, 0);
lean_inc(v_val_1154_);
lean_dec_ref_known(v_a_1153_, 1);
v_snd_1155_ = lean_ctor_get(v_val_1154_, 1);
lean_inc(v_snd_1155_);
lean_dec(v_val_1154_);
v_arity_1156_ = lean_ctor_get(v_val_1134_, 2);
lean_inc(v_arity_1156_);
lean_dec_ref(v_val_1134_);
v___x_1157_ = l_Lean_Expr_getAppFn(v_snd_1155_);
v_nargs_1158_ = l_Lean_Expr_getAppNumArgs(v_snd_1155_);
v___x_1159_ = l_Lean_Expr_constLevels_x21(v___x_1157_);
lean_dec_ref(v___x_1157_);
v___x_1160_ = l_Lean_mkConst(v_a_1149_, v___x_1159_);
v_dummy_1161_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0);
lean_inc(v_nargs_1158_);
v___x_1162_ = lean_mk_array(v_nargs_1158_, v_dummy_1161_);
v___x_1163_ = lean_unsigned_to_nat(1u);
v___x_1164_ = lean_nat_sub(v_nargs_1158_, v___x_1163_);
lean_dec(v_nargs_1158_);
v___x_1165_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_snd_1155_, v___x_1162_, v___x_1164_);
v___x_1166_ = lean_unsigned_to_nat(0u);
v___x_1167_ = l_Array_toSubarray___redArg(v___x_1165_, v___x_1166_, v_arity_1156_);
v___x_1168_ = l_Subarray_copy___redArg(v___x_1167_);
v___x_1169_ = l_Lean_mkAppN(v___x_1160_, v___x_1168_);
lean_dec_ref(v___x_1168_);
v___x_1170_ = lean_array_get(v___x_1135_, v_fields_1136_, v___x_1166_);
lean_dec_ref(v_fields_1136_);
v___x_1171_ = l_Lean_Expr_app___override(v___x_1169_, v___x_1170_);
v___x_1172_ = l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq(v_mvarId_1131_, v___x_1171_, v___x_1137_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
return v___x_1172_;
}
else
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
lean_dec(v_a_1153_);
lean_dec(v_a_1149_);
lean_dec_ref(v_fields_1136_);
lean_dec_ref(v_val_1134_);
lean_dec(v_mvarId_1131_);
v___x_1173_ = lean_obj_once(&l_Lean_Meta_reduceSparseCasesOn___closed__1, &l_Lean_Meta_reduceSparseCasesOn___closed__1_once, _init_l_Lean_Meta_reduceSparseCasesOn___closed__1);
v___x_1174_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1173_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
return v___x_1174_;
}
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
lean_dec(v_a_1149_);
lean_dec_ref(v_fields_1136_);
lean_dec_ref(v_val_1134_);
lean_dec(v_mvarId_1131_);
v_a_1175_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1177_ = v___x_1152_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1152_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1175_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
else
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
lean_dec(v_a_1149_);
lean_dec_ref(v_fields_1136_);
lean_dec_ref(v_val_1134_);
lean_dec(v_mvarId_1131_);
v_a_1183_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_1150_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1150_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
else
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
lean_dec_ref(v_fields_1136_);
lean_dec_ref(v_val_1134_);
lean_dec(v_mvarId_1131_);
v_a_1191_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___x_1148_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1148_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1191_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed(lean_object* v___y_1218_, lean_object* v_mvarId_1219_, lean_object* v___f_1220_, lean_object* v_declName_1221_, lean_object* v_val_1222_, lean_object* v___x_1223_, lean_object* v_fields_1224_, lean_object* v___x_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
uint8_t v___y_31351__boxed_1231_; uint8_t v___x_31356__boxed_1232_; lean_object* v_res_1233_; 
v___y_31351__boxed_1231_ = lean_unbox(v___y_1218_);
v___x_31356__boxed_1232_ = lean_unbox(v___x_1225_);
v_res_1233_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0(v___y_31351__boxed_1231_, v_mvarId_1219_, v___f_1220_, v_declName_1221_, v_val_1222_, v___x_1223_, v_fields_1224_, v___x_31356__boxed_1232_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec_ref(v___x_1223_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(lean_object* v_declName_1234_, lean_object* v_val_1235_, uint8_t v___x_1236_, size_t v_sz_1237_, size_t v_i_1238_, lean_object* v_bs_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
uint8_t v___x_1245_; 
v___x_1245_ = lean_usize_dec_lt(v_i_1238_, v_sz_1237_);
if (v___x_1245_ == 0)
{
lean_object* v___x_1246_; 
lean_dec_ref(v_val_1235_);
lean_dec(v_declName_1234_);
v___x_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1246_, 0, v_bs_1239_);
return v___x_1246_;
}
else
{
lean_object* v_v_1247_; lean_object* v_toInductionSubgoal_1248_; lean_object* v_ctorName_1249_; lean_object* v_mvarId_1250_; lean_object* v_fields_1251_; lean_object* v___f_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v_bs_x27_1255_; uint8_t v___y_1257_; 
v_v_1247_ = lean_array_uget_borrowed(v_bs_1239_, v_i_1238_);
v_toInductionSubgoal_1248_ = lean_ctor_get(v_v_1247_, 0);
v_ctorName_1249_ = lean_ctor_get(v_v_1247_, 1);
lean_inc(v_ctorName_1249_);
v_mvarId_1250_ = lean_ctor_get(v_toInductionSubgoal_1248_, 0);
lean_inc(v_mvarId_1250_);
v_fields_1251_ = lean_ctor_get(v_toInductionSubgoal_1248_, 1);
lean_inc_ref(v_fields_1251_);
v___f_1252_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0));
v___x_1253_ = l_Lean_instInhabitedExpr;
v___x_1254_ = lean_unsigned_to_nat(0u);
v_bs_x27_1255_ = lean_array_uset(v_bs_1239_, v_i_1238_, v___x_1254_);
if (lean_obj_tag(v_ctorName_1249_) == 0)
{
v___y_1257_ = v___x_1245_;
goto v___jp_1256_;
}
else
{
lean_dec_ref_known(v_ctorName_1249_, 1);
v___y_1257_ = v___x_1236_;
goto v___jp_1256_;
}
v___jp_1256_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___y_1260_; lean_object* v___x_1261_; 
v___x_1258_ = lean_box(v___y_1257_);
v___x_1259_ = lean_box(v___x_1236_);
lean_inc_ref(v_val_1235_);
lean_inc(v_declName_1234_);
lean_inc(v_mvarId_1250_);
v___y_1260_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed), 13, 8);
lean_closure_set(v___y_1260_, 0, v___x_1258_);
lean_closure_set(v___y_1260_, 1, v_mvarId_1250_);
lean_closure_set(v___y_1260_, 2, v___f_1252_);
lean_closure_set(v___y_1260_, 3, v_declName_1234_);
lean_closure_set(v___y_1260_, 4, v_val_1235_);
lean_closure_set(v___y_1260_, 5, v___x_1253_);
lean_closure_set(v___y_1260_, 6, v_fields_1251_);
lean_closure_set(v___y_1260_, 7, v___x_1259_);
v___x_1261_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1250_, v___y_1260_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; size_t v___x_1263_; size_t v___x_1264_; lean_object* v___x_1265_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_a_1262_);
lean_dec_ref_known(v___x_1261_, 1);
v___x_1263_ = ((size_t)1ULL);
v___x_1264_ = lean_usize_add(v_i_1238_, v___x_1263_);
v___x_1265_ = lean_array_uset(v_bs_x27_1255_, v_i_1238_, v_a_1262_);
v_i_1238_ = v___x_1264_;
v_bs_1239_ = v___x_1265_;
goto _start;
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
lean_dec_ref(v_bs_x27_1255_);
lean_dec_ref(v_val_1235_);
lean_dec(v_declName_1234_);
v_a_1267_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1261_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1261_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___boxed(lean_object* v_declName_1275_, lean_object* v_val_1276_, lean_object* v___x_1277_, lean_object* v_sz_1278_, lean_object* v_i_1279_, lean_object* v_bs_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
uint8_t v___x_31535__boxed_1286_; size_t v_sz_boxed_1287_; size_t v_i_boxed_1288_; lean_object* v_res_1289_; 
v___x_31535__boxed_1286_ = lean_unbox(v___x_1277_);
v_sz_boxed_1287_ = lean_unbox_usize(v_sz_1278_);
lean_dec(v_sz_1278_);
v_i_boxed_1288_ = lean_unbox_usize(v_i_1279_);
lean_dec(v_i_1279_);
v_res_1289_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(v_declName_1275_, v_val_1276_, v___x_31535__boxed_1286_, v_sz_boxed_1287_, v_i_boxed_1288_, v_bs_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(lean_object* v_declName_1290_, lean_object* v_val_1291_, uint8_t v___x_1292_, size_t v_sz_1293_, size_t v_i_1294_, lean_object* v_bs_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
uint8_t v___x_1301_; 
v___x_1301_ = lean_usize_dec_lt(v_i_1294_, v_sz_1293_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; 
lean_dec_ref(v_val_1291_);
lean_dec(v_declName_1290_);
v___x_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1302_, 0, v_bs_1295_);
return v___x_1302_;
}
else
{
lean_object* v_v_1303_; lean_object* v_toInductionSubgoal_1304_; lean_object* v_ctorName_1305_; lean_object* v_mvarId_1306_; lean_object* v_fields_1307_; lean_object* v___f_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; lean_object* v___x_1311_; lean_object* v_bs_x27_1312_; uint8_t v___y_1314_; 
v_v_1303_ = lean_array_uget_borrowed(v_bs_1295_, v_i_1294_);
v_toInductionSubgoal_1304_ = lean_ctor_get(v_v_1303_, 0);
v_ctorName_1305_ = lean_ctor_get(v_v_1303_, 1);
lean_inc(v_ctorName_1305_);
v_mvarId_1306_ = lean_ctor_get(v_toInductionSubgoal_1304_, 0);
lean_inc(v_mvarId_1306_);
v_fields_1307_ = lean_ctor_get(v_toInductionSubgoal_1304_, 1);
lean_inc_ref(v_fields_1307_);
v___f_1308_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0));
v___x_1309_ = l_Lean_instInhabitedExpr;
v___x_1310_ = 0;
v___x_1311_ = lean_unsigned_to_nat(0u);
v_bs_x27_1312_ = lean_array_uset(v_bs_1295_, v_i_1294_, v___x_1311_);
if (lean_obj_tag(v_ctorName_1305_) == 0)
{
v___y_1314_ = v___x_1292_;
goto v___jp_1313_;
}
else
{
lean_dec_ref_known(v_ctorName_1305_, 1);
v___y_1314_ = v___x_1310_;
goto v___jp_1313_;
}
v___jp_1313_:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___y_1317_; lean_object* v___x_1318_; 
v___x_1315_ = lean_box(v___y_1314_);
v___x_1316_ = lean_box(v___x_1310_);
lean_inc_ref(v_val_1291_);
lean_inc(v_declName_1290_);
lean_inc(v_mvarId_1306_);
v___y_1317_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed), 13, 8);
lean_closure_set(v___y_1317_, 0, v___x_1315_);
lean_closure_set(v___y_1317_, 1, v_mvarId_1306_);
lean_closure_set(v___y_1317_, 2, v___f_1308_);
lean_closure_set(v___y_1317_, 3, v_declName_1290_);
lean_closure_set(v___y_1317_, 4, v_val_1291_);
lean_closure_set(v___y_1317_, 5, v___x_1309_);
lean_closure_set(v___y_1317_, 6, v_fields_1307_);
lean_closure_set(v___y_1317_, 7, v___x_1316_);
v___x_1318_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1306_, v___y_1317_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; size_t v___x_1320_; size_t v___x_1321_; lean_object* v___x_1322_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1319_);
lean_dec_ref_known(v___x_1318_, 1);
v___x_1320_ = ((size_t)1ULL);
v___x_1321_ = lean_usize_add(v_i_1294_, v___x_1320_);
v___x_1322_ = lean_array_uset(v_bs_x27_1312_, v_i_1294_, v_a_1319_);
v_i_1294_ = v___x_1321_;
v_bs_1295_ = v___x_1322_;
goto _start;
}
else
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
lean_dec_ref(v_bs_x27_1312_);
lean_dec_ref(v_val_1291_);
lean_dec(v_declName_1290_);
v_a_1324_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1326_ = v___x_1318_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1318_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1324_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4___boxed(lean_object* v_declName_1332_, lean_object* v_val_1333_, lean_object* v___x_1334_, lean_object* v_sz_1335_, lean_object* v_i_1336_, lean_object* v_bs_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
uint8_t v___x_31609__boxed_1343_; size_t v_sz_boxed_1344_; size_t v_i_boxed_1345_; lean_object* v_res_1346_; 
v___x_31609__boxed_1343_ = lean_unbox(v___x_1334_);
v_sz_boxed_1344_ = lean_unbox_usize(v_sz_1335_);
lean_dec(v_sz_1335_);
v_i_boxed_1345_ = lean_unbox_usize(v_i_1336_);
lean_dec(v_i_1336_);
v_res_1346_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(v_declName_1332_, v_val_1333_, v___x_31609__boxed_1343_, v_sz_boxed_1344_, v_i_boxed_1345_, v_bs_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
return v_res_1346_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1350_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__1));
v___x_1351_ = l_Lean_stringToMessageData(v___x_1350_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(lean_object* v_val_1352_, lean_object* v___x_1353_, lean_object* v_x_1354_, lean_object* v_mvarId_1355_, lean_object* v_declName_1356_, uint8_t v___x_1357_, lean_object* v_____r_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v_majorPos_1389_; lean_object* v_arity_1390_; lean_object* v_insterestingCtors_1391_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___x_1411_; uint8_t v___x_1412_; 
v_majorPos_1389_ = lean_ctor_get(v_val_1352_, 1);
v_arity_1390_ = lean_ctor_get(v_val_1352_, 2);
v_insterestingCtors_1391_ = lean_ctor_get(v_val_1352_, 3);
v___x_1411_ = lean_array_get_size(v_x_1354_);
v___x_1412_ = lean_nat_dec_lt(v___x_1411_, v_arity_1390_);
if (v___x_1412_ == 0)
{
v___y_1393_ = v___y_1359_;
v___y_1394_ = v___y_1360_;
v___y_1395_ = v___y_1361_;
v___y_1396_ = v___y_1362_;
goto v___jp_1392_;
}
else
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
lean_dec(v_declName_1356_);
lean_dec(v_mvarId_1355_);
lean_dec_ref(v_val_1352_);
v___x_1413_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1);
v___x_1414_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1413_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1414_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1414_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
v___jp_1364_:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1371_ = lean_array_get_borrowed(v___x_1353_, v_x_1354_, v___y_1366_);
lean_dec(v___y_1366_);
v___x_1372_ = l_Lean_Expr_fvarId_x21(v___x_1371_);
v___x_1373_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__0));
v___x_1374_ = 0;
v___x_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1375_, 0, v___y_1365_);
v___x_1376_ = l_Lean_MVarId_cases(v_mvarId_1355_, v___x_1372_, v___x_1373_, v___x_1374_, v___x_1375_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; size_t v_sz_1378_; size_t v___x_1379_; lean_object* v___x_1380_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1377_);
lean_dec_ref_known(v___x_1376_, 1);
v_sz_1378_ = lean_array_size(v_a_1377_);
v___x_1379_ = ((size_t)0ULL);
v___x_1380_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(v_declName_1356_, v_val_1352_, v___x_1357_, v_sz_1378_, v___x_1379_, v_a_1377_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
return v___x_1380_;
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
lean_dec(v_declName_1356_);
lean_dec_ref(v_val_1352_);
v_a_1381_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1376_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1376_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
v___jp_1392_:
{
lean_object* v___x_1397_; uint8_t v___x_1398_; 
v___x_1397_ = lean_array_get_borrowed(v___x_1353_, v_x_1354_, v_majorPos_1389_);
v___x_1398_ = l_Lean_Expr_isFVar(v___x_1397_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
lean_dec(v_declName_1356_);
lean_dec(v_mvarId_1355_);
lean_dec_ref(v_val_1352_);
v___x_1399_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2);
lean_inc(v___x_1397_);
v___x_1400_ = l_Lean_indentExpr(v___x_1397_);
v___x_1401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1399_);
lean_ctor_set(v___x_1401_, 1, v___x_1400_);
v___x_1402_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1401_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v___x_1402_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1402_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
if (v_isShared_1406_ == 0)
{
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1403_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
else
{
lean_inc(v_majorPos_1389_);
lean_inc_ref(v_insterestingCtors_1391_);
v___y_1365_ = v_insterestingCtors_1391_;
v___y_1366_ = v_majorPos_1389_;
v___y_1367_ = v___y_1393_;
v___y_1368_ = v___y_1394_;
v___y_1369_ = v___y_1395_;
v___y_1370_ = v___y_1396_;
goto v___jp_1364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___boxed(lean_object* v_val_1423_, lean_object* v___x_1424_, lean_object* v_x_1425_, lean_object* v_mvarId_1426_, lean_object* v_declName_1427_, lean_object* v___x_1428_, lean_object* v_____r_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
uint8_t v___x_31699__boxed_1435_; lean_object* v_res_1436_; 
v___x_31699__boxed_1435_ = lean_unbox(v___x_1428_);
v_res_1436_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(v_val_1423_, v___x_1424_, v_x_1425_, v_mvarId_1426_, v_declName_1427_, v___x_31699__boxed_1435_, v_____r_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec_ref(v_x_1425_);
lean_dec_ref(v___x_1424_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(lean_object* v_cls_1439_, lean_object* v_msg_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v_ref_1446_; lean_object* v___x_1447_; lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1492_; 
v_ref_1446_ = lean_ctor_get(v___y_1443_, 2);
v___x_1447_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msg_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1450_ = v___x_1447_;
v_isShared_1451_ = v_isSharedCheck_1492_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1447_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1492_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1452_; lean_object* v_traceState_1453_; lean_object* v_env_1454_; lean_object* v_nextMacroScope_1455_; lean_object* v_ngen_1456_; lean_object* v_auxDeclNGen_1457_; lean_object* v_cache_1458_; lean_object* v_messages_1459_; lean_object* v_infoState_1460_; lean_object* v_snapshotTasks_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1491_; 
v___x_1452_ = lean_st_ref_take(v___y_1444_);
v_traceState_1453_ = lean_ctor_get(v___x_1452_, 4);
v_env_1454_ = lean_ctor_get(v___x_1452_, 0);
v_nextMacroScope_1455_ = lean_ctor_get(v___x_1452_, 1);
v_ngen_1456_ = lean_ctor_get(v___x_1452_, 2);
v_auxDeclNGen_1457_ = lean_ctor_get(v___x_1452_, 3);
v_cache_1458_ = lean_ctor_get(v___x_1452_, 5);
v_messages_1459_ = lean_ctor_get(v___x_1452_, 6);
v_infoState_1460_ = lean_ctor_get(v___x_1452_, 7);
v_snapshotTasks_1461_ = lean_ctor_get(v___x_1452_, 8);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1463_ = v___x_1452_;
v_isShared_1464_ = v_isSharedCheck_1491_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_snapshotTasks_1461_);
lean_inc(v_infoState_1460_);
lean_inc(v_messages_1459_);
lean_inc(v_cache_1458_);
lean_inc(v_traceState_1453_);
lean_inc(v_auxDeclNGen_1457_);
lean_inc(v_ngen_1456_);
lean_inc(v_nextMacroScope_1455_);
lean_inc(v_env_1454_);
lean_dec(v___x_1452_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1491_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
uint64_t v_tid_1465_; lean_object* v_traces_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1490_; 
v_tid_1465_ = lean_ctor_get_uint64(v_traceState_1453_, sizeof(void*)*1);
v_traces_1466_ = lean_ctor_get(v_traceState_1453_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v_traceState_1453_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1468_ = v_traceState_1453_;
v_isShared_1469_ = v_isSharedCheck_1490_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_traces_1466_);
lean_dec(v_traceState_1453_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1490_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; double v___x_1471_; uint8_t v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1480_; 
v___x_1470_ = lean_box(0);
v___x_1471_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0);
v___x_1472_ = 0;
v___x_1473_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__6));
v___x_1474_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1474_, 0, v_cls_1439_);
lean_ctor_set(v___x_1474_, 1, v___x_1470_);
lean_ctor_set(v___x_1474_, 2, v___x_1473_);
lean_ctor_set_float(v___x_1474_, sizeof(void*)*3, v___x_1471_);
lean_ctor_set_float(v___x_1474_, sizeof(void*)*3 + 8, v___x_1471_);
lean_ctor_set_uint8(v___x_1474_, sizeof(void*)*3 + 16, v___x_1472_);
v___x_1475_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___closed__0));
v___x_1476_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1474_);
lean_ctor_set(v___x_1476_, 1, v_a_1448_);
lean_ctor_set(v___x_1476_, 2, v___x_1475_);
lean_inc(v_ref_1446_);
v___x_1477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1477_, 0, v_ref_1446_);
lean_ctor_set(v___x_1477_, 1, v___x_1476_);
v___x_1478_ = l_Lean_PersistentArray_push___redArg(v_traces_1466_, v___x_1477_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1478_);
v___x_1480_ = v___x_1468_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1478_);
lean_ctor_set_uint64(v_reuseFailAlloc_1489_, sizeof(void*)*1, v_tid_1465_);
v___x_1480_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
lean_object* v___x_1482_; 
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 4, v___x_1480_);
v___x_1482_ = v___x_1463_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_env_1454_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_nextMacroScope_1455_);
lean_ctor_set(v_reuseFailAlloc_1488_, 2, v_ngen_1456_);
lean_ctor_set(v_reuseFailAlloc_1488_, 3, v_auxDeclNGen_1457_);
lean_ctor_set(v_reuseFailAlloc_1488_, 4, v___x_1480_);
lean_ctor_set(v_reuseFailAlloc_1488_, 5, v_cache_1458_);
lean_ctor_set(v_reuseFailAlloc_1488_, 6, v_messages_1459_);
lean_ctor_set(v_reuseFailAlloc_1488_, 7, v_infoState_1460_);
lean_ctor_set(v_reuseFailAlloc_1488_, 8, v_snapshotTasks_1461_);
v___x_1482_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1486_; 
v___x_1483_ = lean_st_ref_put(v___y_1444_, v___x_1482_);
v___x_1484_ = lean_box(0);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 0, v___x_1484_);
v___x_1486_ = v___x_1450_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1484_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___boxed(lean_object* v_cls_1493_, lean_object* v_msg_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v_cls_1493_, v_msg_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5(lean_object* v_declName_1501_, lean_object* v_val_1502_, uint8_t v___x_1503_, uint8_t v___x_1504_, size_t v_sz_1505_, size_t v_i_1506_, lean_object* v_bs_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
uint8_t v___x_1513_; 
v___x_1513_ = lean_usize_dec_lt(v_i_1506_, v_sz_1505_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1514_; 
lean_dec_ref(v_val_1502_);
lean_dec(v_declName_1501_);
v___x_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1514_, 0, v_bs_1507_);
return v___x_1514_;
}
else
{
lean_object* v_v_1515_; lean_object* v_toInductionSubgoal_1516_; lean_object* v_ctorName_1517_; lean_object* v_mvarId_1518_; lean_object* v_fields_1519_; lean_object* v___f_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v_bs_x27_1523_; uint8_t v___y_1525_; 
v_v_1515_ = lean_array_uget_borrowed(v_bs_1507_, v_i_1506_);
v_toInductionSubgoal_1516_ = lean_ctor_get(v_v_1515_, 0);
v_ctorName_1517_ = lean_ctor_get(v_v_1515_, 1);
lean_inc(v_ctorName_1517_);
v_mvarId_1518_ = lean_ctor_get(v_toInductionSubgoal_1516_, 0);
lean_inc(v_mvarId_1518_);
v_fields_1519_ = lean_ctor_get(v_toInductionSubgoal_1516_, 1);
lean_inc_ref(v_fields_1519_);
v___f_1520_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0));
v___x_1521_ = l_Lean_instInhabitedExpr;
v___x_1522_ = lean_unsigned_to_nat(0u);
v_bs_x27_1523_ = lean_array_uset(v_bs_1507_, v_i_1506_, v___x_1522_);
if (lean_obj_tag(v_ctorName_1517_) == 0)
{
v___y_1525_ = v___x_1504_;
goto v___jp_1524_;
}
else
{
lean_dec_ref_known(v_ctorName_1517_, 1);
v___y_1525_ = v___x_1503_;
goto v___jp_1524_;
}
v___jp_1524_:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___y_1528_; lean_object* v___x_1529_; 
v___x_1526_ = lean_box(v___y_1525_);
v___x_1527_ = lean_box(v___x_1503_);
lean_inc_ref(v_val_1502_);
lean_inc(v_declName_1501_);
lean_inc(v_mvarId_1518_);
v___y_1528_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed), 13, 8);
lean_closure_set(v___y_1528_, 0, v___x_1526_);
lean_closure_set(v___y_1528_, 1, v_mvarId_1518_);
lean_closure_set(v___y_1528_, 2, v___f_1520_);
lean_closure_set(v___y_1528_, 3, v_declName_1501_);
lean_closure_set(v___y_1528_, 4, v_val_1502_);
lean_closure_set(v___y_1528_, 5, v___x_1521_);
lean_closure_set(v___y_1528_, 6, v_fields_1519_);
lean_closure_set(v___y_1528_, 7, v___x_1527_);
v___x_1529_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1518_, v___y_1528_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; size_t v___x_1531_; size_t v___x_1532_; lean_object* v___x_1533_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref_known(v___x_1529_, 1);
v___x_1531_ = ((size_t)1ULL);
v___x_1532_ = lean_usize_add(v_i_1506_, v___x_1531_);
v___x_1533_ = lean_array_uset(v_bs_x27_1523_, v_i_1506_, v_a_1530_);
v_i_1506_ = v___x_1532_;
v_bs_1507_ = v___x_1533_;
goto _start;
}
else
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
lean_dec_ref(v_bs_x27_1523_);
lean_dec_ref(v_val_1502_);
lean_dec(v_declName_1501_);
v_a_1535_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1537_ = v___x_1529_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1529_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1535_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5___boxed(lean_object* v_declName_1543_, lean_object* v_val_1544_, lean_object* v___x_1545_, lean_object* v___x_1546_, lean_object* v_sz_1547_, lean_object* v_i_1548_, lean_object* v_bs_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
uint8_t v___x_31943__boxed_1555_; uint8_t v___x_31944__boxed_1556_; size_t v_sz_boxed_1557_; size_t v_i_boxed_1558_; lean_object* v_res_1559_; 
v___x_31943__boxed_1555_ = lean_unbox(v___x_1545_);
v___x_31944__boxed_1556_ = lean_unbox(v___x_1546_);
v_sz_boxed_1557_ = lean_unbox_usize(v_sz_1547_);
lean_dec(v_sz_1547_);
v_i_boxed_1558_ = lean_unbox_usize(v_i_1548_);
lean_dec(v_i_1548_);
v_res_1559_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5(v_declName_1543_, v_val_1544_, v___x_31943__boxed_1555_, v___x_31944__boxed_1556_, v_sz_boxed_1557_, v_i_boxed_1558_, v_bs_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(lean_object* v_val_1560_, lean_object* v___x_1561_, lean_object* v_x_1562_, lean_object* v_mvarId_1563_, uint8_t v___x_1564_, lean_object* v_declName_1565_, uint8_t v_hasTrace_1566_, lean_object* v_____r_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v_majorPos_1597_; lean_object* v_arity_1598_; lean_object* v_insterestingCtors_1599_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___x_1619_; uint8_t v___x_1620_; 
v_majorPos_1597_ = lean_ctor_get(v_val_1560_, 1);
v_arity_1598_ = lean_ctor_get(v_val_1560_, 2);
v_insterestingCtors_1599_ = lean_ctor_get(v_val_1560_, 3);
v___x_1619_ = lean_array_get_size(v_x_1562_);
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
lean_dec(v_declName_1565_);
lean_dec(v_mvarId_1563_);
lean_dec_ref(v_val_1560_);
v___x_1621_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1);
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
v___x_1580_ = lean_array_get_borrowed(v___x_1561_, v_x_1562_, v___y_1574_);
lean_dec(v___y_1574_);
v___x_1581_ = l_Lean_Expr_fvarId_x21(v___x_1580_);
v___x_1582_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__0));
v___x_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1583_, 0, v___y_1575_);
v___x_1584_ = l_Lean_MVarId_cases(v_mvarId_1563_, v___x_1581_, v___x_1582_, v___x_1564_, v___x_1583_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; size_t v_sz_1586_; size_t v___x_1587_; lean_object* v___x_1588_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1584_, 1);
v_sz_1586_ = lean_array_size(v_a_1585_);
v___x_1587_ = ((size_t)0ULL);
v___x_1588_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5(v_declName_1565_, v_val_1560_, v___x_1564_, v_hasTrace_1566_, v_sz_1586_, v___x_1587_, v_a_1585_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
return v___x_1588_;
}
else
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
lean_dec(v_declName_1565_);
lean_dec_ref(v_val_1560_);
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
v___x_1605_ = lean_array_get_borrowed(v___x_1561_, v_x_1562_, v_majorPos_1597_);
v___x_1606_ = l_Lean_Expr_isFVar(v___x_1605_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
lean_dec(v_declName_1565_);
lean_dec(v_mvarId_1563_);
lean_dec_ref(v_val_1560_);
v___x_1607_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2);
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
lean_inc_ref(v_insterestingCtors_1599_);
lean_inc(v_majorPos_1597_);
v___y_1574_ = v_majorPos_1597_;
v___y_1575_ = v_insterestingCtors_1599_;
v___y_1576_ = v___y_1601_;
v___y_1577_ = v___y_1602_;
v___y_1578_ = v___y_1603_;
v___y_1579_ = v___y_1604_;
goto v___jp_1573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___boxed(lean_object* v_val_1631_, lean_object* v___x_1632_, lean_object* v_x_1633_, lean_object* v_mvarId_1634_, lean_object* v___x_1635_, lean_object* v_declName_1636_, lean_object* v_hasTrace_1637_, lean_object* v_____r_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
uint8_t v___x_32028__boxed_1644_; uint8_t v_hasTrace_boxed_1645_; lean_object* v_res_1646_; 
v___x_32028__boxed_1644_ = lean_unbox(v___x_1635_);
v_hasTrace_boxed_1645_ = lean_unbox(v_hasTrace_1637_);
v_res_1646_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(v_val_1631_, v___x_1632_, v_x_1633_, v_mvarId_1634_, v___x_32028__boxed_1644_, v_declName_1636_, v_hasTrace_boxed_1645_, v_____r_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec_ref(v_x_1633_);
lean_dec_ref(v___x_1632_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(lean_object* v___x_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v_toCold_1653_; lean_object* v_options_1654_; uint8_t v_hasTrace_1655_; 
v_toCold_1653_ = lean_ctor_get(v___y_1650_, 0);
v_options_1654_ = lean_ctor_get(v_toCold_1653_, 2);
v_hasTrace_1655_ = lean_ctor_get_uint8(v_options_1654_, sizeof(void*)*1);
if (v_hasTrace_1655_ == 0)
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
lean_dec(v___x_1647_);
v___x_1656_ = lean_box(v_hasTrace_1655_);
v___x_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1656_);
return v___x_1657_;
}
else
{
lean_object* v_inheritedTraceOptions_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; uint8_t v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v_inheritedTraceOptions_1658_ = lean_ctor_get(v_toCold_1653_, 11);
v___x_1659_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__8));
v___x_1660_ = l_Lean_Name_append(v___x_1659_, v___x_1647_);
v___x_1661_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1658_, v_options_1654_, v___x_1660_);
lean_dec(v___x_1660_);
v___x_1662_ = lean_box(v___x_1661_);
v___x_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1662_);
return v___x_1663_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0___boxed(lean_object* v___x_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v___x_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
return v_res_1670_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1(void){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1672_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__0));
v___x_1673_ = l_Lean_stringToMessageData(v___x_1672_);
return v___x_1673_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3(void){
_start:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1675_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__2));
v___x_1676_ = l_Lean_stringToMessageData(v___x_1675_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6(lean_object* v_mvarId_1677_, lean_object* v_x_1678_, lean_object* v_x_1679_, lean_object* v_x_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
if (lean_obj_tag(v_x_1678_) == 5)
{
lean_object* v_fn_1686_; lean_object* v_arg_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v_fn_1686_ = lean_ctor_get(v_x_1678_, 0);
lean_inc_ref(v_fn_1686_);
v_arg_1687_ = lean_ctor_get(v_x_1678_, 1);
lean_inc_ref(v_arg_1687_);
lean_dec_ref_known(v_x_1678_, 2);
v___x_1688_ = lean_array_set(v_x_1679_, v_x_1680_, v_arg_1687_);
v___x_1689_ = lean_unsigned_to_nat(1u);
v___x_1690_ = lean_nat_sub(v_x_1680_, v___x_1689_);
lean_dec(v_x_1680_);
v_x_1678_ = v_fn_1686_;
v_x_1679_ = v___x_1688_;
v_x_1680_ = v___x_1690_;
goto _start;
}
else
{
lean_dec(v_x_1680_);
if (lean_obj_tag(v_x_1678_) == 4)
{
lean_object* v_declName_1692_; lean_object* v___x_1693_; 
v_declName_1692_ = lean_ctor_get(v_x_1678_, 0);
lean_inc_n(v_declName_1692_, 2);
lean_dec_ref_known(v_x_1678_, 2);
v___x_1693_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_declName_1692_, v___y_1684_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; 
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1694_);
lean_dec_ref_known(v___x_1693_, 1);
if (lean_obj_tag(v_a_1694_) == 1)
{
lean_object* v_toCold_1695_; lean_object* v_options_1696_; lean_object* v_val_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_2007_; 
v_toCold_1695_ = lean_ctor_get(v___y_1683_, 0);
v_options_1696_ = lean_ctor_get(v_toCold_1695_, 2);
v_val_1697_ = lean_ctor_get(v_a_1694_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v_a_1694_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_1699_ = v_a_1694_;
v_isShared_1700_ = v_isSharedCheck_2007_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_val_1697_);
lean_dec(v_a_1694_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_2007_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v_inheritedTraceOptions_1701_; uint8_t v_hasTrace_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___y_1706_; lean_object* v___y_1707_; uint8_t v___y_1708_; lean_object* v___y_1741_; lean_object* v_a_1742_; lean_object* v___y_1746_; lean_object* v___y_1749_; lean_object* v___y_1750_; uint8_t v___y_1751_; lean_object* v___y_1784_; lean_object* v_a_1785_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; 
v_inheritedTraceOptions_1701_ = lean_ctor_get(v_toCold_1695_, 11);
v_hasTrace_1702_ = lean_ctor_get_uint8(v_options_1696_, sizeof(void*)*1);
v___x_1703_ = l_Lean_instInhabitedExpr;
v___x_1704_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5));
if (v_hasTrace_1702_ == 0)
{
lean_object* v_majorPos_1815_; lean_object* v_arity_1816_; lean_object* v_insterestingCtors_1817_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___x_1837_; uint8_t v___x_1838_; 
v_majorPos_1815_ = lean_ctor_get(v_val_1697_, 1);
v_arity_1816_ = lean_ctor_get(v_val_1697_, 2);
v_insterestingCtors_1817_ = lean_ctor_get(v_val_1697_, 3);
v___x_1837_ = lean_array_get_size(v_x_1679_);
v___x_1838_ = lean_nat_dec_lt(v___x_1837_, v_arity_1816_);
if (v___x_1838_ == 0)
{
v___y_1819_ = v___y_1681_;
v___y_1820_ = v___y_1682_;
v___y_1821_ = v___y_1683_;
v___y_1822_ = v___y_1684_;
goto v___jp_1818_;
}
else
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
lean_del_object(v___x_1699_);
lean_dec(v_val_1697_);
lean_dec(v_declName_1692_);
lean_dec_ref(v_x_1679_);
lean_dec(v_mvarId_1677_);
v___x_1839_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1);
v___x_1840_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1839_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___x_1840_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1840_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
lean_inc(v_a_1841_);
if (v_isShared_1844_ == 0)
{
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_a_1841_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
v___y_1784_ = v___x_1846_;
v_a_1785_ = v_a_1841_;
goto v___jp_1783_;
}
}
}
v___jp_1818_:
{
lean_object* v___x_1823_; uint8_t v___x_1824_; 
v___x_1823_ = lean_array_get_borrowed(v___x_1703_, v_x_1679_, v_majorPos_1815_);
v___x_1824_ = l_Lean_Expr_isFVar(v___x_1823_);
if (v___x_1824_ == 0)
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1836_; 
lean_inc(v___x_1823_);
lean_del_object(v___x_1699_);
lean_dec(v_val_1697_);
lean_dec(v_declName_1692_);
lean_dec_ref(v_x_1679_);
lean_dec(v_mvarId_1677_);
v___x_1825_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2);
v___x_1826_ = l_Lean_indentExpr(v___x_1823_);
v___x_1827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1825_);
lean_ctor_set(v___x_1827_, 1, v___x_1826_);
v___x_1828_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1827_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1831_ = v___x_1828_;
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1828_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
lean_inc(v_a_1829_);
if (v_isShared_1832_ == 0)
{
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1829_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
v___y_1784_ = v___x_1834_;
v_a_1785_ = v_a_1829_;
goto v___jp_1783_;
}
}
}
else
{
lean_inc_ref(v_insterestingCtors_1817_);
lean_inc(v_majorPos_1815_);
v___y_1789_ = v_majorPos_1815_;
v___y_1790_ = v_insterestingCtors_1817_;
v___y_1791_ = v___y_1819_;
v___y_1792_ = v___y_1820_;
v___y_1793_ = v___y_1821_;
v___y_1794_ = v___y_1822_;
goto v___jp_1788_;
}
}
}
else
{
lean_object* v___f_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; uint8_t v___x_1852_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v_a_1856_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v_a_1871_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; uint8_t v___y_1877_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v_a_1890_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v_a_1909_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v_a_1921_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; uint8_t v___y_1927_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v_a_1940_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; 
lean_del_object(v___x_1699_);
v___f_1849_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1));
v___x_1850_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__6));
v___x_1851_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9);
v___x_1852_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1701_, v_options_1696_, v___x_1851_);
if (v___x_1852_ == 0)
{
lean_object* v___x_1989_; uint8_t v___x_1990_; 
v___x_1989_ = l_Lean_trace_profiler;
v___x_1990_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_options_1696_, v___x_1989_);
if (v___x_1990_ == 0)
{
if (v___x_1852_ == 0)
{
lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1991_ = lean_box(0);
v___x_1992_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(v_val_1697_, v___x_1703_, v_x_1679_, v_mvarId_1677_, v___x_1990_, v_declName_1692_, v_hasTrace_1702_, v___x_1991_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
lean_dec_ref(v_x_1679_);
v___y_1746_ = v___x_1992_;
goto v___jp_1745_;
}
else
{
lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1993_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3);
lean_inc(v_mvarId_1677_);
v___x_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1994_, 0, v_mvarId_1677_);
v___x_1995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1993_);
lean_ctor_set(v___x_1995_, 1, v___x_1994_);
v___x_1996_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1704_, v___x_1995_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; lean_object* v___x_1998_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_1997_);
lean_dec_ref_known(v___x_1996_, 1);
v___x_1998_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(v_val_1697_, v___x_1703_, v_x_1679_, v_mvarId_1677_, v___x_1990_, v_declName_1692_, v_hasTrace_1702_, v_a_1997_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
lean_dec_ref(v_x_1679_);
v___y_1746_ = v___x_1998_;
goto v___jp_1745_;
}
else
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
lean_dec(v_val_1697_);
lean_dec(v_declName_1692_);
lean_dec_ref(v_x_1679_);
lean_dec(v_mvarId_1677_);
v_a_1999_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1996_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1996_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
lean_inc(v_a_1999_);
if (v_isShared_2002_ == 0)
{
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_a_1999_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
v___y_1741_ = v___x_2004_;
v_a_1742_ = v_a_1999_;
goto v___jp_1740_;
}
}
}
}
}
else
{
goto v___jp_1956_;
}
}
else
{
goto v___jp_1956_;
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
v___x_1867_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_1704_, v_hasTrace_1702_, v___x_1850_, v_options_1696_, v___x_1852_, v___y_1855_, v___f_1849_, v___x_1866_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
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
if (v___y_1877_ == 0)
{
lean_object* v___x_1878_; lean_object* v_a_1879_; uint8_t v___x_1880_; 
v___x_1878_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v___x_1704_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
lean_inc(v_a_1879_);
lean_dec_ref(v___x_1878_);
v___x_1880_ = lean_unbox(v_a_1879_);
lean_dec(v_a_1879_);
if (v___x_1880_ == 0)
{
v___y_1869_ = v___y_1874_;
v___y_1870_ = v___y_1875_;
v_a_1871_ = v___y_1876_;
goto v___jp_1868_;
}
else
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1881_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1);
lean_inc_ref(v___y_1876_);
v___x_1882_ = l_Lean_Exception_toMessageData(v___y_1876_);
v___x_1883_ = l_Lean_indentD(v___x_1882_);
v___x_1884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1881_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
v___x_1885_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1704_, v___x_1884_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_dec_ref_known(v___x_1885_, 1);
v___y_1869_ = v___y_1874_;
v___y_1870_ = v___y_1875_;
v_a_1871_ = v___y_1876_;
goto v___jp_1868_;
}
else
{
lean_object* v_a_1886_; 
lean_dec_ref(v___y_1876_);
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1886_);
lean_dec_ref_known(v___x_1885_, 1);
v___y_1869_ = v___y_1874_;
v___y_1870_ = v___y_1875_;
v_a_1871_ = v_a_1886_;
goto v___jp_1868_;
}
}
}
else
{
v___y_1869_ = v___y_1874_;
v___y_1870_ = v___y_1875_;
v_a_1871_ = v___y_1876_;
goto v___jp_1868_;
}
}
v___jp_1887_:
{
uint8_t v___x_1891_; 
v___x_1891_ = l_Lean_Exception_isInterrupt(v_a_1890_);
if (v___x_1891_ == 0)
{
uint8_t v___x_1892_; 
lean_inc_ref(v_a_1890_);
v___x_1892_ = l_Lean_Exception_isRuntime(v_a_1890_);
v___y_1874_ = v___y_1888_;
v___y_1875_ = v___y_1889_;
v___y_1876_ = v_a_1890_;
v___y_1877_ = v___x_1892_;
goto v___jp_1873_;
}
else
{
v___y_1874_ = v___y_1888_;
v___y_1875_ = v___y_1889_;
v___y_1876_ = v_a_1890_;
v___y_1877_ = v___x_1891_;
goto v___jp_1873_;
}
}
v___jp_1893_:
{
if (lean_obj_tag(v___y_1896_) == 0)
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
v_a_1897_ = lean_ctor_get(v___y_1896_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___y_1896_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___y_1896_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___y_1896_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
lean_ctor_set_tag(v___x_1899_, 1);
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1897_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
v___y_1854_ = v___y_1894_;
v___y_1855_ = v___y_1895_;
v_a_1856_ = v___x_1902_;
goto v___jp_1853_;
}
}
}
else
{
lean_object* v_a_1905_; 
v_a_1905_ = lean_ctor_get(v___y_1896_, 0);
lean_inc(v_a_1905_);
lean_dec_ref_known(v___y_1896_, 1);
v___y_1888_ = v___y_1894_;
v___y_1889_ = v___y_1895_;
v_a_1890_ = v_a_1905_;
goto v___jp_1887_;
}
}
v___jp_1906_:
{
lean_object* v___x_1910_; double v___x_1911_; double v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1910_ = lean_io_get_num_heartbeats();
v___x_1911_ = lean_float_of_nat(v___y_1908_);
v___x_1912_ = lean_float_of_nat(v___x_1910_);
v___x_1913_ = lean_box_float(v___x_1911_);
v___x_1914_ = lean_box_float(v___x_1912_);
v___x_1915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1913_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1916_, 0, v_a_1909_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_1704_, v_hasTrace_1702_, v___x_1850_, v_options_1696_, v___x_1852_, v___y_1907_, v___f_1849_, v___x_1916_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
return v___x_1917_;
}
v___jp_1918_:
{
lean_object* v___x_1922_; 
v___x_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1922_, 0, v_a_1921_);
v___y_1907_ = v___y_1919_;
v___y_1908_ = v___y_1920_;
v_a_1909_ = v___x_1922_;
goto v___jp_1906_;
}
v___jp_1923_:
{
if (v___y_1927_ == 0)
{
lean_object* v___x_1928_; lean_object* v_a_1929_; uint8_t v___x_1930_; 
v___x_1928_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v___x_1704_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_a_1929_);
lean_dec_ref(v___x_1928_);
v___x_1930_ = lean_unbox(v_a_1929_);
lean_dec(v_a_1929_);
if (v___x_1930_ == 0)
{
v___y_1919_ = v___y_1925_;
v___y_1920_ = v___y_1926_;
v_a_1921_ = v___y_1924_;
goto v___jp_1918_;
}
else
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1931_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1);
lean_inc_ref(v___y_1924_);
v___x_1932_ = l_Lean_Exception_toMessageData(v___y_1924_);
v___x_1933_ = l_Lean_indentD(v___x_1932_);
v___x_1934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1931_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
v___x_1935_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1704_, v___x_1934_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_dec_ref_known(v___x_1935_, 1);
v___y_1919_ = v___y_1925_;
v___y_1920_ = v___y_1926_;
v_a_1921_ = v___y_1924_;
goto v___jp_1918_;
}
else
{
lean_object* v_a_1936_; 
lean_dec_ref(v___y_1924_);
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
lean_dec_ref_known(v___x_1935_, 1);
v___y_1919_ = v___y_1925_;
v___y_1920_ = v___y_1926_;
v_a_1921_ = v_a_1936_;
goto v___jp_1918_;
}
}
}
else
{
v___y_1919_ = v___y_1925_;
v___y_1920_ = v___y_1926_;
v_a_1921_ = v___y_1924_;
goto v___jp_1918_;
}
}
v___jp_1937_:
{
uint8_t v___x_1941_; 
v___x_1941_ = l_Lean_Exception_isInterrupt(v_a_1940_);
if (v___x_1941_ == 0)
{
uint8_t v___x_1942_; 
lean_inc_ref(v_a_1940_);
v___x_1942_ = l_Lean_Exception_isRuntime(v_a_1940_);
v___y_1924_ = v_a_1940_;
v___y_1925_ = v___y_1938_;
v___y_1926_ = v___y_1939_;
v___y_1927_ = v___x_1942_;
goto v___jp_1923_;
}
else
{
v___y_1924_ = v_a_1940_;
v___y_1925_ = v___y_1938_;
v___y_1926_ = v___y_1939_;
v___y_1927_ = v___x_1941_;
goto v___jp_1923_;
}
}
v___jp_1943_:
{
if (lean_obj_tag(v___y_1946_) == 0)
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
v_a_1947_ = lean_ctor_get(v___y_1946_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___y_1946_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___y_1946_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___y_1946_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
lean_ctor_set_tag(v___x_1949_, 1);
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
v___y_1907_ = v___y_1944_;
v___y_1908_ = v___y_1945_;
v_a_1909_ = v___x_1952_;
goto v___jp_1906_;
}
}
}
else
{
lean_object* v_a_1955_; 
v_a_1955_ = lean_ctor_get(v___y_1946_, 0);
lean_inc(v_a_1955_);
lean_dec_ref_known(v___y_1946_, 1);
v___y_1938_ = v___y_1944_;
v___y_1939_ = v___y_1945_;
v_a_1940_ = v_a_1955_;
goto v___jp_1937_;
}
}
v___jp_1956_:
{
lean_object* v___x_1957_; lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1988_; 
v___x_1957_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___y_1684_);
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1960_ = v___x_1957_;
v_isShared_1961_ = v_isSharedCheck_1988_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1957_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1988_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1962_; uint8_t v___x_1963_; 
v___x_1962_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1963_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_options_1696_, v___x_1962_);
if (v___x_1963_ == 0)
{
lean_object* v___x_1964_; 
v___x_1964_ = lean_io_mono_nanos_now();
if (v___x_1852_ == 0)
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
lean_del_object(v___x_1960_);
v___x_1965_ = lean_box(0);
v___x_1966_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(v_val_1697_, v___x_1703_, v_x_1679_, v_mvarId_1677_, v___x_1963_, v_declName_1692_, v_hasTrace_1702_, v___x_1965_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
lean_dec_ref(v_x_1679_);
v___y_1894_ = v___x_1964_;
v___y_1895_ = v_a_1958_;
v___y_1896_ = v___x_1966_;
goto v___jp_1893_;
}
else
{
lean_object* v___x_1967_; lean_object* v___x_1969_; 
v___x_1967_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3);
lean_inc(v_mvarId_1677_);
if (v_isShared_1961_ == 0)
{
lean_ctor_set_tag(v___x_1960_, 1);
lean_ctor_set(v___x_1960_, 0, v_mvarId_1677_);
v___x_1969_ = v___x_1960_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_mvarId_1677_);
v___x_1969_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1967_);
lean_ctor_set(v___x_1970_, 1, v___x_1969_);
v___x_1971_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1704_, v___x_1970_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v_a_1972_; lean_object* v___x_1973_; 
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
lean_inc(v_a_1972_);
lean_dec_ref_known(v___x_1971_, 1);
v___x_1973_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(v_val_1697_, v___x_1703_, v_x_1679_, v_mvarId_1677_, v___x_1963_, v_declName_1692_, v_hasTrace_1702_, v_a_1972_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
lean_dec_ref(v_x_1679_);
v___y_1894_ = v___x_1964_;
v___y_1895_ = v_a_1958_;
v___y_1896_ = v___x_1973_;
goto v___jp_1893_;
}
else
{
lean_object* v_a_1974_; 
lean_dec(v_val_1697_);
lean_dec(v_declName_1692_);
lean_dec_ref(v_x_1679_);
lean_dec(v_mvarId_1677_);
v_a_1974_ = lean_ctor_get(v___x_1971_, 0);
lean_inc(v_a_1974_);
lean_dec_ref_known(v___x_1971_, 1);
v___y_1888_ = v___x_1964_;
v___y_1889_ = v_a_1958_;
v_a_1890_ = v_a_1974_;
goto v___jp_1887_;
}
}
}
}
else
{
lean_object* v___x_1976_; 
v___x_1976_ = lean_io_get_num_heartbeats();
if (v___x_1852_ == 0)
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
lean_del_object(v___x_1960_);
v___x_1977_ = lean_box(0);
v___x_1978_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(v_val_1697_, v___x_1703_, v_x_1679_, v_mvarId_1677_, v_declName_1692_, v___x_1963_, v___x_1977_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
lean_dec_ref(v_x_1679_);
v___y_1944_ = v_a_1958_;
v___y_1945_ = v___x_1976_;
v___y_1946_ = v___x_1978_;
goto v___jp_1943_;
}
else
{
lean_object* v___x_1979_; lean_object* v___x_1981_; 
v___x_1979_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3);
lean_inc(v_mvarId_1677_);
if (v_isShared_1961_ == 0)
{
lean_ctor_set_tag(v___x_1960_, 1);
lean_ctor_set(v___x_1960_, 0, v_mvarId_1677_);
v___x_1981_ = v___x_1960_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_mvarId_1677_);
v___x_1981_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1979_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
v___x_1983_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1704_, v___x_1982_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v_a_1984_; lean_object* v___x_1985_; 
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
lean_inc(v_a_1984_);
lean_dec_ref_known(v___x_1983_, 1);
v___x_1985_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(v_val_1697_, v___x_1703_, v_x_1679_, v_mvarId_1677_, v_declName_1692_, v___x_1963_, v_a_1984_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
lean_dec_ref(v_x_1679_);
v___y_1944_ = v_a_1958_;
v___y_1945_ = v___x_1976_;
v___y_1946_ = v___x_1985_;
goto v___jp_1943_;
}
else
{
lean_object* v_a_1986_; 
lean_dec(v_val_1697_);
lean_dec(v_declName_1692_);
lean_dec_ref(v_x_1679_);
lean_dec(v_mvarId_1677_);
v_a_1986_ = lean_ctor_get(v___x_1983_, 0);
lean_inc(v_a_1986_);
lean_dec_ref_known(v___x_1983_, 1);
v___y_1938_ = v_a_1958_;
v___y_1939_ = v___x_1976_;
v_a_1940_ = v_a_1986_;
goto v___jp_1937_;
}
}
}
}
}
}
}
v___jp_1705_:
{
if (v___y_1708_ == 0)
{
lean_object* v___x_1709_; lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1739_; 
lean_dec_ref(v___y_1707_);
v___x_1709_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v___x_1704_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1712_ = v___x_1709_;
v_isShared_1713_ = v_isSharedCheck_1739_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1709_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1739_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
uint8_t v___x_1714_; 
v___x_1714_ = lean_unbox(v_a_1710_);
lean_dec(v_a_1710_);
if (v___x_1714_ == 0)
{
lean_object* v___x_1716_; 
if (v_isShared_1713_ == 0)
{
lean_ctor_set_tag(v___x_1712_, 1);
lean_ctor_set(v___x_1712_, 0, v___y_1706_);
v___x_1716_ = v___x_1712_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___y_1706_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
else
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
lean_del_object(v___x_1712_);
v___x_1718_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1);
lean_inc_ref(v___y_1706_);
v___x_1719_ = l_Lean_Exception_toMessageData(v___y_1706_);
v___x_1720_ = l_Lean_indentD(v___x_1719_);
v___x_1721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1718_);
lean_ctor_set(v___x_1721_, 1, v___x_1720_);
v___x_1722_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1704_, v___x_1721_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1729_ == 0)
{
lean_object* v_unused_1730_; 
v_unused_1730_ = lean_ctor_get(v___x_1722_, 0);
lean_dec(v_unused_1730_);
v___x_1724_ = v___x_1722_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_dec(v___x_1722_);
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
lean_ctor_set(v___x_1724_, 0, v___y_1706_);
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___y_1706_);
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
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1738_; 
lean_dec_ref(v___y_1706_);
v_a_1731_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1733_ = v___x_1722_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1722_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_1706_);
return v___y_1707_;
}
}
v___jp_1740_:
{
uint8_t v___x_1743_; 
v___x_1743_ = l_Lean_Exception_isInterrupt(v_a_1742_);
if (v___x_1743_ == 0)
{
uint8_t v___x_1744_; 
lean_inc_ref(v_a_1742_);
v___x_1744_ = l_Lean_Exception_isRuntime(v_a_1742_);
v___y_1706_ = v_a_1742_;
v___y_1707_ = v___y_1741_;
v___y_1708_ = v___x_1744_;
goto v___jp_1705_;
}
else
{
v___y_1706_ = v_a_1742_;
v___y_1707_ = v___y_1741_;
v___y_1708_ = v___x_1743_;
goto v___jp_1705_;
}
}
v___jp_1745_:
{
if (lean_obj_tag(v___y_1746_) == 0)
{
return v___y_1746_;
}
else
{
lean_object* v_a_1747_; 
v_a_1747_ = lean_ctor_get(v___y_1746_, 0);
lean_inc(v_a_1747_);
v___y_1741_ = v___y_1746_;
v_a_1742_ = v_a_1747_;
goto v___jp_1740_;
}
}
v___jp_1748_:
{
if (v___y_1751_ == 0)
{
lean_object* v___x_1752_; lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1782_; 
lean_dec_ref(v___y_1750_);
v___x_1752_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v___x_1704_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1755_ = v___x_1752_;
v_isShared_1756_ = v_isSharedCheck_1782_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1752_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1782_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
uint8_t v___x_1757_; 
v___x_1757_ = lean_unbox(v_a_1753_);
lean_dec(v_a_1753_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1759_; 
if (v_isShared_1756_ == 0)
{
lean_ctor_set_tag(v___x_1755_, 1);
lean_ctor_set(v___x_1755_, 0, v___y_1749_);
v___x_1759_ = v___x_1755_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___y_1749_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
else
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
lean_del_object(v___x_1755_);
v___x_1761_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1);
lean_inc_ref(v___y_1749_);
v___x_1762_ = l_Lean_Exception_toMessageData(v___y_1749_);
v___x_1763_ = l_Lean_indentD(v___x_1762_);
v___x_1764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1761_);
lean_ctor_set(v___x_1764_, 1, v___x_1763_);
v___x_1765_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1704_, v___x_1764_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1772_ == 0)
{
lean_object* v_unused_1773_; 
v_unused_1773_ = lean_ctor_get(v___x_1765_, 0);
lean_dec(v_unused_1773_);
v___x_1767_ = v___x_1765_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_dec(v___x_1765_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
lean_ctor_set_tag(v___x_1767_, 1);
lean_ctor_set(v___x_1767_, 0, v___y_1749_);
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___y_1749_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
else
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1781_; 
lean_dec_ref(v___y_1749_);
v_a_1774_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1776_ = v___x_1765_;
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1765_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1779_; 
if (v_isShared_1777_ == 0)
{
v___x_1779_ = v___x_1776_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_a_1774_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_1749_);
return v___y_1750_;
}
}
v___jp_1783_:
{
uint8_t v___x_1786_; 
v___x_1786_ = l_Lean_Exception_isInterrupt(v_a_1785_);
if (v___x_1786_ == 0)
{
uint8_t v___x_1787_; 
lean_inc_ref(v_a_1785_);
v___x_1787_ = l_Lean_Exception_isRuntime(v_a_1785_);
v___y_1749_ = v_a_1785_;
v___y_1750_ = v___y_1784_;
v___y_1751_ = v___x_1787_;
goto v___jp_1748_;
}
else
{
v___y_1749_ = v_a_1785_;
v___y_1750_ = v___y_1784_;
v___y_1751_ = v___x_1786_;
goto v___jp_1748_;
}
}
v___jp_1788_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1799_; 
v___x_1795_ = lean_array_get(v___x_1703_, v_x_1679_, v___y_1789_);
lean_dec(v___y_1789_);
lean_dec_ref(v_x_1679_);
v___x_1796_ = l_Lean_Expr_fvarId_x21(v___x_1795_);
lean_dec(v___x_1795_);
v___x_1797_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__0));
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 0, v___y_1790_);
v___x_1799_ = v___x_1699_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___y_1790_);
v___x_1799_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Lean_MVarId_cases(v_mvarId_1677_, v___x_1796_, v___x_1797_, v_hasTrace_1702_, v___x_1799_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; size_t v_sz_1802_; size_t v___x_1803_; lean_object* v___x_1804_; 
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
lean_inc(v_a_1801_);
lean_dec_ref_known(v___x_1800_, 1);
v_sz_1802_ = lean_array_size(v_a_1801_);
v___x_1803_ = ((size_t)0ULL);
v___x_1804_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(v_declName_1692_, v_val_1697_, v_hasTrace_1702_, v_sz_1802_, v___x_1803_, v_a_1801_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
if (lean_obj_tag(v___x_1804_) == 0)
{
return v___x_1804_;
}
else
{
lean_object* v_a_1805_; 
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_a_1805_);
v___y_1784_ = v___x_1804_;
v_a_1785_ = v_a_1805_;
goto v___jp_1783_;
}
}
else
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1813_; 
lean_dec(v_val_1697_);
lean_dec(v_declName_1692_);
v_a_1806_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1808_ = v___x_1800_;
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1800_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
lean_inc(v_a_1806_);
if (v_isShared_1809_ == 0)
{
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1806_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
v___y_1784_ = v___x_1811_;
v_a_1785_ = v_a_1806_;
goto v___jp_1783_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
lean_dec(v_a_1694_);
lean_dec(v_declName_1692_);
lean_dec_ref(v_x_1679_);
lean_dec(v_mvarId_1677_);
v___x_2008_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12);
v___x_2009_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_2008_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
return v___x_2009_;
}
}
else
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2017_; 
lean_dec(v_declName_1692_);
lean_dec_ref(v_x_1679_);
lean_dec(v_mvarId_1677_);
v_a_2010_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2012_ = v___x_1693_;
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___x_1693_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
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
return v___x_2015_;
}
}
}
}
else
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
lean_dec_ref(v_x_1679_);
lean_dec_ref(v_x_1678_);
lean_dec(v_mvarId_1677_);
v___x_2018_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14);
v___x_2019_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_2018_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
return v___x_2019_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___boxed(lean_object* v_mvarId_2020_, lean_object* v_x_2021_, lean_object* v_x_2022_, lean_object* v_x_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6(v_mvarId_2020_, v_x_2021_, v_x_2022_, v_x_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitSparseCasesOn(lean_object* v_mvarId_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_){
_start:
{
lean_object* v___x_2036_; 
lean_inc(v_mvarId_2030_);
v___x_2036_ = l_Lean_MVarId_getType(v_mvarId_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v___x_2038_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_a_2037_);
lean_dec_ref_known(v___x_2036_, 1);
v___x_2038_ = l_Lean_Meta_matchEqHEqLHS_x3f(v_a_2037_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v_a_2039_; 
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_a_2039_);
lean_dec_ref_known(v___x_2038_, 1);
if (lean_obj_tag(v_a_2039_) == 1)
{
lean_object* v_val_2040_; lean_object* v_snd_2041_; lean_object* v_dummy_2042_; lean_object* v_nargs_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v_val_2040_ = lean_ctor_get(v_a_2039_, 0);
lean_inc(v_val_2040_);
lean_dec_ref_known(v_a_2039_, 1);
v_snd_2041_ = lean_ctor_get(v_val_2040_, 1);
lean_inc(v_snd_2041_);
lean_dec(v_val_2040_);
v_dummy_2042_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0);
v_nargs_2043_ = l_Lean_Expr_getAppNumArgs(v_snd_2041_);
lean_inc(v_nargs_2043_);
v___x_2044_ = lean_mk_array(v_nargs_2043_, v_dummy_2042_);
v___x_2045_ = lean_unsigned_to_nat(1u);
v___x_2046_ = lean_nat_sub(v_nargs_2043_, v___x_2045_);
lean_dec(v_nargs_2043_);
v___x_2047_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6(v_mvarId_2030_, v_snd_2041_, v___x_2044_, v___x_2046_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_);
return v___x_2047_;
}
else
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
lean_dec(v_a_2039_);
lean_dec(v_mvarId_2030_);
v___x_2048_ = lean_obj_once(&l_Lean_Meta_reduceSparseCasesOn___closed__1, &l_Lean_Meta_reduceSparseCasesOn___closed__1_once, _init_l_Lean_Meta_reduceSparseCasesOn___closed__1);
v___x_2049_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_2048_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_);
return v___x_2049_;
}
}
else
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
lean_dec(v_mvarId_2030_);
v_a_2050_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_2038_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2038_);
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
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_dec(v_mvarId_2030_);
v_a_2058_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_2036_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2036_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitSparseCasesOn___boxed(lean_object* v_mvarId_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l_Lean_Meta_splitSparseCasesOn(v_mvarId_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
lean_dec(v_a_2070_);
lean_dec_ref(v_a_2069_);
lean_dec(v_a_2068_);
lean_dec_ref(v_a_2067_);
return v_res_2072_;
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
