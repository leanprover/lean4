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
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_10528__overap_213_; lean_object* v___x_214_; 
v___x_211_ = lean_box(0);
v___x_212_ = l_instInhabitedOfMonad___redArg(v___x_210_, v___x_211_);
v___x_10528__overap_213_ = lean_panic_fn_borrowed(v___x_212_, v_msg_156_);
lean_dec(v___x_212_);
lean_inc(v___y_160_);
lean_inc_ref(v___y_159_);
lean_inc(v___y_158_);
lean_inc_ref(v___y_157_);
v___x_214_ = lean_apply_5(v___x_10528__overap_213_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, lean_box(0));
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
lean_object* v___x_240_; lean_object* v_env_241_; lean_object* v___x_242_; lean_object* v_mctx_243_; lean_object* v_lctx_244_; lean_object* v_options_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_240_ = lean_st_ref_get(v___y_238_);
v_env_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc_ref(v_env_241_);
lean_dec(v___x_240_);
v___x_242_ = lean_st_ref_get(v___y_236_);
v_mctx_243_ = lean_ctor_get(v___x_242_, 0);
lean_inc_ref(v_mctx_243_);
lean_dec(v___x_242_);
v_lctx_244_ = lean_ctor_get(v___y_235_, 2);
v_options_245_ = lean_ctor_get(v___y_237_, 2);
lean_inc_ref(v_options_245_);
lean_inc_ref(v_lctx_244_);
v___x_246_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_246_, 0, v_env_241_);
lean_ctor_set(v___x_246_, 1, v_mctx_243_);
lean_ctor_set(v___x_246_, 2, v_lctx_244_);
lean_ctor_set(v___x_246_, 3, v_options_245_);
v___x_247_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v_msgData_234_);
v___x_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5___boxed(lean_object* v_msgData_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msgData_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(lean_object* v_msg_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_ref_262_; lean_object* v___x_263_; lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_272_; 
v_ref_262_ = lean_ctor_get(v___y_259_, 5);
v___x_263_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msg_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
v_a_264_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_272_ == 0)
{
v___x_266_ = v___x_263_;
v_isShared_267_ = v_isSharedCheck_272_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_263_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_272_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; lean_object* v___x_270_; 
lean_inc(v_ref_262_);
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v_ref_262_);
lean_ctor_set(v___x_268_, 1, v_a_264_);
if (v_isShared_267_ == 0)
{
lean_ctor_set_tag(v___x_266_, 1);
lean_ctor_set(v___x_266_, 0, v___x_268_);
v___x_270_ = v___x_266_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_268_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg___boxed(lean_object* v_msg_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v_msg_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
return v_res_279_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__1(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__0));
v___x_282_ = l_Lean_stringToMessageData(v___x_281_);
return v___x_282_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__3(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__2));
v___x_285_ = l_Lean_stringToMessageData(v___x_284_);
return v___x_285_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__7(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_289_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__6));
v___x_290_ = lean_unsigned_to_nat(11u);
v___x_291_ = lean_unsigned_to_nat(122u);
v___x_292_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__5));
v___x_293_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__4));
v___x_294_ = l_mkPanicMessageWithDecl(v___x_293_, v___x_292_, v___x_291_, v___x_290_, v___x_289_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0(lean_object* v_constName_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v___x_309_; lean_object* v_env_310_; uint8_t v___x_311_; lean_object* v___x_312_; 
v___x_309_ = lean_st_ref_get(v___y_299_);
v_env_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc_ref(v_env_310_);
lean_dec(v___x_309_);
v___x_311_ = 0;
lean_inc(v_constName_295_);
v___x_312_ = l_Lean_Environment_findAsync_x3f(v_env_310_, v_constName_295_, v___x_311_);
if (lean_obj_tag(v___x_312_) == 1)
{
lean_object* v_val_313_; uint8_t v_kind_314_; 
v_val_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_val_313_);
lean_dec_ref_known(v___x_312_, 1);
v_kind_314_ = lean_ctor_get_uint8(v_val_313_, sizeof(void*)*3);
if (v_kind_314_ == 6)
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_313_);
if (lean_obj_tag(v___x_315_) == 6)
{
lean_object* v_val_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
lean_dec(v_constName_295_);
v_val_316_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___x_315_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_val_316_);
lean_dec(v___x_315_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
lean_ctor_set_tag(v___x_318_, 0);
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_val_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; 
lean_dec_ref(v___x_315_);
v___x_324_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__7);
v___x_325_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0_spec__0(v___x_324_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_334_; 
v_a_326_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_334_ == 0)
{
v___x_328_ = v___x_325_;
v_isShared_329_ = v_isSharedCheck_334_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_325_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_334_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
if (lean_obj_tag(v_a_326_) == 0)
{
lean_del_object(v___x_328_);
goto v___jp_301_;
}
else
{
lean_object* v_val_330_; lean_object* v___x_332_; 
lean_dec(v_constName_295_);
v_val_330_ = lean_ctor_get(v_a_326_, 0);
lean_inc(v_val_330_);
lean_dec_ref_known(v_a_326_, 1);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v_val_330_);
v___x_332_ = v___x_328_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_val_330_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
else
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_342_; 
lean_dec(v_constName_295_);
v_a_335_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_342_ == 0)
{
v___x_337_ = v___x_325_;
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_325_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_338_ == 0)
{
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_335_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
}
else
{
lean_dec(v_val_313_);
goto v___jp_301_;
}
}
else
{
lean_dec(v___x_312_);
goto v___jp_301_;
}
v___jp_301_:
{
lean_object* v___x_302_; uint8_t v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_302_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__1);
v___x_303_ = 0;
v___x_304_ = l_Lean_MessageData_ofConstName(v_constName_295_, v___x_303_);
v___x_305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_302_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v___x_306_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___closed__3);
v___x_307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_305_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
v___x_308_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_307_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
return v___x_308_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0___boxed(lean_object* v_constName_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0(v_constName_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_reduceSparseCasesOn_spec__2(size_t v_sz_350_, size_t v_i_351_, lean_object* v_bs_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
uint8_t v___x_358_; 
v___x_358_ = lean_usize_dec_lt(v_i_351_, v_sz_350_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; 
v___x_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_359_, 0, v_bs_352_);
return v___x_359_;
}
else
{
lean_object* v_v_360_; lean_object* v___x_361_; 
v_v_360_ = lean_array_uget_borrowed(v_bs_352_, v_i_351_);
lean_inc(v_v_360_);
v___x_361_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_reduceSparseCasesOn_spec__0(v_v_360_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; lean_object* v_cidx_363_; lean_object* v___x_364_; lean_object* v_bs_x27_365_; size_t v___x_366_; size_t v___x_367_; lean_object* v___x_368_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_a_362_);
lean_dec_ref_known(v___x_361_, 1);
v_cidx_363_ = lean_ctor_get(v_a_362_, 2);
lean_inc(v_cidx_363_);
lean_dec(v_a_362_);
v___x_364_ = lean_unsigned_to_nat(0u);
v_bs_x27_365_ = lean_array_uset(v_bs_352_, v_i_351_, v___x_364_);
v___x_366_ = ((size_t)1ULL);
v___x_367_ = lean_usize_add(v_i_351_, v___x_366_);
v___x_368_ = lean_array_uset(v_bs_x27_365_, v_i_351_, v_cidx_363_);
v_i_351_ = v___x_367_;
v_bs_352_ = v___x_368_;
goto _start;
}
else
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_377_; 
lean_dec_ref(v_bs_352_);
v_a_370_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_377_ == 0)
{
v___x_372_ = v___x_361_;
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_361_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_reduceSparseCasesOn_spec__2___boxed(lean_object* v_sz_378_, lean_object* v_i_379_, lean_object* v_bs_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
size_t v_sz_boxed_386_; size_t v_i_boxed_387_; lean_object* v_res_388_; 
v_sz_boxed_386_ = lean_unbox_usize(v_sz_378_);
lean_dec(v_sz_378_);
v_i_boxed_387_ = lean_unbox_usize(v_i_379_);
lean_dec(v_i_379_);
v_res_388_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_reduceSparseCasesOn_spec__2(v_sz_boxed_386_, v_i_boxed_387_, v_bs_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
return v_res_388_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0(void){
_start:
{
lean_object* v___x_389_; lean_object* v_dummy_390_; 
v___x_389_ = lean_box(0);
v_dummy_390_ = l_Lean_Expr_sort___override(v___x_389_);
return v_dummy_390_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__2(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__1));
v___x_393_ = l_Lean_stringToMessageData(v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0(lean_object* v___x_394_, lean_object* v_x_395_, lean_object* v_majorPos_396_, lean_object* v_insterestingCtors_397_, lean_object* v_declName_398_, lean_object* v_snd_399_, lean_object* v_arity_400_, lean_object* v_mvarId_401_, lean_object* v___f_402_, lean_object* v_____r_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = lean_array_get_borrowed(v___x_394_, v_x_395_, v_majorPos_396_);
lean_inc(v___x_409_);
v___x_410_ = l_Lean_Meta_isConstructorApp_x27_x3f(v___x_409_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_411_; 
v_a_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_a_411_);
lean_dec_ref_known(v___x_410_, 1);
if (lean_obj_tag(v_a_411_) == 1)
{
lean_object* v_val_412_; lean_object* v_toConstantVal_413_; lean_object* v_cidx_414_; lean_object* v_name_415_; uint8_t v___x_416_; 
v_val_412_ = lean_ctor_get(v_a_411_, 0);
lean_inc(v_val_412_);
lean_dec_ref_known(v_a_411_, 1);
v_toConstantVal_413_ = lean_ctor_get(v_val_412_, 0);
lean_inc_ref(v_toConstantVal_413_);
v_cidx_414_ = lean_ctor_get(v_val_412_, 2);
lean_inc(v_cidx_414_);
lean_dec(v_val_412_);
v_name_415_ = lean_ctor_get(v_toConstantVal_413_, 0);
lean_inc(v_name_415_);
lean_dec_ref(v_toConstantVal_413_);
v___x_416_ = l_Array_contains___at___00Lean_Meta_reduceSparseCasesOn_spec__1(v_insterestingCtors_397_, v_name_415_);
lean_dec(v_name_415_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; 
lean_dec_ref(v___f_402_);
v___x_417_ = l_Lean_Meta_getSparseCasesOnEq(v_declName_398_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; size_t v_sz_419_; size_t v___x_420_; lean_object* v___x_421_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_a_418_);
lean_dec_ref_known(v___x_417_, 1);
v_sz_419_ = lean_array_size(v_insterestingCtors_397_);
v___x_420_ = ((size_t)0ULL);
v___x_421_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_reduceSparseCasesOn_spec__2(v_sz_419_, v___x_420_, v_insterestingCtors_397_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v_a_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v_a_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_a_422_);
lean_dec_ref_known(v___x_421_, 1);
v___x_423_ = l_Lean_mkRawNatLit(v_cidx_414_);
v___x_424_ = l_Lean_mkHasNotBitProof(v___x_423_, v_a_422_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
lean_dec(v_a_422_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; lean_object* v___x_426_; lean_object* v_nargs_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v_dummy_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_a_425_);
lean_dec_ref_known(v___x_424_, 1);
v___x_426_ = l_Lean_Expr_getAppFn(v_snd_399_);
v_nargs_427_ = l_Lean_Expr_getAppNumArgs(v_snd_399_);
v___x_428_ = l_Lean_Expr_constLevels_x21(v___x_426_);
lean_dec_ref(v___x_426_);
v___x_429_ = l_Lean_mkConst(v_a_418_, v___x_428_);
v_dummy_430_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0);
lean_inc(v_nargs_427_);
v___x_431_ = lean_mk_array(v_nargs_427_, v_dummy_430_);
v___x_432_ = lean_unsigned_to_nat(1u);
v___x_433_ = lean_nat_sub(v_nargs_427_, v___x_432_);
lean_dec(v_nargs_427_);
v___x_434_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_snd_399_, v___x_431_, v___x_433_);
v___x_435_ = lean_unsigned_to_nat(0u);
v___x_436_ = l_Array_toSubarray___redArg(v___x_434_, v___x_435_, v_arity_400_);
v___x_437_ = l_Subarray_copy___redArg(v___x_436_);
v___x_438_ = l_Lean_mkAppN(v___x_429_, v___x_437_);
lean_dec_ref(v___x_437_);
v___x_439_ = l_Lean_Expr_app___override(v___x_438_, v_a_425_);
v___x_440_ = l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq(v_mvarId_401_, v___x_439_, v___x_416_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_450_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_450_ == 0)
{
v___x_443_ = v___x_440_;
v_isShared_444_ = v_isSharedCheck_450_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_440_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_450_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_448_; 
v___x_445_ = lean_mk_empty_array_with_capacity(v___x_432_);
v___x_446_ = lean_array_push(v___x_445_, v_a_441_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_446_);
v___x_448_ = v___x_443_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_446_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
v_a_451_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_440_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_440_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
else
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
lean_dec(v_a_418_);
lean_dec(v_mvarId_401_);
lean_dec(v_arity_400_);
lean_dec_ref(v_snd_399_);
v_a_459_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_424_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_424_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_459_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
else
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_474_; 
lean_dec(v_a_418_);
lean_dec(v_cidx_414_);
lean_dec(v_mvarId_401_);
lean_dec(v_arity_400_);
lean_dec_ref(v_snd_399_);
v_a_467_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v___x_421_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_421_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_472_; 
if (v_isShared_470_ == 0)
{
v___x_472_ = v___x_469_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_467_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
else
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
lean_dec(v_cidx_414_);
lean_dec(v_mvarId_401_);
lean_dec(v_arity_400_);
lean_dec_ref(v_snd_399_);
lean_dec_ref(v_insterestingCtors_397_);
v_a_475_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_417_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_417_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
else
{
lean_object* v___x_483_; 
lean_dec(v_cidx_414_);
lean_dec(v_arity_400_);
lean_dec_ref(v_snd_399_);
lean_dec(v_declName_398_);
lean_dec_ref(v_insterestingCtors_397_);
v___x_483_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_401_, v___f_402_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_494_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_494_ == 0)
{
v___x_486_ = v___x_483_;
v_isShared_487_ = v_isSharedCheck_494_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_483_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_494_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_492_; 
v___x_488_ = lean_unsigned_to_nat(1u);
v___x_489_ = lean_mk_empty_array_with_capacity(v___x_488_);
v___x_490_ = lean_array_push(v___x_489_, v_a_484_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 0, v___x_490_);
v___x_492_ = v___x_486_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_490_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
else
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
v_a_495_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___x_483_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_483_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_495_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
}
else
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
lean_dec(v_a_411_);
lean_dec_ref(v___f_402_);
lean_dec(v_mvarId_401_);
lean_dec(v_arity_400_);
lean_dec_ref(v_snd_399_);
lean_dec(v_declName_398_);
lean_dec_ref(v_insterestingCtors_397_);
v___x_503_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__2);
lean_inc(v___x_409_);
v___x_504_ = l_Lean_indentExpr(v___x_409_);
v___x_505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_503_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
v___x_506_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_505_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
return v___x_506_;
}
}
else
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
lean_dec_ref(v___f_402_);
lean_dec(v_mvarId_401_);
lean_dec(v_arity_400_);
lean_dec_ref(v_snd_399_);
lean_dec(v_declName_398_);
lean_dec_ref(v_insterestingCtors_397_);
v_a_507_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_514_ == 0)
{
v___x_509_ = v___x_410_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_410_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_a_507_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___boxed(lean_object* v___x_515_, lean_object* v_x_516_, lean_object* v_majorPos_517_, lean_object* v_insterestingCtors_518_, lean_object* v_declName_519_, lean_object* v_snd_520_, lean_object* v_arity_521_, lean_object* v_mvarId_522_, lean_object* v___f_523_, lean_object* v_____r_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0(v___x_515_, v_x_516_, v_majorPos_517_, v_insterestingCtors_518_, v_declName_519_, v_snd_520_, v_arity_521_, v_mvarId_522_, v___f_523_, v_____r_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v_majorPos_517_);
lean_dec_ref(v_x_516_);
lean_dec_ref(v___x_515_);
return v_res_530_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__0));
v___x_533_ = l_Lean_stringToMessageData(v___x_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(uint8_t v___x_534_, lean_object* v___f_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
if (v___x_534_ == 0)
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = lean_box(0);
lean_inc(v___y_539_);
lean_inc_ref(v___y_538_);
lean_inc(v___y_537_);
lean_inc_ref(v___y_536_);
v___x_542_ = lean_apply_6(v___f_535_, v___x_541_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, lean_box(0));
return v___x_542_;
}
else
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
lean_dec_ref(v___f_535_);
v___x_543_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1);
v___x_544_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_543_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
v_a_545_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_544_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_544_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___boxed(lean_object* v___x_553_, lean_object* v___f_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
uint8_t v___x_14344__boxed_560_; lean_object* v_res_561_; 
v___x_14344__boxed_560_ = lean_unbox(v___x_553_);
v_res_561_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(v___x_14344__boxed_560_, v___f_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
return v_res_561_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1(void){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__0));
v___x_564_ = l_Lean_stringToMessageData(v___x_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2(lean_object* v_x_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___closed__1);
v___x_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2___boxed(lean_object* v_x_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__2(v_x_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec_ref(v_x_573_);
return v_res_579_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11(lean_object* v_e_580_){
_start:
{
if (lean_obj_tag(v_e_580_) == 0)
{
uint8_t v___x_581_; 
v___x_581_ = 2;
return v___x_581_;
}
else
{
uint8_t v___x_582_; 
v___x_582_ = 0;
return v___x_582_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11___boxed(lean_object* v_e_583_){
_start:
{
uint8_t v_res_584_; lean_object* v_r_585_; 
v_res_584_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11(v_e_583_);
lean_dec_ref(v_e_583_);
v_r_585_ = lean_box(v_res_584_);
return v_r_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12(lean_object* v_opts_586_, lean_object* v_opt_587_){
_start:
{
lean_object* v_name_588_; lean_object* v_defValue_589_; lean_object* v_map_590_; lean_object* v___x_591_; 
v_name_588_ = lean_ctor_get(v_opt_587_, 0);
v_defValue_589_ = lean_ctor_get(v_opt_587_, 1);
v_map_590_ = lean_ctor_get(v_opts_586_, 0);
v___x_591_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_590_, v_name_588_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_inc(v_defValue_589_);
return v_defValue_589_;
}
else
{
lean_object* v_val_592_; 
v_val_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_val_592_);
lean_dec_ref_known(v___x_591_, 1);
if (lean_obj_tag(v_val_592_) == 3)
{
lean_object* v_v_593_; 
v_v_593_ = lean_ctor_get(v_val_592_, 0);
lean_inc(v_v_593_);
lean_dec_ref_known(v_val_592_, 1);
return v_v_593_;
}
else
{
lean_dec(v_val_592_);
lean_inc(v_defValue_589_);
return v_defValue_589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12___boxed(lean_object* v_opts_594_, lean_object* v_opt_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12(v_opts_594_, v_opt_595_);
lean_dec_ref(v_opt_595_);
lean_dec_ref(v_opts_594_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg(lean_object* v_x_597_){
_start:
{
if (lean_obj_tag(v_x_597_) == 0)
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_606_; 
v_a_599_ = lean_ctor_get(v_x_597_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v_x_597_);
if (v_isSharedCheck_606_ == 0)
{
v___x_601_ = v_x_597_;
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v_x_597_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
lean_ctor_set_tag(v___x_601_, 1);
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_a_599_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
else
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
v_a_607_ = lean_ctor_get(v_x_597_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v_x_597_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v_x_597_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v_x_597_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
lean_ctor_set_tag(v___x_609_, 0);
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_607_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg___boxed(lean_object* v_x_615_, lean_object* v___y_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg(v_x_615_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9_spec__10(size_t v_sz_618_, size_t v_i_619_, lean_object* v_bs_620_){
_start:
{
uint8_t v___x_621_; 
v___x_621_ = lean_usize_dec_lt(v_i_619_, v_sz_618_);
if (v___x_621_ == 0)
{
return v_bs_620_;
}
else
{
lean_object* v_v_622_; lean_object* v_msg_623_; lean_object* v___x_624_; lean_object* v_bs_x27_625_; size_t v___x_626_; size_t v___x_627_; lean_object* v___x_628_; 
v_v_622_ = lean_array_uget_borrowed(v_bs_620_, v_i_619_);
v_msg_623_ = lean_ctor_get(v_v_622_, 1);
lean_inc_ref(v_msg_623_);
v___x_624_ = lean_unsigned_to_nat(0u);
v_bs_x27_625_ = lean_array_uset(v_bs_620_, v_i_619_, v___x_624_);
v___x_626_ = ((size_t)1ULL);
v___x_627_ = lean_usize_add(v_i_619_, v___x_626_);
v___x_628_ = lean_array_uset(v_bs_x27_625_, v_i_619_, v_msg_623_);
v_i_619_ = v___x_627_;
v_bs_620_ = v___x_628_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9_spec__10___boxed(lean_object* v_sz_630_, lean_object* v_i_631_, lean_object* v_bs_632_){
_start:
{
size_t v_sz_boxed_633_; size_t v_i_boxed_634_; lean_object* v_res_635_; 
v_sz_boxed_633_ = lean_unbox_usize(v_sz_630_);
lean_dec(v_sz_630_);
v_i_boxed_634_ = lean_unbox_usize(v_i_631_);
lean_dec(v_i_631_);
v_res_635_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9_spec__10(v_sz_boxed_633_, v_i_boxed_634_, v_bs_632_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9(lean_object* v_oldTraces_636_, lean_object* v_data_637_, lean_object* v_ref_638_, lean_object* v_msg_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v_fileName_645_; lean_object* v_fileMap_646_; lean_object* v_options_647_; lean_object* v_currRecDepth_648_; lean_object* v_maxRecDepth_649_; lean_object* v_ref_650_; lean_object* v_currNamespace_651_; lean_object* v_openDecls_652_; lean_object* v_initHeartbeats_653_; lean_object* v_maxHeartbeats_654_; lean_object* v_quotContext_655_; lean_object* v_currMacroScope_656_; uint8_t v_diag_657_; lean_object* v_cancelTk_x3f_658_; uint8_t v_suppressElabErrors_659_; lean_object* v_inheritedTraceOptions_660_; lean_object* v___x_661_; lean_object* v_traceState_662_; lean_object* v_traces_663_; lean_object* v_ref_664_; lean_object* v___x_665_; lean_object* v___x_666_; size_t v_sz_667_; size_t v___x_668_; lean_object* v___x_669_; lean_object* v_msg_670_; lean_object* v___x_671_; lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_709_; 
v_fileName_645_ = lean_ctor_get(v___y_642_, 0);
v_fileMap_646_ = lean_ctor_get(v___y_642_, 1);
v_options_647_ = lean_ctor_get(v___y_642_, 2);
v_currRecDepth_648_ = lean_ctor_get(v___y_642_, 3);
v_maxRecDepth_649_ = lean_ctor_get(v___y_642_, 4);
v_ref_650_ = lean_ctor_get(v___y_642_, 5);
v_currNamespace_651_ = lean_ctor_get(v___y_642_, 6);
v_openDecls_652_ = lean_ctor_get(v___y_642_, 7);
v_initHeartbeats_653_ = lean_ctor_get(v___y_642_, 8);
v_maxHeartbeats_654_ = lean_ctor_get(v___y_642_, 9);
v_quotContext_655_ = lean_ctor_get(v___y_642_, 10);
v_currMacroScope_656_ = lean_ctor_get(v___y_642_, 11);
v_diag_657_ = lean_ctor_get_uint8(v___y_642_, sizeof(void*)*14);
v_cancelTk_x3f_658_ = lean_ctor_get(v___y_642_, 12);
v_suppressElabErrors_659_ = lean_ctor_get_uint8(v___y_642_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_660_ = lean_ctor_get(v___y_642_, 13);
v___x_661_ = lean_st_ref_get(v___y_643_);
v_traceState_662_ = lean_ctor_get(v___x_661_, 4);
lean_inc_ref(v_traceState_662_);
lean_dec(v___x_661_);
v_traces_663_ = lean_ctor_get(v_traceState_662_, 0);
lean_inc_ref(v_traces_663_);
lean_dec_ref(v_traceState_662_);
v_ref_664_ = l_Lean_replaceRef(v_ref_638_, v_ref_650_);
lean_inc_ref(v_inheritedTraceOptions_660_);
lean_inc(v_cancelTk_x3f_658_);
lean_inc(v_currMacroScope_656_);
lean_inc(v_quotContext_655_);
lean_inc(v_maxHeartbeats_654_);
lean_inc(v_initHeartbeats_653_);
lean_inc(v_openDecls_652_);
lean_inc(v_currNamespace_651_);
lean_inc(v_maxRecDepth_649_);
lean_inc(v_currRecDepth_648_);
lean_inc_ref(v_options_647_);
lean_inc_ref(v_fileMap_646_);
lean_inc_ref(v_fileName_645_);
v___x_665_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_665_, 0, v_fileName_645_);
lean_ctor_set(v___x_665_, 1, v_fileMap_646_);
lean_ctor_set(v___x_665_, 2, v_options_647_);
lean_ctor_set(v___x_665_, 3, v_currRecDepth_648_);
lean_ctor_set(v___x_665_, 4, v_maxRecDepth_649_);
lean_ctor_set(v___x_665_, 5, v_ref_664_);
lean_ctor_set(v___x_665_, 6, v_currNamespace_651_);
lean_ctor_set(v___x_665_, 7, v_openDecls_652_);
lean_ctor_set(v___x_665_, 8, v_initHeartbeats_653_);
lean_ctor_set(v___x_665_, 9, v_maxHeartbeats_654_);
lean_ctor_set(v___x_665_, 10, v_quotContext_655_);
lean_ctor_set(v___x_665_, 11, v_currMacroScope_656_);
lean_ctor_set(v___x_665_, 12, v_cancelTk_x3f_658_);
lean_ctor_set(v___x_665_, 13, v_inheritedTraceOptions_660_);
lean_ctor_set_uint8(v___x_665_, sizeof(void*)*14, v_diag_657_);
lean_ctor_set_uint8(v___x_665_, sizeof(void*)*14 + 1, v_suppressElabErrors_659_);
v___x_666_ = l_Lean_PersistentArray_toArray___redArg(v_traces_663_);
lean_dec_ref(v_traces_663_);
v_sz_667_ = lean_array_size(v___x_666_);
v___x_668_ = ((size_t)0ULL);
v___x_669_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9_spec__10(v_sz_667_, v___x_668_, v___x_666_);
v_msg_670_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_670_, 0, v_data_637_);
lean_ctor_set(v_msg_670_, 1, v_msg_639_);
lean_ctor_set(v_msg_670_, 2, v___x_669_);
v___x_671_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msg_670_, v___y_640_, v___y_641_, v___x_665_, v___y_643_);
lean_dec_ref_known(v___x_665_, 14);
v_a_672_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_709_ == 0)
{
v___x_674_ = v___x_671_;
v_isShared_675_ = v_isSharedCheck_709_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_671_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_709_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_676_; lean_object* v_traceState_677_; lean_object* v_env_678_; lean_object* v_nextMacroScope_679_; lean_object* v_ngen_680_; lean_object* v_auxDeclNGen_681_; lean_object* v_cache_682_; lean_object* v_messages_683_; lean_object* v_infoState_684_; lean_object* v_snapshotTasks_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_708_; 
v___x_676_ = lean_st_ref_take(v___y_643_);
v_traceState_677_ = lean_ctor_get(v___x_676_, 4);
v_env_678_ = lean_ctor_get(v___x_676_, 0);
v_nextMacroScope_679_ = lean_ctor_get(v___x_676_, 1);
v_ngen_680_ = lean_ctor_get(v___x_676_, 2);
v_auxDeclNGen_681_ = lean_ctor_get(v___x_676_, 3);
v_cache_682_ = lean_ctor_get(v___x_676_, 5);
v_messages_683_ = lean_ctor_get(v___x_676_, 6);
v_infoState_684_ = lean_ctor_get(v___x_676_, 7);
v_snapshotTasks_685_ = lean_ctor_get(v___x_676_, 8);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_708_ == 0)
{
v___x_687_ = v___x_676_;
v_isShared_688_ = v_isSharedCheck_708_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_snapshotTasks_685_);
lean_inc(v_infoState_684_);
lean_inc(v_messages_683_);
lean_inc(v_cache_682_);
lean_inc(v_traceState_677_);
lean_inc(v_auxDeclNGen_681_);
lean_inc(v_ngen_680_);
lean_inc(v_nextMacroScope_679_);
lean_inc(v_env_678_);
lean_dec(v___x_676_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_708_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
uint64_t v_tid_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_706_; 
v_tid_689_ = lean_ctor_get_uint64(v_traceState_677_, sizeof(void*)*1);
v_isSharedCheck_706_ = !lean_is_exclusive(v_traceState_677_);
if (v_isSharedCheck_706_ == 0)
{
lean_object* v_unused_707_; 
v_unused_707_ = lean_ctor_get(v_traceState_677_, 0);
lean_dec(v_unused_707_);
v___x_691_ = v_traceState_677_;
v_isShared_692_ = v_isSharedCheck_706_;
goto v_resetjp_690_;
}
else
{
lean_dec(v_traceState_677_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_706_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_693_, 0, v_ref_638_);
lean_ctor_set(v___x_693_, 1, v_a_672_);
v___x_694_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_636_, v___x_693_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_694_);
v___x_696_ = v___x_691_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_694_);
lean_ctor_set_uint64(v_reuseFailAlloc_705_, sizeof(void*)*1, v_tid_689_);
v___x_696_ = v_reuseFailAlloc_705_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_698_; 
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 4, v___x_696_);
v___x_698_ = v___x_687_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_env_678_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_nextMacroScope_679_);
lean_ctor_set(v_reuseFailAlloc_704_, 2, v_ngen_680_);
lean_ctor_set(v_reuseFailAlloc_704_, 3, v_auxDeclNGen_681_);
lean_ctor_set(v_reuseFailAlloc_704_, 4, v___x_696_);
lean_ctor_set(v_reuseFailAlloc_704_, 5, v_cache_682_);
lean_ctor_set(v_reuseFailAlloc_704_, 6, v_messages_683_);
lean_ctor_set(v_reuseFailAlloc_704_, 7, v_infoState_684_);
lean_ctor_set(v_reuseFailAlloc_704_, 8, v_snapshotTasks_685_);
v___x_698_ = v_reuseFailAlloc_704_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_702_; 
v___x_699_ = lean_st_ref_put(v___y_643_, v___x_698_);
v___x_700_ = lean_box(0);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v___x_700_);
v___x_702_ = v___x_674_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_700_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9___boxed(lean_object* v_oldTraces_710_, lean_object* v_data_711_, lean_object* v_ref_712_, lean_object* v_msg_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9(v_oldTraces_710_, v_data_711_, v_ref_712_, v_msg_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
return v_res_719_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0(void){
_start:
{
lean_object* v___x_720_; double v___x_721_; 
v___x_720_ = lean_unsigned_to_nat(0u);
v___x_721_ = lean_float_of_nat(v___x_720_);
return v___x_721_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__1));
v___x_724_ = l_Lean_stringToMessageData(v___x_723_);
return v___x_724_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__3(void){
_start:
{
lean_object* v___x_725_; double v___x_726_; 
v___x_725_ = lean_unsigned_to_nat(1000u);
v___x_726_ = lean_float_of_nat(v___x_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(lean_object* v_cls_727_, uint8_t v_collapsed_728_, lean_object* v_tag_729_, lean_object* v_opts_730_, uint8_t v_clsEnabled_731_, lean_object* v_oldTraces_732_, lean_object* v_msg_733_, lean_object* v_resStartStop_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_fst_740_; lean_object* v_snd_741_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v_data_745_; lean_object* v_fst_756_; lean_object* v_snd_757_; lean_object* v___x_758_; uint8_t v___x_759_; lean_object* v___y_761_; lean_object* v_a_762_; uint8_t v___y_777_; double v___y_808_; 
v_fst_740_ = lean_ctor_get(v_resStartStop_734_, 0);
lean_inc(v_fst_740_);
v_snd_741_ = lean_ctor_get(v_resStartStop_734_, 1);
lean_inc(v_snd_741_);
lean_dec_ref(v_resStartStop_734_);
v_fst_756_ = lean_ctor_get(v_snd_741_, 0);
lean_inc(v_fst_756_);
v_snd_757_ = lean_ctor_get(v_snd_741_, 1);
lean_inc(v_snd_757_);
lean_dec(v_snd_741_);
v___x_758_ = l_Lean_trace_profiler;
v___x_759_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_opts_730_, v___x_758_);
if (v___x_759_ == 0)
{
v___y_777_ = v___x_759_;
goto v___jp_776_;
}
else
{
lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_813_ = l_Lean_trace_profiler_useHeartbeats;
v___x_814_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_opts_730_, v___x_813_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; lean_object* v___x_816_; double v___x_817_; double v___x_818_; double v___x_819_; 
v___x_815_ = l_Lean_trace_profiler_threshold;
v___x_816_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12(v_opts_730_, v___x_815_);
v___x_817_ = lean_float_of_nat(v___x_816_);
v___x_818_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__3);
v___x_819_ = lean_float_div(v___x_817_, v___x_818_);
v___y_808_ = v___x_819_;
goto v___jp_807_;
}
else
{
lean_object* v___x_820_; lean_object* v___x_821_; double v___x_822_; 
v___x_820_ = l_Lean_trace_profiler_threshold;
v___x_821_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12(v_opts_730_, v___x_820_);
v___x_822_ = lean_float_of_nat(v___x_821_);
v___y_808_ = v___x_822_;
goto v___jp_807_;
}
}
v___jp_742_:
{
lean_object* v___x_746_; 
lean_inc(v___y_743_);
v___x_746_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9(v_oldTraces_732_, v_data_745_, v___y_743_, v___y_744_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v___x_747_; 
lean_dec_ref_known(v___x_746_, 1);
v___x_747_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg(v_fst_740_);
return v___x_747_;
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
lean_dec(v_fst_740_);
v_a_748_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_746_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_746_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
v___jp_760_:
{
uint8_t v_result_763_; lean_object* v___x_764_; lean_object* v___x_765_; double v___x_766_; lean_object* v_data_767_; 
v_result_763_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11(v_fst_740_);
v___x_764_ = lean_box(v_result_763_);
v___x_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
v___x_766_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0);
lean_inc_ref(v_tag_729_);
lean_inc_ref(v___x_765_);
lean_inc(v_cls_727_);
v_data_767_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_767_, 0, v_cls_727_);
lean_ctor_set(v_data_767_, 1, v___x_765_);
lean_ctor_set(v_data_767_, 2, v_tag_729_);
lean_ctor_set_float(v_data_767_, sizeof(void*)*3, v___x_766_);
lean_ctor_set_float(v_data_767_, sizeof(void*)*3 + 8, v___x_766_);
lean_ctor_set_uint8(v_data_767_, sizeof(void*)*3 + 16, v_collapsed_728_);
if (v___x_759_ == 0)
{
lean_dec_ref_known(v___x_765_, 1);
lean_dec(v_snd_757_);
lean_dec(v_fst_756_);
lean_dec_ref(v_tag_729_);
lean_dec(v_cls_727_);
v___y_743_ = v___y_761_;
v___y_744_ = v_a_762_;
v_data_745_ = v_data_767_;
goto v___jp_742_;
}
else
{
lean_object* v_data_768_; double v___x_769_; double v___x_770_; 
lean_dec_ref_known(v_data_767_, 3);
v_data_768_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_768_, 0, v_cls_727_);
lean_ctor_set(v_data_768_, 1, v___x_765_);
lean_ctor_set(v_data_768_, 2, v_tag_729_);
v___x_769_ = lean_unbox_float(v_fst_756_);
lean_dec(v_fst_756_);
lean_ctor_set_float(v_data_768_, sizeof(void*)*3, v___x_769_);
v___x_770_ = lean_unbox_float(v_snd_757_);
lean_dec(v_snd_757_);
lean_ctor_set_float(v_data_768_, sizeof(void*)*3 + 8, v___x_770_);
lean_ctor_set_uint8(v_data_768_, sizeof(void*)*3 + 16, v_collapsed_728_);
v___y_743_ = v___y_761_;
v___y_744_ = v_a_762_;
v_data_745_ = v_data_768_;
goto v___jp_742_;
}
}
v___jp_771_:
{
lean_object* v_ref_772_; lean_object* v___x_773_; 
v_ref_772_ = lean_ctor_get(v___y_737_, 5);
lean_inc(v___y_738_);
lean_inc_ref(v___y_737_);
lean_inc(v___y_736_);
lean_inc_ref(v___y_735_);
lean_inc(v_fst_740_);
v___x_773_ = lean_apply_6(v_msg_733_, v_fst_740_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, lean_box(0));
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_a_774_);
lean_dec_ref_known(v___x_773_, 1);
v___y_761_ = v_ref_772_;
v_a_762_ = v_a_774_;
goto v___jp_760_;
}
else
{
lean_object* v___x_775_; 
lean_dec_ref_known(v___x_773_, 1);
v___x_775_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__2);
v___y_761_ = v_ref_772_;
v_a_762_ = v___x_775_;
goto v___jp_760_;
}
}
v___jp_776_:
{
if (v_clsEnabled_731_ == 0)
{
if (v___y_777_ == 0)
{
lean_object* v___x_778_; lean_object* v_traceState_779_; lean_object* v_env_780_; lean_object* v_nextMacroScope_781_; lean_object* v_ngen_782_; lean_object* v_auxDeclNGen_783_; lean_object* v_cache_784_; lean_object* v_messages_785_; lean_object* v_infoState_786_; lean_object* v_snapshotTasks_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_806_; 
lean_dec(v_snd_757_);
lean_dec(v_fst_756_);
lean_dec_ref(v_msg_733_);
lean_dec_ref(v_tag_729_);
lean_dec(v_cls_727_);
v___x_778_ = lean_st_ref_take(v___y_738_);
v_traceState_779_ = lean_ctor_get(v___x_778_, 4);
v_env_780_ = lean_ctor_get(v___x_778_, 0);
v_nextMacroScope_781_ = lean_ctor_get(v___x_778_, 1);
v_ngen_782_ = lean_ctor_get(v___x_778_, 2);
v_auxDeclNGen_783_ = lean_ctor_get(v___x_778_, 3);
v_cache_784_ = lean_ctor_get(v___x_778_, 5);
v_messages_785_ = lean_ctor_get(v___x_778_, 6);
v_infoState_786_ = lean_ctor_get(v___x_778_, 7);
v_snapshotTasks_787_ = lean_ctor_get(v___x_778_, 8);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_806_ == 0)
{
v___x_789_ = v___x_778_;
v_isShared_790_ = v_isSharedCheck_806_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_snapshotTasks_787_);
lean_inc(v_infoState_786_);
lean_inc(v_messages_785_);
lean_inc(v_cache_784_);
lean_inc(v_traceState_779_);
lean_inc(v_auxDeclNGen_783_);
lean_inc(v_ngen_782_);
lean_inc(v_nextMacroScope_781_);
lean_inc(v_env_780_);
lean_dec(v___x_778_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_806_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
uint64_t v_tid_791_; lean_object* v_traces_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_805_; 
v_tid_791_ = lean_ctor_get_uint64(v_traceState_779_, sizeof(void*)*1);
v_traces_792_ = lean_ctor_get(v_traceState_779_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v_traceState_779_);
if (v_isSharedCheck_805_ == 0)
{
v___x_794_ = v_traceState_779_;
v_isShared_795_ = v_isSharedCheck_805_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_traces_792_);
lean_dec(v_traceState_779_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_805_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_796_; lean_object* v___x_798_; 
v___x_796_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_732_, v_traces_792_);
lean_dec_ref(v_traces_792_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v___x_796_);
v___x_798_ = v___x_794_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_796_);
lean_ctor_set_uint64(v_reuseFailAlloc_804_, sizeof(void*)*1, v_tid_791_);
v___x_798_ = v_reuseFailAlloc_804_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
lean_object* v___x_800_; 
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 4, v___x_798_);
v___x_800_ = v___x_789_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_env_780_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v_nextMacroScope_781_);
lean_ctor_set(v_reuseFailAlloc_803_, 2, v_ngen_782_);
lean_ctor_set(v_reuseFailAlloc_803_, 3, v_auxDeclNGen_783_);
lean_ctor_set(v_reuseFailAlloc_803_, 4, v___x_798_);
lean_ctor_set(v_reuseFailAlloc_803_, 5, v_cache_784_);
lean_ctor_set(v_reuseFailAlloc_803_, 6, v_messages_785_);
lean_ctor_set(v_reuseFailAlloc_803_, 7, v_infoState_786_);
lean_ctor_set(v_reuseFailAlloc_803_, 8, v_snapshotTasks_787_);
v___x_800_ = v_reuseFailAlloc_803_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = lean_st_ref_put(v___y_738_, v___x_800_);
v___x_802_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg(v_fst_740_);
return v___x_802_;
}
}
}
}
}
else
{
goto v___jp_771_;
}
}
else
{
goto v___jp_771_;
}
}
v___jp_807_:
{
double v___x_809_; double v___x_810_; double v___x_811_; uint8_t v___x_812_; 
v___x_809_ = lean_unbox_float(v_snd_757_);
v___x_810_ = lean_unbox_float(v_fst_756_);
v___x_811_ = lean_float_sub(v___x_809_, v___x_810_);
v___x_812_ = lean_float_decLt(v___y_808_, v___x_811_);
v___y_777_ = v___x_812_;
goto v___jp_776_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___boxed(lean_object* v_cls_823_, lean_object* v_collapsed_824_, lean_object* v_tag_825_, lean_object* v_opts_826_, lean_object* v_clsEnabled_827_, lean_object* v_oldTraces_828_, lean_object* v_msg_829_, lean_object* v_resStartStop_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
uint8_t v_collapsed_boxed_836_; uint8_t v_clsEnabled_boxed_837_; lean_object* v_res_838_; 
v_collapsed_boxed_836_ = lean_unbox(v_collapsed_824_);
v_clsEnabled_boxed_837_ = lean_unbox(v_clsEnabled_827_);
v_res_838_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v_cls_823_, v_collapsed_boxed_836_, v_tag_825_, v_opts_826_, v_clsEnabled_boxed_837_, v_oldTraces_828_, v_msg_829_, v_resStartStop_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec_ref(v_opts_826_);
return v_res_838_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_852_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5));
v___x_853_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__8));
v___x_854_ = l_Lean_Name_append(v___x_853_, v___x_852_);
return v___x_854_;
}
}
static double _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10(void){
_start:
{
lean_object* v___x_855_; double v___x_856_; 
v___x_855_ = lean_unsigned_to_nat(1000000000u);
v___x_856_ = lean_float_of_nat(v___x_855_);
return v___x_856_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12(void){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__11));
v___x_859_ = l_Lean_stringToMessageData(v___x_858_);
return v___x_859_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__13));
v___x_862_ = l_Lean_stringToMessageData(v___x_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7(lean_object* v_snd_863_, lean_object* v_mvarId_864_, lean_object* v_x_865_, lean_object* v_x_866_, lean_object* v_x_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
if (lean_obj_tag(v_x_865_) == 5)
{
lean_object* v_fn_873_; lean_object* v_arg_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v_fn_873_ = lean_ctor_get(v_x_865_, 0);
lean_inc_ref(v_fn_873_);
v_arg_874_ = lean_ctor_get(v_x_865_, 1);
lean_inc_ref(v_arg_874_);
lean_dec_ref_known(v_x_865_, 2);
v___x_875_ = lean_array_set(v_x_866_, v_x_867_, v_arg_874_);
v___x_876_ = lean_unsigned_to_nat(1u);
v___x_877_ = lean_nat_sub(v_x_867_, v___x_876_);
lean_dec(v_x_867_);
v_x_865_ = v_fn_873_;
v_x_866_ = v___x_875_;
v_x_867_ = v___x_877_;
goto _start;
}
else
{
lean_dec(v_x_867_);
if (lean_obj_tag(v_x_865_) == 4)
{
lean_object* v_declName_879_; lean_object* v___x_880_; 
v_declName_879_ = lean_ctor_get(v_x_865_, 0);
lean_inc_n(v_declName_879_, 2);
lean_dec_ref_known(v_x_865_, 2);
v___x_880_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_declName_879_, v___y_871_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_a_881_);
lean_dec_ref_known(v___x_880_, 1);
if (lean_obj_tag(v_a_881_) == 1)
{
lean_object* v_val_882_; lean_object* v_options_883_; lean_object* v_majorPos_884_; lean_object* v_arity_885_; lean_object* v_insterestingCtors_886_; lean_object* v_inheritedTraceOptions_887_; uint8_t v_hasTrace_888_; lean_object* v___f_889_; lean_object* v___x_890_; lean_object* v___f_891_; lean_object* v___x_892_; uint8_t v___x_893_; 
v_val_882_ = lean_ctor_get(v_a_881_, 0);
lean_inc(v_val_882_);
lean_dec_ref_known(v_a_881_, 1);
v_options_883_ = lean_ctor_get(v___y_870_, 2);
v_majorPos_884_ = lean_ctor_get(v_val_882_, 1);
lean_inc(v_majorPos_884_);
v_arity_885_ = lean_ctor_get(v_val_882_, 2);
lean_inc_n(v_arity_885_, 2);
v_insterestingCtors_886_ = lean_ctor_get(v_val_882_, 3);
lean_inc_ref(v_insterestingCtors_886_);
lean_dec(v_val_882_);
v_inheritedTraceOptions_887_ = lean_ctor_get(v___y_870_, 13);
v_hasTrace_888_ = lean_ctor_get_uint8(v_options_883_, sizeof(void*)*1);
v___f_889_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0));
v___x_890_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_x_866_);
v___f_891_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___boxed), 15, 9);
lean_closure_set(v___f_891_, 0, v___x_890_);
lean_closure_set(v___f_891_, 1, v_x_866_);
lean_closure_set(v___f_891_, 2, v_majorPos_884_);
lean_closure_set(v___f_891_, 3, v_insterestingCtors_886_);
lean_closure_set(v___f_891_, 4, v_declName_879_);
lean_closure_set(v___f_891_, 5, v_snd_863_);
lean_closure_set(v___f_891_, 6, v_arity_885_);
lean_closure_set(v___f_891_, 7, v_mvarId_864_);
lean_closure_set(v___f_891_, 8, v___f_889_);
v___x_892_ = lean_array_get_size(v_x_866_);
lean_dec_ref(v_x_866_);
v___x_893_ = lean_nat_dec_lt(v___x_892_, v_arity_885_);
lean_dec(v_arity_885_);
if (v_hasTrace_888_ == 0)
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(v___x_893_, v___f_891_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
return v___x_894_;
}
else
{
lean_object* v___f_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; uint8_t v___x_899_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v_a_903_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v_a_918_; 
v___f_895_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1));
v___x_896_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5));
v___x_897_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__6));
v___x_898_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9);
v___x_899_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_887_, v_options_883_, v___x_898_);
if (v___x_899_ == 0)
{
lean_object* v___x_968_; uint8_t v___x_969_; 
v___x_968_ = l_Lean_trace_profiler;
v___x_969_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_options_883_, v___x_968_);
if (v___x_969_ == 0)
{
lean_object* v___x_970_; 
v___x_970_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(v___x_893_, v___f_891_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
return v___x_970_;
}
else
{
goto v___jp_927_;
}
}
else
{
goto v___jp_927_;
}
v___jp_900_:
{
lean_object* v___x_904_; double v___x_905_; double v___x_906_; double v___x_907_; double v___x_908_; double v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_904_ = lean_io_mono_nanos_now();
v___x_905_ = lean_float_of_nat(v___y_902_);
v___x_906_ = lean_float_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10);
v___x_907_ = lean_float_div(v___x_905_, v___x_906_);
v___x_908_ = lean_float_of_nat(v___x_904_);
v___x_909_ = lean_float_div(v___x_908_, v___x_906_);
v___x_910_ = lean_box_float(v___x_907_);
v___x_911_ = lean_box_float(v___x_909_);
v___x_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_910_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
v___x_913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_913_, 0, v_a_903_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_896_, v_hasTrace_888_, v___x_897_, v_options_883_, v___x_899_, v___y_901_, v___f_895_, v___x_913_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
return v___x_914_;
}
v___jp_915_:
{
lean_object* v___x_919_; double v___x_920_; double v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_919_ = lean_io_get_num_heartbeats();
v___x_920_ = lean_float_of_nat(v___y_917_);
v___x_921_ = lean_float_of_nat(v___x_919_);
v___x_922_ = lean_box_float(v___x_920_);
v___x_923_ = lean_box_float(v___x_921_);
v___x_924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_922_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_925_, 0, v_a_918_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
v___x_926_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_896_, v_hasTrace_888_, v___x_897_, v_options_883_, v___x_899_, v___y_916_, v___f_895_, v___x_925_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
return v___x_926_;
}
v___jp_927_:
{
lean_object* v___x_928_; lean_object* v_a_929_; lean_object* v___x_930_; uint8_t v___x_931_; 
v___x_928_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___y_871_);
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
lean_dec_ref(v___x_928_);
v___x_930_ = l_Lean_trace_profiler_useHeartbeats;
v___x_931_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_options_883_, v___x_930_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = lean_io_mono_nanos_now();
v___x_933_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(v___x_893_, v___f_891_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_941_ == 0)
{
v___x_936_ = v___x_933_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_933_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
lean_ctor_set_tag(v___x_936_, 1);
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
v___y_901_ = v_a_929_;
v___y_902_ = v___x_932_;
v_a_903_ = v___x_939_;
goto v___jp_900_;
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
v_a_942_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_933_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_933_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
lean_ctor_set_tag(v___x_944_, 0);
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
v___y_901_ = v_a_929_;
v___y_902_ = v___x_932_;
v_a_903_ = v___x_947_;
goto v___jp_900_;
}
}
}
}
else
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = lean_io_get_num_heartbeats();
v___x_951_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(v___x_893_, v___f_891_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___x_951_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_951_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
lean_ctor_set_tag(v___x_954_, 1);
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_952_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
v___y_916_ = v_a_929_;
v___y_917_ = v___x_950_;
v_a_918_ = v___x_957_;
goto v___jp_915_;
}
}
}
else
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_967_; 
v_a_960_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_967_ == 0)
{
v___x_962_ = v___x_951_;
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_951_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
lean_ctor_set_tag(v___x_962_, 0);
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_960_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
v___y_916_ = v_a_929_;
v___y_917_ = v___x_950_;
v_a_918_ = v___x_965_;
goto v___jp_915_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_971_; lean_object* v___x_972_; 
lean_dec(v_a_881_);
lean_dec(v_declName_879_);
lean_dec_ref(v_x_866_);
lean_dec(v_mvarId_864_);
lean_dec_ref(v_snd_863_);
v___x_971_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12);
v___x_972_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_971_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
return v___x_972_;
}
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
lean_dec(v_declName_879_);
lean_dec_ref(v_x_866_);
lean_dec(v_mvarId_864_);
lean_dec_ref(v_snd_863_);
v_a_973_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_880_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_880_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
else
{
lean_object* v___x_981_; lean_object* v___x_982_; 
lean_dec_ref(v_x_866_);
lean_dec_ref(v_x_865_);
lean_dec(v_mvarId_864_);
lean_dec_ref(v_snd_863_);
v___x_981_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14);
v___x_982_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_981_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
return v___x_982_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___boxed(lean_object* v_snd_983_, lean_object* v_mvarId_984_, lean_object* v_x_985_, lean_object* v_x_986_, lean_object* v_x_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7(v_snd_983_, v_mvarId_984_, v_x_985_, v_x_986_, v_x_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
return v_res_993_;
}
}
static lean_object* _init_l_Lean_Meta_reduceSparseCasesOn___closed__1(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = ((lean_object*)(l_Lean_Meta_reduceSparseCasesOn___closed__0));
v___x_996_ = l_Lean_stringToMessageData(v___x_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceSparseCasesOn(lean_object* v_mvarId_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v___x_1003_; 
lean_inc(v_mvarId_997_);
v___x_1003_ = l_Lean_MVarId_getType(v_mvarId_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1003_, 1);
v___x_1005_ = l_Lean_Meta_matchEqHEqLHS_x3f(v_a_1004_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_a_1006_);
lean_dec_ref_known(v___x_1005_, 1);
if (lean_obj_tag(v_a_1006_) == 1)
{
lean_object* v_val_1007_; lean_object* v_snd_1008_; lean_object* v_dummy_1009_; lean_object* v_nargs_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v_val_1007_ = lean_ctor_get(v_a_1006_, 0);
lean_inc(v_val_1007_);
lean_dec_ref_known(v_a_1006_, 1);
v_snd_1008_ = lean_ctor_get(v_val_1007_, 1);
lean_inc_n(v_snd_1008_, 2);
lean_dec(v_val_1007_);
v_dummy_1009_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0);
v_nargs_1010_ = l_Lean_Expr_getAppNumArgs(v_snd_1008_);
lean_inc(v_nargs_1010_);
v___x_1011_ = lean_mk_array(v_nargs_1010_, v_dummy_1009_);
v___x_1012_ = lean_unsigned_to_nat(1u);
v___x_1013_ = lean_nat_sub(v_nargs_1010_, v___x_1012_);
lean_dec(v_nargs_1010_);
v___x_1014_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7(v_snd_1008_, v_mvarId_997_, v_snd_1008_, v___x_1011_, v___x_1013_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_);
return v___x_1014_;
}
else
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
lean_dec(v_a_1006_);
lean_dec(v_mvarId_997_);
v___x_1015_ = lean_obj_once(&l_Lean_Meta_reduceSparseCasesOn___closed__1, &l_Lean_Meta_reduceSparseCasesOn___closed__1_once, _init_l_Lean_Meta_reduceSparseCasesOn___closed__1);
v___x_1016_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1015_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_);
return v___x_1016_;
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
lean_dec(v_mvarId_997_);
v_a_1017_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_1005_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1005_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
else
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
lean_dec(v_mvarId_997_);
v_a_1025_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_1003_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1003_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1025_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceSparseCasesOn___boxed(lean_object* v_mvarId_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l_Lean_Meta_reduceSparseCasesOn(v_mvarId_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_);
lean_dec(v_a_1037_);
lean_dec_ref(v_a_1036_);
lean_dec(v_a_1035_);
lean_dec_ref(v_a_1034_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3(lean_object* v_00_u03b1_1040_, lean_object* v_msg_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v_msg_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___boxed(lean_object* v_00_u03b1_1048_, lean_object* v_msg_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3(v_00_u03b1_1048_, v_msg_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10(lean_object* v_00_u03b1_1056_, lean_object* v_x_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg(v_x_1057_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___boxed(lean_object* v_00_u03b1_1064_, lean_object* v_x_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10(v_00_u03b1_1064_, v_x_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(lean_object* v_mvarId_1072_, lean_object* v_x_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1072_, v_x_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1079_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1079_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
v_a_1088_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1079_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1079_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg___boxed(lean_object* v_mvarId_1096_, lean_object* v_x_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1096_, v_x_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2(lean_object* v_00_u03b1_1104_, lean_object* v_mvarId_1105_, lean_object* v_x_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1105_, v_x_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___boxed(lean_object* v_00_u03b1_1113_, lean_object* v_mvarId_1114_, lean_object* v_x_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2(v_00_u03b1_1113_, v_mvarId_1114_, v_x_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_splitSparseCasesOn_spec__1(lean_object* v_a_1122_, lean_object* v_a_1123_){
_start:
{
if (lean_obj_tag(v_a_1122_) == 0)
{
lean_object* v___x_1124_; 
v___x_1124_ = l_List_reverse___redArg(v_a_1123_);
return v___x_1124_;
}
else
{
lean_object* v_head_1125_; lean_object* v_tail_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1135_; 
v_head_1125_ = lean_ctor_get(v_a_1122_, 0);
v_tail_1126_ = lean_ctor_get(v_a_1122_, 1);
v_isSharedCheck_1135_ = !lean_is_exclusive(v_a_1122_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1128_ = v_a_1122_;
v_isShared_1129_ = v_isSharedCheck_1135_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_tail_1126_);
lean_inc(v_head_1125_);
lean_dec(v_a_1122_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1135_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1130_ = l_Lean_MessageData_ofExpr(v_head_1125_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 1, v_a_1123_);
lean_ctor_set(v___x_1128_, 0, v___x_1130_);
v___x_1132_ = v___x_1128_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1130_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_a_1123_);
v___x_1132_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
v_a_1122_ = v_tail_1126_;
v_a_1123_ = v___x_1132_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__0));
v___x_1138_ = l_Lean_stringToMessageData(v___x_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0(uint8_t v___y_1139_, lean_object* v_mvarId_1140_, lean_object* v___f_1141_, lean_object* v_declName_1142_, lean_object* v_val_1143_, lean_object* v___x_1144_, lean_object* v_fields_1145_, uint8_t v___x_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; 
if (v___y_1139_ == 0)
{
lean_object* v___x_1208_; 
lean_dec_ref(v_fields_1145_);
lean_dec_ref(v_val_1143_);
lean_dec(v_declName_1142_);
v___x_1208_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_1140_, v___f_1141_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
return v___x_1208_;
}
else
{
lean_object* v___x_1209_; lean_object* v___x_1210_; uint8_t v___x_1211_; 
lean_dec_ref(v___f_1141_);
v___x_1209_ = lean_array_get_size(v_fields_1145_);
v___x_1210_ = lean_unsigned_to_nat(1u);
v___x_1211_ = lean_nat_dec_eq(v___x_1209_, v___x_1210_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1212_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1);
lean_inc_ref(v_fields_1145_);
v___x_1213_ = lean_array_to_list(v_fields_1145_);
v___x_1214_ = lean_box(0);
v___x_1215_ = l_List_mapTR_loop___at___00Lean_Meta_splitSparseCasesOn_spec__1(v___x_1213_, v___x_1214_);
v___x_1216_ = l_Lean_MessageData_ofList(v___x_1215_);
v___x_1217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1212_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
v___x_1218_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1217_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_dec_ref_known(v___x_1218_, 1);
v___y_1153_ = v___y_1147_;
v___y_1154_ = v___y_1148_;
v___y_1155_ = v___y_1149_;
v___y_1156_ = v___y_1150_;
goto v___jp_1152_;
}
else
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1226_; 
lean_dec_ref(v_fields_1145_);
lean_dec_ref(v_val_1143_);
lean_dec(v_declName_1142_);
lean_dec(v_mvarId_1140_);
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1221_ = v___x_1218_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1218_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1222_ == 0)
{
v___x_1224_ = v___x_1221_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1219_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
else
{
v___y_1153_ = v___y_1147_;
v___y_1154_ = v___y_1148_;
v___y_1155_ = v___y_1149_;
v___y_1156_ = v___y_1150_;
goto v___jp_1152_;
}
}
v___jp_1152_:
{
lean_object* v___x_1157_; 
v___x_1157_ = l_Lean_Meta_getSparseCasesOnEq(v_declName_1142_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; lean_object* v___x_1159_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_a_1158_);
lean_dec_ref_known(v___x_1157_, 1);
lean_inc(v_mvarId_1140_);
v___x_1159_ = l_Lean_MVarId_getType(v_mvarId_1140_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1160_; lean_object* v___x_1161_; 
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_a_1160_);
lean_dec_ref_known(v___x_1159_, 1);
v___x_1161_ = l_Lean_Meta_matchEqHEqLHS_x3f(v_a_1160_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; 
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_a_1162_);
lean_dec_ref_known(v___x_1161_, 1);
if (lean_obj_tag(v_a_1162_) == 1)
{
lean_object* v_val_1163_; lean_object* v_snd_1164_; lean_object* v_arity_1165_; lean_object* v___x_1166_; lean_object* v_nargs_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v_dummy_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v_val_1163_ = lean_ctor_get(v_a_1162_, 0);
lean_inc(v_val_1163_);
lean_dec_ref_known(v_a_1162_, 1);
v_snd_1164_ = lean_ctor_get(v_val_1163_, 1);
lean_inc(v_snd_1164_);
lean_dec(v_val_1163_);
v_arity_1165_ = lean_ctor_get(v_val_1143_, 2);
lean_inc(v_arity_1165_);
lean_dec_ref(v_val_1143_);
v___x_1166_ = l_Lean_Expr_getAppFn(v_snd_1164_);
v_nargs_1167_ = l_Lean_Expr_getAppNumArgs(v_snd_1164_);
v___x_1168_ = l_Lean_Expr_constLevels_x21(v___x_1166_);
lean_dec_ref(v___x_1166_);
v___x_1169_ = l_Lean_mkConst(v_a_1158_, v___x_1168_);
v_dummy_1170_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0);
lean_inc(v_nargs_1167_);
v___x_1171_ = lean_mk_array(v_nargs_1167_, v_dummy_1170_);
v___x_1172_ = lean_unsigned_to_nat(1u);
v___x_1173_ = lean_nat_sub(v_nargs_1167_, v___x_1172_);
lean_dec(v_nargs_1167_);
v___x_1174_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_snd_1164_, v___x_1171_, v___x_1173_);
v___x_1175_ = lean_unsigned_to_nat(0u);
v___x_1176_ = l_Array_toSubarray___redArg(v___x_1174_, v___x_1175_, v_arity_1165_);
v___x_1177_ = l_Subarray_copy___redArg(v___x_1176_);
v___x_1178_ = l_Lean_mkAppN(v___x_1169_, v___x_1177_);
lean_dec_ref(v___x_1177_);
v___x_1179_ = lean_array_get(v___x_1144_, v_fields_1145_, v___x_1175_);
lean_dec_ref(v_fields_1145_);
v___x_1180_ = l_Lean_Expr_app___override(v___x_1178_, v___x_1179_);
v___x_1181_ = l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq(v_mvarId_1140_, v___x_1180_, v___x_1146_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
return v___x_1181_;
}
else
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
lean_dec(v_a_1162_);
lean_dec(v_a_1158_);
lean_dec_ref(v_fields_1145_);
lean_dec_ref(v_val_1143_);
lean_dec(v_mvarId_1140_);
v___x_1182_ = lean_obj_once(&l_Lean_Meta_reduceSparseCasesOn___closed__1, &l_Lean_Meta_reduceSparseCasesOn___closed__1_once, _init_l_Lean_Meta_reduceSparseCasesOn___closed__1);
v___x_1183_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1182_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
return v___x_1183_;
}
}
else
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
lean_dec(v_a_1158_);
lean_dec_ref(v_fields_1145_);
lean_dec_ref(v_val_1143_);
lean_dec(v_mvarId_1140_);
v_a_1184_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1161_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1161_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1184_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
lean_dec(v_a_1158_);
lean_dec_ref(v_fields_1145_);
lean_dec_ref(v_val_1143_);
lean_dec(v_mvarId_1140_);
v_a_1192_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1159_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1159_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_dec_ref(v_fields_1145_);
lean_dec_ref(v_val_1143_);
lean_dec(v_mvarId_1140_);
v_a_1200_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1157_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1157_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed(lean_object* v___y_1227_, lean_object* v_mvarId_1228_, lean_object* v___f_1229_, lean_object* v_declName_1230_, lean_object* v_val_1231_, lean_object* v___x_1232_, lean_object* v_fields_1233_, lean_object* v___x_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
uint8_t v___y_31194__boxed_1240_; uint8_t v___x_31199__boxed_1241_; lean_object* v_res_1242_; 
v___y_31194__boxed_1240_ = lean_unbox(v___y_1227_);
v___x_31199__boxed_1241_ = lean_unbox(v___x_1234_);
v_res_1242_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0(v___y_31194__boxed_1240_, v_mvarId_1228_, v___f_1229_, v_declName_1230_, v_val_1231_, v___x_1232_, v_fields_1233_, v___x_31199__boxed_1241_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec_ref(v___x_1232_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(lean_object* v_declName_1243_, lean_object* v_val_1244_, uint8_t v___x_1245_, size_t v_sz_1246_, size_t v_i_1247_, lean_object* v_bs_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
uint8_t v___x_1254_; 
v___x_1254_ = lean_usize_dec_lt(v_i_1247_, v_sz_1246_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; 
lean_dec_ref(v_val_1244_);
lean_dec(v_declName_1243_);
v___x_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1255_, 0, v_bs_1248_);
return v___x_1255_;
}
else
{
lean_object* v_v_1256_; lean_object* v_toInductionSubgoal_1257_; lean_object* v_ctorName_1258_; lean_object* v_mvarId_1259_; lean_object* v_fields_1260_; lean_object* v___f_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v_bs_x27_1264_; uint8_t v___y_1266_; 
v_v_1256_ = lean_array_uget_borrowed(v_bs_1248_, v_i_1247_);
v_toInductionSubgoal_1257_ = lean_ctor_get(v_v_1256_, 0);
v_ctorName_1258_ = lean_ctor_get(v_v_1256_, 1);
lean_inc(v_ctorName_1258_);
v_mvarId_1259_ = lean_ctor_get(v_toInductionSubgoal_1257_, 0);
lean_inc(v_mvarId_1259_);
v_fields_1260_ = lean_ctor_get(v_toInductionSubgoal_1257_, 1);
lean_inc_ref(v_fields_1260_);
v___f_1261_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0));
v___x_1262_ = l_Lean_instInhabitedExpr;
v___x_1263_ = lean_unsigned_to_nat(0u);
v_bs_x27_1264_ = lean_array_uset(v_bs_1248_, v_i_1247_, v___x_1263_);
if (lean_obj_tag(v_ctorName_1258_) == 0)
{
v___y_1266_ = v___x_1254_;
goto v___jp_1265_;
}
else
{
lean_dec_ref_known(v_ctorName_1258_, 1);
v___y_1266_ = v___x_1245_;
goto v___jp_1265_;
}
v___jp_1265_:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___y_1269_; lean_object* v___x_1270_; 
v___x_1267_ = lean_box(v___y_1266_);
v___x_1268_ = lean_box(v___x_1245_);
lean_inc_ref(v_val_1244_);
lean_inc(v_declName_1243_);
lean_inc(v_mvarId_1259_);
v___y_1269_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed), 13, 8);
lean_closure_set(v___y_1269_, 0, v___x_1267_);
lean_closure_set(v___y_1269_, 1, v_mvarId_1259_);
lean_closure_set(v___y_1269_, 2, v___f_1261_);
lean_closure_set(v___y_1269_, 3, v_declName_1243_);
lean_closure_set(v___y_1269_, 4, v_val_1244_);
lean_closure_set(v___y_1269_, 5, v___x_1262_);
lean_closure_set(v___y_1269_, 6, v_fields_1260_);
lean_closure_set(v___y_1269_, 7, v___x_1268_);
v___x_1270_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1259_, v___y_1269_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; size_t v___x_1272_; size_t v___x_1273_; lean_object* v___x_1274_; 
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_a_1271_);
lean_dec_ref_known(v___x_1270_, 1);
v___x_1272_ = ((size_t)1ULL);
v___x_1273_ = lean_usize_add(v_i_1247_, v___x_1272_);
v___x_1274_ = lean_array_uset(v_bs_x27_1264_, v_i_1247_, v_a_1271_);
v_i_1247_ = v___x_1273_;
v_bs_1248_ = v___x_1274_;
goto _start;
}
else
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
lean_dec_ref(v_bs_x27_1264_);
lean_dec_ref(v_val_1244_);
lean_dec(v_declName_1243_);
v_a_1276_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1270_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1270_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___boxed(lean_object* v_declName_1284_, lean_object* v_val_1285_, lean_object* v___x_1286_, lean_object* v_sz_1287_, lean_object* v_i_1288_, lean_object* v_bs_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
uint8_t v___x_31378__boxed_1295_; size_t v_sz_boxed_1296_; size_t v_i_boxed_1297_; lean_object* v_res_1298_; 
v___x_31378__boxed_1295_ = lean_unbox(v___x_1286_);
v_sz_boxed_1296_ = lean_unbox_usize(v_sz_1287_);
lean_dec(v_sz_1287_);
v_i_boxed_1297_ = lean_unbox_usize(v_i_1288_);
lean_dec(v_i_1288_);
v_res_1298_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(v_declName_1284_, v_val_1285_, v___x_31378__boxed_1295_, v_sz_boxed_1296_, v_i_boxed_1297_, v_bs_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
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
v___f_1317_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0));
v___x_1318_ = l_Lean_instInhabitedExpr;
v___x_1319_ = 0;
v___x_1320_ = lean_unsigned_to_nat(0u);
v_bs_x27_1321_ = lean_array_uset(v_bs_1304_, v_i_1303_, v___x_1320_);
if (lean_obj_tag(v_ctorName_1314_) == 0)
{
v___y_1323_ = v___x_1301_;
goto v___jp_1322_;
}
else
{
lean_dec_ref_known(v_ctorName_1314_, 1);
v___y_1323_ = v___x_1319_;
goto v___jp_1322_;
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
v___x_1327_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1315_, v___y_1326_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; size_t v___x_1329_; size_t v___x_1330_; lean_object* v___x_1331_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_a_1328_);
lean_dec_ref_known(v___x_1327_, 1);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4___boxed(lean_object* v_declName_1341_, lean_object* v_val_1342_, lean_object* v___x_1343_, lean_object* v_sz_1344_, lean_object* v_i_1345_, lean_object* v_bs_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
uint8_t v___x_31452__boxed_1352_; size_t v_sz_boxed_1353_; size_t v_i_boxed_1354_; lean_object* v_res_1355_; 
v___x_31452__boxed_1352_ = lean_unbox(v___x_1343_);
v_sz_boxed_1353_ = lean_unbox_usize(v_sz_1344_);
lean_dec(v_sz_1344_);
v_i_boxed_1354_ = lean_unbox_usize(v_i_1345_);
lean_dec(v_i_1345_);
v_res_1355_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(v_declName_1341_, v_val_1342_, v___x_31452__boxed_1352_, v_sz_boxed_1353_, v_i_boxed_1354_, v_bs_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
return v_res_1355_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1359_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__1));
v___x_1360_ = l_Lean_stringToMessageData(v___x_1359_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(lean_object* v_val_1361_, lean_object* v___x_1362_, lean_object* v_x_1363_, lean_object* v_mvarId_1364_, lean_object* v_declName_1365_, uint8_t v___x_1366_, lean_object* v_____r_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v_majorPos_1398_; lean_object* v_arity_1399_; lean_object* v_insterestingCtors_1400_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___x_1420_; uint8_t v___x_1421_; 
v_majorPos_1398_ = lean_ctor_get(v_val_1361_, 1);
v_arity_1399_ = lean_ctor_get(v_val_1361_, 2);
v_insterestingCtors_1400_ = lean_ctor_get(v_val_1361_, 3);
v___x_1420_ = lean_array_get_size(v_x_1363_);
v___x_1421_ = lean_nat_dec_lt(v___x_1420_, v_arity_1399_);
if (v___x_1421_ == 0)
{
v___y_1402_ = v___y_1368_;
v___y_1403_ = v___y_1369_;
v___y_1404_ = v___y_1370_;
v___y_1405_ = v___y_1371_;
goto v___jp_1401_;
}
else
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1431_; 
lean_dec(v_declName_1365_);
lean_dec(v_mvarId_1364_);
lean_dec_ref(v_val_1361_);
v___x_1422_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1);
v___x_1423_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1422_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1426_ = v___x_1423_;
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1423_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1427_ == 0)
{
v___x_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_a_1424_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
v___jp_1373_:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; uint8_t v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1380_ = lean_array_get_borrowed(v___x_1362_, v_x_1363_, v___y_1374_);
lean_dec(v___y_1374_);
v___x_1381_ = l_Lean_Expr_fvarId_x21(v___x_1380_);
v___x_1382_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__0));
v___x_1383_ = 0;
v___x_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1384_, 0, v___y_1375_);
v___x_1385_ = l_Lean_MVarId_cases(v_mvarId_1364_, v___x_1381_, v___x_1382_, v___x_1383_, v___x_1384_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; size_t v_sz_1387_; size_t v___x_1388_; lean_object* v___x_1389_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_a_1386_);
lean_dec_ref_known(v___x_1385_, 1);
v_sz_1387_ = lean_array_size(v_a_1386_);
v___x_1388_ = ((size_t)0ULL);
v___x_1389_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(v_declName_1365_, v_val_1361_, v___x_1366_, v_sz_1387_, v___x_1388_, v_a_1386_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
return v___x_1389_;
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
lean_dec(v_declName_1365_);
lean_dec_ref(v_val_1361_);
v_a_1390_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v___x_1385_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1385_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1390_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
v___jp_1401_:
{
lean_object* v___x_1406_; uint8_t v___x_1407_; 
v___x_1406_ = lean_array_get_borrowed(v___x_1362_, v_x_1363_, v_majorPos_1398_);
v___x_1407_ = l_Lean_Expr_isFVar(v___x_1406_);
if (v___x_1407_ == 0)
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
lean_dec(v_declName_1365_);
lean_dec(v_mvarId_1364_);
lean_dec_ref(v_val_1361_);
v___x_1408_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2);
lean_inc(v___x_1406_);
v___x_1409_ = l_Lean_indentExpr(v___x_1406_);
v___x_1410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1408_);
lean_ctor_set(v___x_1410_, 1, v___x_1409_);
v___x_1411_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1410_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___x_1411_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1411_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1412_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
else
{
lean_inc_ref(v_insterestingCtors_1400_);
lean_inc(v_majorPos_1398_);
v___y_1374_ = v_majorPos_1398_;
v___y_1375_ = v_insterestingCtors_1400_;
v___y_1376_ = v___y_1402_;
v___y_1377_ = v___y_1403_;
v___y_1378_ = v___y_1404_;
v___y_1379_ = v___y_1405_;
goto v___jp_1373_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___boxed(lean_object* v_val_1432_, lean_object* v___x_1433_, lean_object* v_x_1434_, lean_object* v_mvarId_1435_, lean_object* v_declName_1436_, lean_object* v___x_1437_, lean_object* v_____r_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
uint8_t v___x_31542__boxed_1444_; lean_object* v_res_1445_; 
v___x_31542__boxed_1444_ = lean_unbox(v___x_1437_);
v_res_1445_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(v_val_1432_, v___x_1433_, v_x_1434_, v_mvarId_1435_, v_declName_1436_, v___x_31542__boxed_1444_, v_____r_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec_ref(v_x_1434_);
lean_dec_ref(v___x_1433_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(lean_object* v_cls_1448_, lean_object* v_msg_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v_ref_1455_; lean_object* v___x_1456_; lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1501_; 
v_ref_1455_ = lean_ctor_get(v___y_1452_, 5);
v___x_1456_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msg_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1459_ = v___x_1456_;
v_isShared_1460_ = v_isSharedCheck_1501_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1456_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1501_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1461_; lean_object* v_traceState_1462_; lean_object* v_env_1463_; lean_object* v_nextMacroScope_1464_; lean_object* v_ngen_1465_; lean_object* v_auxDeclNGen_1466_; lean_object* v_cache_1467_; lean_object* v_messages_1468_; lean_object* v_infoState_1469_; lean_object* v_snapshotTasks_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1500_; 
v___x_1461_ = lean_st_ref_take(v___y_1453_);
v_traceState_1462_ = lean_ctor_get(v___x_1461_, 4);
v_env_1463_ = lean_ctor_get(v___x_1461_, 0);
v_nextMacroScope_1464_ = lean_ctor_get(v___x_1461_, 1);
v_ngen_1465_ = lean_ctor_get(v___x_1461_, 2);
v_auxDeclNGen_1466_ = lean_ctor_get(v___x_1461_, 3);
v_cache_1467_ = lean_ctor_get(v___x_1461_, 5);
v_messages_1468_ = lean_ctor_get(v___x_1461_, 6);
v_infoState_1469_ = lean_ctor_get(v___x_1461_, 7);
v_snapshotTasks_1470_ = lean_ctor_get(v___x_1461_, 8);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1472_ = v___x_1461_;
v_isShared_1473_ = v_isSharedCheck_1500_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_snapshotTasks_1470_);
lean_inc(v_infoState_1469_);
lean_inc(v_messages_1468_);
lean_inc(v_cache_1467_);
lean_inc(v_traceState_1462_);
lean_inc(v_auxDeclNGen_1466_);
lean_inc(v_ngen_1465_);
lean_inc(v_nextMacroScope_1464_);
lean_inc(v_env_1463_);
lean_dec(v___x_1461_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1500_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
uint64_t v_tid_1474_; lean_object* v_traces_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1499_; 
v_tid_1474_ = lean_ctor_get_uint64(v_traceState_1462_, sizeof(void*)*1);
v_traces_1475_ = lean_ctor_get(v_traceState_1462_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v_traceState_1462_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1477_ = v_traceState_1462_;
v_isShared_1478_ = v_isSharedCheck_1499_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_traces_1475_);
lean_dec(v_traceState_1462_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1499_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1479_; double v___x_1480_; uint8_t v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1489_; 
v___x_1479_ = lean_box(0);
v___x_1480_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0);
v___x_1481_ = 0;
v___x_1482_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__6));
v___x_1483_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1483_, 0, v_cls_1448_);
lean_ctor_set(v___x_1483_, 1, v___x_1479_);
lean_ctor_set(v___x_1483_, 2, v___x_1482_);
lean_ctor_set_float(v___x_1483_, sizeof(void*)*3, v___x_1480_);
lean_ctor_set_float(v___x_1483_, sizeof(void*)*3 + 8, v___x_1480_);
lean_ctor_set_uint8(v___x_1483_, sizeof(void*)*3 + 16, v___x_1481_);
v___x_1484_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___closed__0));
v___x_1485_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1483_);
lean_ctor_set(v___x_1485_, 1, v_a_1457_);
lean_ctor_set(v___x_1485_, 2, v___x_1484_);
lean_inc(v_ref_1455_);
v___x_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1486_, 0, v_ref_1455_);
lean_ctor_set(v___x_1486_, 1, v___x_1485_);
v___x_1487_ = l_Lean_PersistentArray_push___redArg(v_traces_1475_, v___x_1486_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 0, v___x_1487_);
v___x_1489_ = v___x_1477_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1487_);
lean_ctor_set_uint64(v_reuseFailAlloc_1498_, sizeof(void*)*1, v_tid_1474_);
v___x_1489_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
lean_object* v___x_1491_; 
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 4, v___x_1489_);
v___x_1491_ = v___x_1472_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_env_1463_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v_nextMacroScope_1464_);
lean_ctor_set(v_reuseFailAlloc_1497_, 2, v_ngen_1465_);
lean_ctor_set(v_reuseFailAlloc_1497_, 3, v_auxDeclNGen_1466_);
lean_ctor_set(v_reuseFailAlloc_1497_, 4, v___x_1489_);
lean_ctor_set(v_reuseFailAlloc_1497_, 5, v_cache_1467_);
lean_ctor_set(v_reuseFailAlloc_1497_, 6, v_messages_1468_);
lean_ctor_set(v_reuseFailAlloc_1497_, 7, v_infoState_1469_);
lean_ctor_set(v_reuseFailAlloc_1497_, 8, v_snapshotTasks_1470_);
v___x_1491_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1495_; 
v___x_1492_ = lean_st_ref_put(v___y_1453_, v___x_1491_);
v___x_1493_ = lean_box(0);
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 0, v___x_1493_);
v___x_1495_ = v___x_1459_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1493_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___boxed(lean_object* v_cls_1502_, lean_object* v_msg_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v_cls_1502_, v_msg_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5(lean_object* v_declName_1510_, lean_object* v_val_1511_, uint8_t v___x_1512_, uint8_t v___x_1513_, size_t v_sz_1514_, size_t v_i_1515_, lean_object* v_bs_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
uint8_t v___x_1522_; 
v___x_1522_ = lean_usize_dec_lt(v_i_1515_, v_sz_1514_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; 
lean_dec_ref(v_val_1511_);
lean_dec(v_declName_1510_);
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
v___f_1529_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0));
v___x_1530_ = l_Lean_instInhabitedExpr;
v___x_1531_ = lean_unsigned_to_nat(0u);
v_bs_x27_1532_ = lean_array_uset(v_bs_1516_, v_i_1515_, v___x_1531_);
if (lean_obj_tag(v_ctorName_1526_) == 0)
{
v___y_1534_ = v___x_1513_;
goto v___jp_1533_;
}
else
{
lean_dec_ref_known(v_ctorName_1526_, 1);
v___y_1534_ = v___x_1512_;
goto v___jp_1533_;
}
v___jp_1533_:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___y_1537_; lean_object* v___x_1538_; 
v___x_1535_ = lean_box(v___y_1534_);
v___x_1536_ = lean_box(v___x_1512_);
lean_inc_ref(v_val_1511_);
lean_inc(v_declName_1510_);
lean_inc(v_mvarId_1527_);
v___y_1537_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed), 13, 8);
lean_closure_set(v___y_1537_, 0, v___x_1535_);
lean_closure_set(v___y_1537_, 1, v_mvarId_1527_);
lean_closure_set(v___y_1537_, 2, v___f_1529_);
lean_closure_set(v___y_1537_, 3, v_declName_1510_);
lean_closure_set(v___y_1537_, 4, v_val_1511_);
lean_closure_set(v___y_1537_, 5, v___x_1530_);
lean_closure_set(v___y_1537_, 6, v_fields_1528_);
lean_closure_set(v___y_1537_, 7, v___x_1536_);
v___x_1538_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1527_, v___y_1537_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; size_t v___x_1540_; size_t v___x_1541_; lean_object* v___x_1542_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_a_1539_);
lean_dec_ref_known(v___x_1538_, 1);
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
lean_dec_ref(v_val_1511_);
lean_dec(v_declName_1510_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5___boxed(lean_object* v_declName_1552_, lean_object* v_val_1553_, lean_object* v___x_1554_, lean_object* v___x_1555_, lean_object* v_sz_1556_, lean_object* v_i_1557_, lean_object* v_bs_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
uint8_t v___x_31786__boxed_1564_; uint8_t v___x_31787__boxed_1565_; size_t v_sz_boxed_1566_; size_t v_i_boxed_1567_; lean_object* v_res_1568_; 
v___x_31786__boxed_1564_ = lean_unbox(v___x_1554_);
v___x_31787__boxed_1565_ = lean_unbox(v___x_1555_);
v_sz_boxed_1566_ = lean_unbox_usize(v_sz_1556_);
lean_dec(v_sz_1556_);
v_i_boxed_1567_ = lean_unbox_usize(v_i_1557_);
lean_dec(v_i_1557_);
v_res_1568_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5(v_declName_1552_, v_val_1553_, v___x_31786__boxed_1564_, v___x_31787__boxed_1565_, v_sz_boxed_1566_, v_i_boxed_1567_, v_bs_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(lean_object* v_val_1569_, lean_object* v___x_1570_, lean_object* v_x_1571_, lean_object* v_mvarId_1572_, uint8_t v___x_1573_, lean_object* v_declName_1574_, uint8_t v_hasTrace_1575_, lean_object* v_____r_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v_majorPos_1606_; lean_object* v_arity_1607_; lean_object* v_insterestingCtors_1608_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___x_1628_; uint8_t v___x_1629_; 
v_majorPos_1606_ = lean_ctor_get(v_val_1569_, 1);
v_arity_1607_ = lean_ctor_get(v_val_1569_, 2);
v_insterestingCtors_1608_ = lean_ctor_get(v_val_1569_, 3);
v___x_1628_ = lean_array_get_size(v_x_1571_);
v___x_1629_ = lean_nat_dec_lt(v___x_1628_, v_arity_1607_);
if (v___x_1629_ == 0)
{
v___y_1610_ = v___y_1577_;
v___y_1611_ = v___y_1578_;
v___y_1612_ = v___y_1579_;
v___y_1613_ = v___y_1580_;
goto v___jp_1609_;
}
else
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
lean_dec(v_declName_1574_);
lean_dec(v_mvarId_1572_);
lean_dec_ref(v_val_1569_);
v___x_1630_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1);
v___x_1631_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1630_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1631_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1631_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
v___jp_1582_:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1589_ = lean_array_get_borrowed(v___x_1570_, v_x_1571_, v___y_1583_);
lean_dec(v___y_1583_);
v___x_1590_ = l_Lean_Expr_fvarId_x21(v___x_1589_);
v___x_1591_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__0));
v___x_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1592_, 0, v___y_1584_);
v___x_1593_ = l_Lean_MVarId_cases(v_mvarId_1572_, v___x_1590_, v___x_1591_, v___x_1573_, v___x_1592_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; size_t v_sz_1595_; size_t v___x_1596_; lean_object* v___x_1597_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_a_1594_);
lean_dec_ref_known(v___x_1593_, 1);
v_sz_1595_ = lean_array_size(v_a_1594_);
v___x_1596_ = ((size_t)0ULL);
v___x_1597_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5(v_declName_1574_, v_val_1569_, v___x_1573_, v_hasTrace_1575_, v_sz_1595_, v___x_1596_, v_a_1594_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
return v___x_1597_;
}
else
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
lean_dec(v_declName_1574_);
lean_dec_ref(v_val_1569_);
v_a_1598_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v___x_1593_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1593_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
v___jp_1609_:
{
lean_object* v___x_1614_; uint8_t v___x_1615_; 
v___x_1614_ = lean_array_get_borrowed(v___x_1570_, v_x_1571_, v_majorPos_1606_);
v___x_1615_ = l_Lean_Expr_isFVar(v___x_1614_);
if (v___x_1615_ == 0)
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
lean_dec(v_declName_1574_);
lean_dec(v_mvarId_1572_);
lean_dec_ref(v_val_1569_);
v___x_1616_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2);
lean_inc(v___x_1614_);
v___x_1617_ = l_Lean_indentExpr(v___x_1614_);
v___x_1618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1616_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
v___x_1619_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1618_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1619_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1619_);
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
else
{
lean_inc_ref(v_insterestingCtors_1608_);
lean_inc(v_majorPos_1606_);
v___y_1583_ = v_majorPos_1606_;
v___y_1584_ = v_insterestingCtors_1608_;
v___y_1585_ = v___y_1610_;
v___y_1586_ = v___y_1611_;
v___y_1587_ = v___y_1612_;
v___y_1588_ = v___y_1613_;
goto v___jp_1582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___boxed(lean_object* v_val_1640_, lean_object* v___x_1641_, lean_object* v_x_1642_, lean_object* v_mvarId_1643_, lean_object* v___x_1644_, lean_object* v_declName_1645_, lean_object* v_hasTrace_1646_, lean_object* v_____r_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
uint8_t v___x_31871__boxed_1653_; uint8_t v_hasTrace_boxed_1654_; lean_object* v_res_1655_; 
v___x_31871__boxed_1653_ = lean_unbox(v___x_1644_);
v_hasTrace_boxed_1654_ = lean_unbox(v_hasTrace_1646_);
v_res_1655_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(v_val_1640_, v___x_1641_, v_x_1642_, v_mvarId_1643_, v___x_31871__boxed_1653_, v_declName_1645_, v_hasTrace_boxed_1654_, v_____r_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec_ref(v_x_1642_);
lean_dec_ref(v___x_1641_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(lean_object* v___x_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v_options_1662_; uint8_t v_hasTrace_1663_; 
v_options_1662_ = lean_ctor_get(v___y_1659_, 2);
v_hasTrace_1663_ = lean_ctor_get_uint8(v_options_1662_, sizeof(void*)*1);
if (v_hasTrace_1663_ == 0)
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
lean_dec(v___x_1656_);
v___x_1664_ = lean_box(v_hasTrace_1663_);
v___x_1665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1664_);
return v___x_1665_;
}
else
{
lean_object* v_inheritedTraceOptions_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; uint8_t v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v_inheritedTraceOptions_1666_ = lean_ctor_get(v___y_1659_, 13);
v___x_1667_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__8));
v___x_1668_ = l_Lean_Name_append(v___x_1667_, v___x_1656_);
v___x_1669_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1666_, v_options_1662_, v___x_1668_);
lean_dec(v___x_1668_);
v___x_1670_ = lean_box(v___x_1669_);
v___x_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
return v___x_1671_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0___boxed(lean_object* v___x_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v___x_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
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
lean_object* v_declName_1700_; lean_object* v___x_1701_; 
v_declName_1700_ = lean_ctor_get(v_x_1686_, 0);
lean_inc_n(v_declName_1700_, 2);
lean_dec_ref_known(v_x_1686_, 2);
v___x_1701_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_declName_1700_, v___y_1692_);
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v_a_1702_; 
v_a_1702_ = lean_ctor_get(v___x_1701_, 0);
lean_inc(v_a_1702_);
lean_dec_ref_known(v___x_1701_, 1);
if (lean_obj_tag(v_a_1702_) == 1)
{
lean_object* v_options_1703_; lean_object* v_val_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_2014_; 
v_options_1703_ = lean_ctor_get(v___y_1691_, 2);
v_val_1704_ = lean_ctor_get(v_a_1702_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v_a_1702_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_1706_ = v_a_1702_;
v_isShared_1707_ = v_isSharedCheck_2014_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_val_1704_);
lean_dec(v_a_1702_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_2014_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v_inheritedTraceOptions_1708_; uint8_t v_hasTrace_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___y_1713_; lean_object* v___y_1714_; uint8_t v___y_1715_; lean_object* v___y_1748_; lean_object* v_a_1749_; lean_object* v___y_1753_; lean_object* v___y_1756_; lean_object* v___y_1757_; uint8_t v___y_1758_; lean_object* v___y_1791_; lean_object* v_a_1792_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; 
v_inheritedTraceOptions_1708_ = lean_ctor_get(v___y_1691_, 13);
v_hasTrace_1709_ = lean_ctor_get_uint8(v_options_1703_, sizeof(void*)*1);
v___x_1710_ = l_Lean_instInhabitedExpr;
v___x_1711_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5));
if (v_hasTrace_1709_ == 0)
{
lean_object* v_majorPos_1822_; lean_object* v_arity_1823_; lean_object* v_insterestingCtors_1824_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___x_1844_; uint8_t v___x_1845_; 
v_majorPos_1822_ = lean_ctor_get(v_val_1704_, 1);
v_arity_1823_ = lean_ctor_get(v_val_1704_, 2);
v_insterestingCtors_1824_ = lean_ctor_get(v_val_1704_, 3);
v___x_1844_ = lean_array_get_size(v_x_1687_);
v___x_1845_ = lean_nat_dec_lt(v___x_1844_, v_arity_1823_);
if (v___x_1845_ == 0)
{
v___y_1826_ = v___y_1689_;
v___y_1827_ = v___y_1690_;
v___y_1828_ = v___y_1691_;
v___y_1829_ = v___y_1692_;
goto v___jp_1825_;
}
else
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1855_; 
lean_del_object(v___x_1706_);
lean_dec(v_val_1704_);
lean_dec(v_declName_1700_);
lean_dec_ref(v_x_1687_);
lean_dec(v_mvarId_1685_);
v___x_1846_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1);
v___x_1847_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1846_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1850_ = v___x_1847_;
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1847_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
lean_inc(v_a_1848_);
if (v_isShared_1851_ == 0)
{
v___x_1853_ = v___x_1850_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_a_1848_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
v___y_1791_ = v___x_1853_;
v_a_1792_ = v_a_1848_;
goto v___jp_1790_;
}
}
}
v___jp_1825_:
{
lean_object* v___x_1830_; uint8_t v___x_1831_; 
v___x_1830_ = lean_array_get_borrowed(v___x_1710_, v_x_1687_, v_majorPos_1822_);
v___x_1831_ = l_Lean_Expr_isFVar(v___x_1830_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
lean_inc(v___x_1830_);
lean_del_object(v___x_1706_);
lean_dec(v_val_1704_);
lean_dec(v_declName_1700_);
lean_dec_ref(v_x_1687_);
lean_dec(v_mvarId_1685_);
v___x_1832_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2);
v___x_1833_ = l_Lean_indentExpr(v___x_1830_);
v___x_1834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1832_);
lean_ctor_set(v___x_1834_, 1, v___x_1833_);
v___x_1835_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1834_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1838_ = v___x_1835_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1835_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
lean_inc(v_a_1836_);
if (v_isShared_1839_ == 0)
{
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_a_1836_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
v___y_1791_ = v___x_1841_;
v_a_1792_ = v_a_1836_;
goto v___jp_1790_;
}
}
}
else
{
lean_inc(v_majorPos_1822_);
lean_inc_ref(v_insterestingCtors_1824_);
v___y_1796_ = v_insterestingCtors_1824_;
v___y_1797_ = v_majorPos_1822_;
v___y_1798_ = v___y_1826_;
v___y_1799_ = v___y_1827_;
v___y_1800_ = v___y_1828_;
v___y_1801_ = v___y_1829_;
goto v___jp_1795_;
}
}
}
else
{
lean_object* v___f_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; uint8_t v___x_1859_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v_a_1863_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v_a_1878_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; uint8_t v___y_1884_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v_a_1897_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v_a_1916_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v_a_1928_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; uint8_t v___y_1934_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v_a_1947_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; 
lean_del_object(v___x_1706_);
v___f_1856_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1));
v___x_1857_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__6));
v___x_1858_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9);
v___x_1859_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1708_, v_options_1703_, v___x_1858_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1996_; uint8_t v___x_1997_; 
v___x_1996_ = l_Lean_trace_profiler;
v___x_1997_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_options_1703_, v___x_1996_);
if (v___x_1997_ == 0)
{
if (v___x_1859_ == 0)
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1998_ = lean_box(0);
v___x_1999_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(v_val_1704_, v___x_1710_, v_x_1687_, v_mvarId_1685_, v___x_1997_, v_declName_1700_, v_hasTrace_1709_, v___x_1998_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec_ref(v_x_1687_);
v___y_1753_ = v___x_1999_;
goto v___jp_1752_;
}
else
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2000_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3);
lean_inc(v_mvarId_1685_);
v___x_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2001_, 0, v_mvarId_1685_);
v___x_2002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2000_);
lean_ctor_set(v___x_2002_, 1, v___x_2001_);
v___x_2003_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1711_, v___x_2002_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; lean_object* v___x_2005_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_a_2004_);
lean_dec_ref_known(v___x_2003_, 1);
v___x_2005_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(v_val_1704_, v___x_1710_, v_x_1687_, v_mvarId_1685_, v___x_1997_, v_declName_1700_, v_hasTrace_1709_, v_a_2004_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec_ref(v_x_1687_);
v___y_1753_ = v___x_2005_;
goto v___jp_1752_;
}
else
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2013_; 
lean_dec(v_val_1704_);
lean_dec(v_declName_1700_);
lean_dec_ref(v_x_1687_);
lean_dec(v_mvarId_1685_);
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
v___y_1748_ = v___x_2011_;
v_a_1749_ = v_a_2006_;
goto v___jp_1747_;
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
v___x_1874_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_1711_, v_hasTrace_1709_, v___x_1857_, v_options_1703_, v___x_1859_, v___y_1862_, v___f_1856_, v___x_1873_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
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
v___x_1885_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v___x_1711_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1886_);
lean_dec_ref(v___x_1885_);
v___x_1887_ = lean_unbox(v_a_1886_);
lean_dec(v_a_1886_);
if (v___x_1887_ == 0)
{
v___y_1876_ = v___y_1881_;
v___y_1877_ = v___y_1882_;
v_a_1878_ = v___y_1883_;
goto v___jp_1875_;
}
else
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1888_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1);
lean_inc_ref(v___y_1883_);
v___x_1889_ = l_Lean_Exception_toMessageData(v___y_1883_);
v___x_1890_ = l_Lean_indentD(v___x_1889_);
v___x_1891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1888_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
v___x_1892_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1711_, v___x_1891_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_dec_ref_known(v___x_1892_, 1);
v___y_1876_ = v___y_1881_;
v___y_1877_ = v___y_1882_;
v_a_1878_ = v___y_1883_;
goto v___jp_1875_;
}
else
{
lean_object* v_a_1893_; 
lean_dec_ref(v___y_1883_);
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_a_1893_);
lean_dec_ref_known(v___x_1892_, 1);
v___y_1876_ = v___y_1881_;
v___y_1877_ = v___y_1882_;
v_a_1878_ = v_a_1893_;
goto v___jp_1875_;
}
}
}
else
{
v___y_1876_ = v___y_1881_;
v___y_1877_ = v___y_1882_;
v_a_1878_ = v___y_1883_;
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
v___y_1882_ = v___y_1896_;
v___y_1883_ = v_a_1897_;
v___y_1884_ = v___x_1899_;
goto v___jp_1880_;
}
else
{
v___y_1881_ = v___y_1895_;
v___y_1882_ = v___y_1896_;
v___y_1883_ = v_a_1897_;
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
v___x_1918_ = lean_float_of_nat(v___y_1915_);
v___x_1919_ = lean_float_of_nat(v___x_1917_);
v___x_1920_ = lean_box_float(v___x_1918_);
v___x_1921_ = lean_box_float(v___x_1919_);
v___x_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1920_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1923_, 0, v_a_1916_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
v___x_1924_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_1711_, v_hasTrace_1709_, v___x_1857_, v_options_1703_, v___x_1859_, v___y_1914_, v___f_1856_, v___x_1923_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
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
v___x_1935_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v___x_1711_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
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
v___x_1942_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1711_, v___x_1941_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
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
v___x_1964_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___y_1692_);
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
v___x_1970_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_options_1703_, v___x_1969_);
if (v___x_1970_ == 0)
{
lean_object* v___x_1971_; 
v___x_1971_ = lean_io_mono_nanos_now();
if (v___x_1859_ == 0)
{
lean_object* v___x_1972_; lean_object* v___x_1973_; 
lean_del_object(v___x_1967_);
v___x_1972_ = lean_box(0);
v___x_1973_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(v_val_1704_, v___x_1710_, v_x_1687_, v_mvarId_1685_, v___x_1970_, v_declName_1700_, v_hasTrace_1709_, v___x_1972_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec_ref(v_x_1687_);
v___y_1901_ = v___x_1971_;
v___y_1902_ = v_a_1965_;
v___y_1903_ = v___x_1973_;
goto v___jp_1900_;
}
else
{
lean_object* v___x_1974_; lean_object* v___x_1976_; 
v___x_1974_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3);
lean_inc(v_mvarId_1685_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set_tag(v___x_1967_, 1);
lean_ctor_set(v___x_1967_, 0, v_mvarId_1685_);
v___x_1976_ = v___x_1967_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_mvarId_1685_);
v___x_1976_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1974_);
lean_ctor_set(v___x_1977_, 1, v___x_1976_);
v___x_1978_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1711_, v___x_1977_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v___x_1980_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_1979_);
lean_dec_ref_known(v___x_1978_, 1);
v___x_1980_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(v_val_1704_, v___x_1710_, v_x_1687_, v_mvarId_1685_, v___x_1970_, v_declName_1700_, v_hasTrace_1709_, v_a_1979_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec_ref(v_x_1687_);
v___y_1901_ = v___x_1971_;
v___y_1902_ = v_a_1965_;
v___y_1903_ = v___x_1980_;
goto v___jp_1900_;
}
else
{
lean_object* v_a_1981_; 
lean_dec(v_val_1704_);
lean_dec(v_declName_1700_);
lean_dec_ref(v_x_1687_);
lean_dec(v_mvarId_1685_);
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
v___x_1985_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(v_val_1704_, v___x_1710_, v_x_1687_, v_mvarId_1685_, v_declName_1700_, v___x_1970_, v___x_1984_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec_ref(v_x_1687_);
v___y_1951_ = v_a_1965_;
v___y_1952_ = v___x_1983_;
v___y_1953_ = v___x_1985_;
goto v___jp_1950_;
}
else
{
lean_object* v___x_1986_; lean_object* v___x_1988_; 
v___x_1986_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3);
lean_inc(v_mvarId_1685_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set_tag(v___x_1967_, 1);
lean_ctor_set(v___x_1967_, 0, v_mvarId_1685_);
v___x_1988_ = v___x_1967_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_mvarId_1685_);
v___x_1988_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1986_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
v___x_1990_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1711_, v___x_1989_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v___x_1992_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_1991_);
lean_dec_ref_known(v___x_1990_, 1);
v___x_1992_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(v_val_1704_, v___x_1710_, v_x_1687_, v_mvarId_1685_, v_declName_1700_, v___x_1970_, v_a_1991_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec_ref(v_x_1687_);
v___y_1951_ = v_a_1965_;
v___y_1952_ = v___x_1983_;
v___y_1953_ = v___x_1992_;
goto v___jp_1950_;
}
else
{
lean_object* v_a_1993_; 
lean_dec(v_val_1704_);
lean_dec(v_declName_1700_);
lean_dec_ref(v_x_1687_);
lean_dec(v_mvarId_1685_);
v_a_1993_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_1993_);
lean_dec_ref_known(v___x_1990_, 1);
v___y_1945_ = v_a_1965_;
v___y_1946_ = v___x_1983_;
v_a_1947_ = v_a_1993_;
goto v___jp_1944_;
}
}
}
}
}
}
}
v___jp_1712_:
{
if (v___y_1715_ == 0)
{
lean_object* v___x_1716_; lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1746_; 
lean_dec_ref(v___y_1713_);
v___x_1716_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v___x_1711_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1719_ = v___x_1716_;
v_isShared_1720_ = v_isSharedCheck_1746_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1716_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1746_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
uint8_t v___x_1721_; 
v___x_1721_ = lean_unbox(v_a_1717_);
lean_dec(v_a_1717_);
if (v___x_1721_ == 0)
{
lean_object* v___x_1723_; 
if (v_isShared_1720_ == 0)
{
lean_ctor_set_tag(v___x_1719_, 1);
lean_ctor_set(v___x_1719_, 0, v___y_1714_);
v___x_1723_ = v___x_1719_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___y_1714_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
else
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
lean_del_object(v___x_1719_);
v___x_1725_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1);
lean_inc_ref(v___y_1714_);
v___x_1726_ = l_Lean_Exception_toMessageData(v___y_1714_);
v___x_1727_ = l_Lean_indentD(v___x_1726_);
v___x_1728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1725_);
lean_ctor_set(v___x_1728_, 1, v___x_1727_);
v___x_1729_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1711_, v___x_1728_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1736_; 
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1736_ == 0)
{
lean_object* v_unused_1737_; 
v_unused_1737_ = lean_ctor_get(v___x_1729_, 0);
lean_dec(v_unused_1737_);
v___x_1731_ = v___x_1729_;
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
else
{
lean_dec(v___x_1729_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
lean_ctor_set_tag(v___x_1731_, 1);
lean_ctor_set(v___x_1731_, 0, v___y_1714_);
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___y_1714_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
else
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1745_; 
lean_dec_ref(v___y_1714_);
v_a_1738_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1740_ = v___x_1729_;
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1729_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1743_; 
if (v_isShared_1741_ == 0)
{
v___x_1743_ = v___x_1740_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1738_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_1714_);
return v___y_1713_;
}
}
v___jp_1747_:
{
uint8_t v___x_1750_; 
v___x_1750_ = l_Lean_Exception_isInterrupt(v_a_1749_);
if (v___x_1750_ == 0)
{
uint8_t v___x_1751_; 
lean_inc_ref(v_a_1749_);
v___x_1751_ = l_Lean_Exception_isRuntime(v_a_1749_);
v___y_1713_ = v___y_1748_;
v___y_1714_ = v_a_1749_;
v___y_1715_ = v___x_1751_;
goto v___jp_1712_;
}
else
{
v___y_1713_ = v___y_1748_;
v___y_1714_ = v_a_1749_;
v___y_1715_ = v___x_1750_;
goto v___jp_1712_;
}
}
v___jp_1752_:
{
if (lean_obj_tag(v___y_1753_) == 0)
{
return v___y_1753_;
}
else
{
lean_object* v_a_1754_; 
v_a_1754_ = lean_ctor_get(v___y_1753_, 0);
lean_inc(v_a_1754_);
v___y_1748_ = v___y_1753_;
v_a_1749_ = v_a_1754_;
goto v___jp_1747_;
}
}
v___jp_1755_:
{
if (v___y_1758_ == 0)
{
lean_object* v___x_1759_; lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1789_; 
lean_dec_ref(v___y_1756_);
v___x_1759_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v___x_1711_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1762_ = v___x_1759_;
v_isShared_1763_ = v_isSharedCheck_1789_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1759_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1789_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
uint8_t v___x_1764_; 
v___x_1764_ = lean_unbox(v_a_1760_);
lean_dec(v_a_1760_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1766_; 
if (v_isShared_1763_ == 0)
{
lean_ctor_set_tag(v___x_1762_, 1);
lean_ctor_set(v___x_1762_, 0, v___y_1757_);
v___x_1766_ = v___x_1762_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___y_1757_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
else
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
lean_del_object(v___x_1762_);
v___x_1768_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1);
lean_inc_ref(v___y_1757_);
v___x_1769_ = l_Lean_Exception_toMessageData(v___y_1757_);
v___x_1770_ = l_Lean_indentD(v___x_1769_);
v___x_1771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1768_);
lean_ctor_set(v___x_1771_, 1, v___x_1770_);
v___x_1772_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1711_, v___x_1771_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1779_ == 0)
{
lean_object* v_unused_1780_; 
v_unused_1780_ = lean_ctor_get(v___x_1772_, 0);
lean_dec(v_unused_1780_);
v___x_1774_ = v___x_1772_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_dec(v___x_1772_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
lean_ctor_set_tag(v___x_1774_, 1);
lean_ctor_set(v___x_1774_, 0, v___y_1757_);
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___y_1757_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_dec_ref(v___y_1757_);
v_a_1781_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1772_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1772_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_1757_);
return v___y_1756_;
}
}
v___jp_1790_:
{
uint8_t v___x_1793_; 
v___x_1793_ = l_Lean_Exception_isInterrupt(v_a_1792_);
if (v___x_1793_ == 0)
{
uint8_t v___x_1794_; 
lean_inc_ref(v_a_1792_);
v___x_1794_ = l_Lean_Exception_isRuntime(v_a_1792_);
v___y_1756_ = v___y_1791_;
v___y_1757_ = v_a_1792_;
v___y_1758_ = v___x_1794_;
goto v___jp_1755_;
}
else
{
v___y_1756_ = v___y_1791_;
v___y_1757_ = v_a_1792_;
v___y_1758_ = v___x_1793_;
goto v___jp_1755_;
}
}
v___jp_1795_:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1806_; 
v___x_1802_ = lean_array_get(v___x_1710_, v_x_1687_, v___y_1797_);
lean_dec(v___y_1797_);
lean_dec_ref(v_x_1687_);
v___x_1803_ = l_Lean_Expr_fvarId_x21(v___x_1802_);
lean_dec(v___x_1802_);
v___x_1804_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__0));
if (v_isShared_1707_ == 0)
{
lean_ctor_set(v___x_1706_, 0, v___y_1796_);
v___x_1806_ = v___x_1706_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___y_1796_);
v___x_1806_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Lean_MVarId_cases(v_mvarId_1685_, v___x_1803_, v___x_1804_, v_hasTrace_1709_, v___x_1806_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; size_t v_sz_1809_; size_t v___x_1810_; lean_object* v___x_1811_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_a_1808_);
lean_dec_ref_known(v___x_1807_, 1);
v_sz_1809_ = lean_array_size(v_a_1808_);
v___x_1810_ = ((size_t)0ULL);
v___x_1811_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(v_declName_1700_, v_val_1704_, v_hasTrace_1709_, v_sz_1809_, v___x_1810_, v_a_1808_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
if (lean_obj_tag(v___x_1811_) == 0)
{
return v___x_1811_;
}
else
{
lean_object* v_a_1812_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_a_1812_);
v___y_1791_ = v___x_1811_;
v_a_1792_ = v_a_1812_;
goto v___jp_1790_;
}
}
else
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
lean_dec(v_val_1704_);
lean_dec(v_declName_1700_);
v_a_1813_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1807_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1807_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
lean_inc(v_a_1813_);
if (v_isShared_1816_ == 0)
{
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
v___y_1791_ = v___x_1818_;
v_a_1792_ = v_a_1813_;
goto v___jp_1790_;
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
lean_dec(v_a_1702_);
lean_dec(v_declName_1700_);
lean_dec_ref(v_x_1687_);
lean_dec(v_mvarId_1685_);
v___x_2015_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12);
v___x_2016_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_2015_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
return v___x_2016_;
}
}
else
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
lean_dec(v_declName_1700_);
lean_dec_ref(v_x_1687_);
lean_dec(v_mvarId_1685_);
v_a_2017_ = lean_ctor_get(v___x_1701_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_1701_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_1701_);
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
lean_dec_ref(v_x_1687_);
lean_dec_ref(v_x_1686_);
lean_dec(v_mvarId_1685_);
v___x_2025_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14);
v___x_2026_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_2025_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
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
v_dummy_2049_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0);
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
