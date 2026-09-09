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
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_10538__overap_213_; lean_object* v___x_214_; 
v___x_211_ = lean_box(0);
v___x_212_ = l_instInhabitedOfMonad___redArg(v___x_210_, v___x_211_);
v___x_10538__overap_213_ = lean_panic_fn_borrowed(v___x_212_, v_msg_156_);
lean_dec(v___x_212_);
lean_inc(v___y_160_);
lean_inc_ref(v___y_159_);
lean_inc(v___y_158_);
lean_inc_ref(v___y_157_);
v___x_214_ = lean_apply_5(v___x_10538__overap_213_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, lean_box(0));
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
v_options_245_ = lean_ctor_get(v___y_237_, 1);
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
v_ref_262_ = lean_ctor_get(v___y_259_, 4);
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
uint8_t v___x_14307__boxed_560_; lean_object* v_res_561_; 
v___x_14307__boxed_560_ = lean_unbox(v___x_553_);
v_res_561_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(v___x_14307__boxed_560_, v___f_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
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
lean_object* v_toCold_645_; lean_object* v_options_646_; lean_object* v_currRecDepth_647_; lean_object* v_maxRecDepth_648_; lean_object* v_ref_649_; lean_object* v_currNamespace_650_; lean_object* v_openDecls_651_; lean_object* v_initHeartbeats_652_; lean_object* v_maxHeartbeats_653_; lean_object* v_currMacroScope_654_; uint8_t v_diag_655_; uint8_t v_suppressElabErrors_656_; lean_object* v___x_657_; lean_object* v_traceState_658_; lean_object* v_traces_659_; lean_object* v_ref_660_; lean_object* v___x_661_; lean_object* v___x_662_; size_t v_sz_663_; size_t v___x_664_; lean_object* v___x_665_; lean_object* v_msg_666_; lean_object* v___x_667_; lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_705_; 
v_toCold_645_ = lean_ctor_get(v___y_642_, 0);
v_options_646_ = lean_ctor_get(v___y_642_, 1);
v_currRecDepth_647_ = lean_ctor_get(v___y_642_, 2);
v_maxRecDepth_648_ = lean_ctor_get(v___y_642_, 3);
v_ref_649_ = lean_ctor_get(v___y_642_, 4);
v_currNamespace_650_ = lean_ctor_get(v___y_642_, 5);
v_openDecls_651_ = lean_ctor_get(v___y_642_, 6);
v_initHeartbeats_652_ = lean_ctor_get(v___y_642_, 7);
v_maxHeartbeats_653_ = lean_ctor_get(v___y_642_, 8);
v_currMacroScope_654_ = lean_ctor_get(v___y_642_, 9);
v_diag_655_ = lean_ctor_get_uint8(v___y_642_, sizeof(void*)*10);
v_suppressElabErrors_656_ = lean_ctor_get_uint8(v___y_642_, sizeof(void*)*10 + 1);
v___x_657_ = lean_st_ref_get(v___y_643_);
v_traceState_658_ = lean_ctor_get(v___x_657_, 4);
lean_inc_ref(v_traceState_658_);
lean_dec(v___x_657_);
v_traces_659_ = lean_ctor_get(v_traceState_658_, 0);
lean_inc_ref(v_traces_659_);
lean_dec_ref(v_traceState_658_);
v_ref_660_ = l_Lean_replaceRef(v_ref_638_, v_ref_649_);
lean_inc(v_currMacroScope_654_);
lean_inc(v_maxHeartbeats_653_);
lean_inc(v_initHeartbeats_652_);
lean_inc(v_openDecls_651_);
lean_inc(v_currNamespace_650_);
lean_inc(v_maxRecDepth_648_);
lean_inc(v_currRecDepth_647_);
lean_inc_ref(v_options_646_);
lean_inc_ref(v_toCold_645_);
v___x_661_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_661_, 0, v_toCold_645_);
lean_ctor_set(v___x_661_, 1, v_options_646_);
lean_ctor_set(v___x_661_, 2, v_currRecDepth_647_);
lean_ctor_set(v___x_661_, 3, v_maxRecDepth_648_);
lean_ctor_set(v___x_661_, 4, v_ref_660_);
lean_ctor_set(v___x_661_, 5, v_currNamespace_650_);
lean_ctor_set(v___x_661_, 6, v_openDecls_651_);
lean_ctor_set(v___x_661_, 7, v_initHeartbeats_652_);
lean_ctor_set(v___x_661_, 8, v_maxHeartbeats_653_);
lean_ctor_set(v___x_661_, 9, v_currMacroScope_654_);
lean_ctor_set_uint8(v___x_661_, sizeof(void*)*10, v_diag_655_);
lean_ctor_set_uint8(v___x_661_, sizeof(void*)*10 + 1, v_suppressElabErrors_656_);
v___x_662_ = l_Lean_PersistentArray_toArray___redArg(v_traces_659_);
lean_dec_ref(v_traces_659_);
v_sz_663_ = lean_array_size(v___x_662_);
v___x_664_ = ((size_t)0ULL);
v___x_665_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__9_spec__10(v_sz_663_, v___x_664_, v___x_662_);
v_msg_666_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_666_, 0, v_data_637_);
lean_ctor_set(v_msg_666_, 1, v_msg_639_);
lean_ctor_set(v_msg_666_, 2, v___x_665_);
v___x_667_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msg_666_, v___y_640_, v___y_641_, v___x_661_, v___y_643_);
lean_dec_ref_known(v___x_661_, 10);
v_a_668_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_705_ == 0)
{
v___x_670_ = v___x_667_;
v_isShared_671_ = v_isSharedCheck_705_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_667_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_705_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_672_; lean_object* v_traceState_673_; lean_object* v_env_674_; lean_object* v_nextMacroScope_675_; lean_object* v_ngen_676_; lean_object* v_auxDeclNGen_677_; lean_object* v_cache_678_; lean_object* v_messages_679_; lean_object* v_infoState_680_; lean_object* v_snapshotTasks_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_704_; 
v___x_672_ = lean_st_ref_take(v___y_643_);
v_traceState_673_ = lean_ctor_get(v___x_672_, 4);
v_env_674_ = lean_ctor_get(v___x_672_, 0);
v_nextMacroScope_675_ = lean_ctor_get(v___x_672_, 1);
v_ngen_676_ = lean_ctor_get(v___x_672_, 2);
v_auxDeclNGen_677_ = lean_ctor_get(v___x_672_, 3);
v_cache_678_ = lean_ctor_get(v___x_672_, 5);
v_messages_679_ = lean_ctor_get(v___x_672_, 6);
v_infoState_680_ = lean_ctor_get(v___x_672_, 7);
v_snapshotTasks_681_ = lean_ctor_get(v___x_672_, 8);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_704_ == 0)
{
v___x_683_ = v___x_672_;
v_isShared_684_ = v_isSharedCheck_704_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_snapshotTasks_681_);
lean_inc(v_infoState_680_);
lean_inc(v_messages_679_);
lean_inc(v_cache_678_);
lean_inc(v_traceState_673_);
lean_inc(v_auxDeclNGen_677_);
lean_inc(v_ngen_676_);
lean_inc(v_nextMacroScope_675_);
lean_inc(v_env_674_);
lean_dec(v___x_672_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_704_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
uint64_t v_tid_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_702_; 
v_tid_685_ = lean_ctor_get_uint64(v_traceState_673_, sizeof(void*)*1);
v_isSharedCheck_702_ = !lean_is_exclusive(v_traceState_673_);
if (v_isSharedCheck_702_ == 0)
{
lean_object* v_unused_703_; 
v_unused_703_ = lean_ctor_get(v_traceState_673_, 0);
lean_dec(v_unused_703_);
v___x_687_ = v_traceState_673_;
v_isShared_688_ = v_isSharedCheck_702_;
goto v_resetjp_686_;
}
else
{
lean_dec(v_traceState_673_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_702_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_692_; 
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v_ref_638_);
lean_ctor_set(v___x_689_, 1, v_a_668_);
v___x_690_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_636_, v___x_689_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v___x_690_);
v___x_692_ = v___x_687_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_690_);
lean_ctor_set_uint64(v_reuseFailAlloc_701_, sizeof(void*)*1, v_tid_685_);
v___x_692_ = v_reuseFailAlloc_701_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v___x_694_; 
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 4, v___x_692_);
v___x_694_ = v___x_683_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_env_674_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_nextMacroScope_675_);
lean_ctor_set(v_reuseFailAlloc_700_, 2, v_ngen_676_);
lean_ctor_set(v_reuseFailAlloc_700_, 3, v_auxDeclNGen_677_);
lean_ctor_set(v_reuseFailAlloc_700_, 4, v___x_692_);
lean_ctor_set(v_reuseFailAlloc_700_, 5, v_cache_678_);
lean_ctor_set(v_reuseFailAlloc_700_, 6, v_messages_679_);
lean_ctor_set(v_reuseFailAlloc_700_, 7, v_infoState_680_);
lean_ctor_set(v_reuseFailAlloc_700_, 8, v_snapshotTasks_681_);
v___x_694_ = v_reuseFailAlloc_700_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_698_; 
v___x_695_ = lean_st_ref_put(v___y_643_, v___x_694_);
v___x_696_ = lean_box(0);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_696_);
v___x_698_ = v___x_670_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_696_);
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
lean_object* v_fst_736_; lean_object* v_snd_737_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v_data_741_; lean_object* v_fst_752_; lean_object* v_snd_753_; lean_object* v___x_754_; uint8_t v___x_755_; lean_object* v___y_757_; lean_object* v_a_758_; uint8_t v___y_773_; double v___y_804_; 
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
lean_object* v___x_809_; uint8_t v___x_810_; 
v___x_809_ = l_Lean_trace_profiler_useHeartbeats;
v___x_810_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_opts_726_, v___x_809_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; lean_object* v___x_812_; double v___x_813_; double v___x_814_; double v___x_815_; 
v___x_811_ = l_Lean_trace_profiler_threshold;
v___x_812_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12(v_opts_726_, v___x_811_);
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
v___x_817_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12(v_opts_726_, v___x_816_);
v___x_818_ = lean_float_of_nat(v___x_817_);
v___y_804_ = v___x_818_;
goto v___jp_803_;
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
v_ref_768_ = lean_ctor_get(v___y_733_, 4);
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
lean_object* v___x_774_; lean_object* v_traceState_775_; lean_object* v_env_776_; lean_object* v_nextMacroScope_777_; lean_object* v_ngen_778_; lean_object* v_auxDeclNGen_779_; lean_object* v_cache_780_; lean_object* v_messages_781_; lean_object* v_infoState_782_; lean_object* v_snapshotTasks_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_802_; 
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
v_messages_781_ = lean_ctor_get(v___x_774_, 6);
v_infoState_782_ = lean_ctor_get(v___x_774_, 7);
v_snapshotTasks_783_ = lean_ctor_get(v___x_774_, 8);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_802_ == 0)
{
v___x_785_ = v___x_774_;
v_isShared_786_ = v_isSharedCheck_802_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_snapshotTasks_783_);
lean_inc(v_infoState_782_);
lean_inc(v_messages_781_);
lean_inc(v_cache_780_);
lean_inc(v_traceState_775_);
lean_inc(v_auxDeclNGen_779_);
lean_inc(v_ngen_778_);
lean_inc(v_nextMacroScope_777_);
lean_inc(v_env_776_);
lean_dec(v___x_774_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_802_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
uint64_t v_tid_787_; lean_object* v_traces_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_801_; 
v_tid_787_ = lean_ctor_get_uint64(v_traceState_775_, sizeof(void*)*1);
v_traces_788_ = lean_ctor_get(v_traceState_775_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v_traceState_775_);
if (v_isSharedCheck_801_ == 0)
{
v___x_790_ = v_traceState_775_;
v_isShared_791_ = v_isSharedCheck_801_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_traces_788_);
lean_dec(v_traceState_775_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_801_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_792_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_728_, v_traces_788_);
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
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_env_776_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v_nextMacroScope_777_);
lean_ctor_set(v_reuseFailAlloc_799_, 2, v_ngen_778_);
lean_ctor_set(v_reuseFailAlloc_799_, 3, v_auxDeclNGen_779_);
lean_ctor_set(v_reuseFailAlloc_799_, 4, v___x_794_);
lean_ctor_set(v_reuseFailAlloc_799_, 5, v_cache_780_);
lean_ctor_set(v_reuseFailAlloc_799_, 6, v_messages_781_);
lean_ctor_set(v_reuseFailAlloc_799_, 7, v_infoState_782_);
lean_ctor_set(v_reuseFailAlloc_799_, 8, v_snapshotTasks_783_);
v___x_796_ = v_reuseFailAlloc_799_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_st_ref_put(v___y_734_, v___x_796_);
v___x_798_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg(v_fst_736_);
return v___x_798_;
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
v___jp_803_:
{
double v___x_805_; double v___x_806_; double v___x_807_; uint8_t v___x_808_; 
v___x_805_ = lean_unbox_float(v_snd_753_);
v___x_806_ = lean_unbox_float(v_fst_752_);
v___x_807_ = lean_float_sub(v___x_805_, v___x_806_);
v___x_808_ = lean_float_decLt(v___y_804_, v___x_807_);
v___y_773_ = v___x_808_;
goto v___jp_772_;
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
lean_object* v_declName_875_; lean_object* v___x_876_; 
v_declName_875_ = lean_ctor_get(v_x_861_, 0);
lean_inc_n(v_declName_875_, 2);
lean_dec_ref_known(v_x_861_, 2);
v___x_876_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_declName_875_, v___y_867_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_a_877_);
lean_dec_ref_known(v___x_876_, 1);
if (lean_obj_tag(v_a_877_) == 1)
{
lean_object* v_val_878_; lean_object* v_options_879_; lean_object* v_majorPos_880_; lean_object* v_arity_881_; lean_object* v_insterestingCtors_882_; lean_object* v_toCold_883_; uint8_t v_hasTrace_884_; lean_object* v___f_885_; lean_object* v___x_886_; lean_object* v___f_887_; lean_object* v___x_888_; uint8_t v___x_889_; 
v_val_878_ = lean_ctor_get(v_a_877_, 0);
lean_inc(v_val_878_);
lean_dec_ref_known(v_a_877_, 1);
v_options_879_ = lean_ctor_get(v___y_866_, 1);
v_majorPos_880_ = lean_ctor_get(v_val_878_, 1);
lean_inc(v_majorPos_880_);
v_arity_881_ = lean_ctor_get(v_val_878_, 2);
lean_inc_n(v_arity_881_, 2);
v_insterestingCtors_882_ = lean_ctor_get(v_val_878_, 3);
lean_inc_ref(v_insterestingCtors_882_);
lean_dec(v_val_878_);
v_toCold_883_ = lean_ctor_get(v___y_866_, 0);
v_hasTrace_884_ = lean_ctor_get_uint8(v_options_879_, sizeof(void*)*1);
v___f_885_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0));
v___x_886_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_x_862_);
v___f_887_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___boxed), 15, 9);
lean_closure_set(v___f_887_, 0, v___x_886_);
lean_closure_set(v___f_887_, 1, v_x_862_);
lean_closure_set(v___f_887_, 2, v_majorPos_880_);
lean_closure_set(v___f_887_, 3, v_insterestingCtors_882_);
lean_closure_set(v___f_887_, 4, v_declName_875_);
lean_closure_set(v___f_887_, 5, v_snd_859_);
lean_closure_set(v___f_887_, 6, v_arity_881_);
lean_closure_set(v___f_887_, 7, v_mvarId_860_);
lean_closure_set(v___f_887_, 8, v___f_885_);
v___x_888_ = lean_array_get_size(v_x_862_);
lean_dec_ref(v_x_862_);
v___x_889_ = lean_nat_dec_lt(v___x_888_, v_arity_881_);
lean_dec(v_arity_881_);
if (v_hasTrace_884_ == 0)
{
lean_object* v___x_890_; 
v___x_890_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(v___x_889_, v___f_887_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
return v___x_890_;
}
else
{
lean_object* v_inheritedTraceOptions_891_; lean_object* v___f_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; uint8_t v___x_896_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v_a_900_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v_a_915_; 
v_inheritedTraceOptions_891_ = lean_ctor_get(v_toCold_883_, 4);
v___f_892_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1));
v___x_893_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5));
v___x_894_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__6));
v___x_895_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9);
v___x_896_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_891_, v_options_879_, v___x_895_);
if (v___x_896_ == 0)
{
lean_object* v___x_965_; uint8_t v___x_966_; 
v___x_965_ = l_Lean_trace_profiler;
v___x_966_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_options_879_, v___x_965_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(v___x_889_, v___f_887_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
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
v___x_911_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_893_, v_hasTrace_884_, v___x_894_, v_options_879_, v___x_896_, v___y_899_, v___f_892_, v___x_910_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
return v___x_911_;
}
v___jp_912_:
{
lean_object* v___x_916_; double v___x_917_; double v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_916_ = lean_io_get_num_heartbeats();
v___x_917_ = lean_float_of_nat(v___y_913_);
v___x_918_ = lean_float_of_nat(v___x_916_);
v___x_919_ = lean_box_float(v___x_917_);
v___x_920_ = lean_box_float(v___x_918_);
v___x_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_919_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
v___x_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_922_, 0, v_a_915_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_893_, v_hasTrace_884_, v___x_894_, v_options_879_, v___x_896_, v___y_914_, v___f_892_, v___x_922_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
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
v___x_928_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_options_879_, v___x_927_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = lean_io_mono_nanos_now();
v___x_930_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(v___x_889_, v___f_887_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
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
v___x_948_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(v___x_889_, v___f_887_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
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
v___y_913_ = v___x_947_;
v___y_914_ = v_a_926_;
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
v___y_913_ = v___x_947_;
v___y_914_ = v_a_926_;
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
lean_dec(v_a_877_);
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
v_a_970_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_876_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_876_);
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
v_dummy_1006_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0);
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
v_dummy_1167_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0);
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
uint8_t v___y_31240__boxed_1237_; uint8_t v___x_31245__boxed_1238_; lean_object* v_res_1239_; 
v___y_31240__boxed_1237_ = lean_unbox(v___y_1224_);
v___x_31245__boxed_1238_ = lean_unbox(v___x_1231_);
v_res_1239_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0(v___y_31240__boxed_1237_, v_mvarId_1225_, v___f_1226_, v_declName_1227_, v_val_1228_, v___x_1229_, v_fields_1230_, v___x_31245__boxed_1238_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
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
uint8_t v___x_31424__boxed_1292_; size_t v_sz_boxed_1293_; size_t v_i_boxed_1294_; lean_object* v_res_1295_; 
v___x_31424__boxed_1292_ = lean_unbox(v___x_1283_);
v_sz_boxed_1293_ = lean_unbox_usize(v_sz_1284_);
lean_dec(v_sz_1284_);
v_i_boxed_1294_ = lean_unbox_usize(v_i_1285_);
lean_dec(v_i_1285_);
v_res_1295_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(v_declName_1281_, v_val_1282_, v___x_31424__boxed_1292_, v_sz_boxed_1293_, v_i_boxed_1294_, v_bs_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(lean_object* v_declName_1296_, lean_object* v_val_1297_, uint8_t v___x_1298_, size_t v_sz_1299_, size_t v_i_1300_, lean_object* v_bs_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
uint8_t v___x_1307_; 
v___x_1307_ = lean_usize_dec_lt(v_i_1300_, v_sz_1299_);
if (v___x_1307_ == 0)
{
lean_object* v___x_1308_; 
lean_dec_ref(v_val_1297_);
lean_dec(v_declName_1296_);
v___x_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1308_, 0, v_bs_1301_);
return v___x_1308_;
}
else
{
lean_object* v_v_1309_; lean_object* v_toInductionSubgoal_1310_; lean_object* v_ctorName_1311_; lean_object* v_mvarId_1312_; lean_object* v_fields_1313_; lean_object* v___f_1314_; lean_object* v___x_1315_; uint8_t v___x_1316_; lean_object* v___x_1317_; lean_object* v_bs_x27_1318_; uint8_t v___y_1320_; 
v_v_1309_ = lean_array_uget_borrowed(v_bs_1301_, v_i_1300_);
v_toInductionSubgoal_1310_ = lean_ctor_get(v_v_1309_, 0);
v_ctorName_1311_ = lean_ctor_get(v_v_1309_, 1);
lean_inc(v_ctorName_1311_);
v_mvarId_1312_ = lean_ctor_get(v_toInductionSubgoal_1310_, 0);
lean_inc(v_mvarId_1312_);
v_fields_1313_ = lean_ctor_get(v_toInductionSubgoal_1310_, 1);
lean_inc_ref(v_fields_1313_);
v___f_1314_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0));
v___x_1315_ = l_Lean_instInhabitedExpr;
v___x_1316_ = 0;
v___x_1317_ = lean_unsigned_to_nat(0u);
v_bs_x27_1318_ = lean_array_uset(v_bs_1301_, v_i_1300_, v___x_1317_);
if (lean_obj_tag(v_ctorName_1311_) == 0)
{
v___y_1320_ = v___x_1298_;
goto v___jp_1319_;
}
else
{
lean_dec_ref_known(v_ctorName_1311_, 1);
v___y_1320_ = v___x_1316_;
goto v___jp_1319_;
}
v___jp_1319_:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___y_1323_; lean_object* v___x_1324_; 
v___x_1321_ = lean_box(v___y_1320_);
v___x_1322_ = lean_box(v___x_1316_);
lean_inc_ref(v_val_1297_);
lean_inc(v_declName_1296_);
lean_inc(v_mvarId_1312_);
v___y_1323_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed), 13, 8);
lean_closure_set(v___y_1323_, 0, v___x_1321_);
lean_closure_set(v___y_1323_, 1, v_mvarId_1312_);
lean_closure_set(v___y_1323_, 2, v___f_1314_);
lean_closure_set(v___y_1323_, 3, v_declName_1296_);
lean_closure_set(v___y_1323_, 4, v_val_1297_);
lean_closure_set(v___y_1323_, 5, v___x_1315_);
lean_closure_set(v___y_1323_, 6, v_fields_1313_);
lean_closure_set(v___y_1323_, 7, v___x_1322_);
v___x_1324_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1312_, v___y_1323_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; size_t v___x_1326_; size_t v___x_1327_; lean_object* v___x_1328_; 
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_a_1325_);
lean_dec_ref_known(v___x_1324_, 1);
v___x_1326_ = ((size_t)1ULL);
v___x_1327_ = lean_usize_add(v_i_1300_, v___x_1326_);
v___x_1328_ = lean_array_uset(v_bs_x27_1318_, v_i_1300_, v_a_1325_);
v_i_1300_ = v___x_1327_;
v_bs_1301_ = v___x_1328_;
goto _start;
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
lean_dec_ref(v_bs_x27_1318_);
lean_dec_ref(v_val_1297_);
lean_dec(v_declName_1296_);
v_a_1330_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1332_ = v___x_1324_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1324_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4___boxed(lean_object* v_declName_1338_, lean_object* v_val_1339_, lean_object* v___x_1340_, lean_object* v_sz_1341_, lean_object* v_i_1342_, lean_object* v_bs_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
uint8_t v___x_31498__boxed_1349_; size_t v_sz_boxed_1350_; size_t v_i_boxed_1351_; lean_object* v_res_1352_; 
v___x_31498__boxed_1349_ = lean_unbox(v___x_1340_);
v_sz_boxed_1350_ = lean_unbox_usize(v_sz_1341_);
lean_dec(v_sz_1341_);
v_i_boxed_1351_ = lean_unbox_usize(v_i_1342_);
lean_dec(v_i_1342_);
v_res_1352_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(v_declName_1338_, v_val_1339_, v___x_31498__boxed_1349_, v_sz_boxed_1350_, v_i_boxed_1351_, v_bs_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
return v_res_1352_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__1));
v___x_1357_ = l_Lean_stringToMessageData(v___x_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(lean_object* v_val_1358_, lean_object* v___x_1359_, lean_object* v_x_1360_, lean_object* v_mvarId_1361_, lean_object* v_declName_1362_, uint8_t v___x_1363_, lean_object* v_____r_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v_majorPos_1395_; lean_object* v_arity_1396_; lean_object* v_insterestingCtors_1397_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___x_1417_; uint8_t v___x_1418_; 
v_majorPos_1395_ = lean_ctor_get(v_val_1358_, 1);
v_arity_1396_ = lean_ctor_get(v_val_1358_, 2);
v_insterestingCtors_1397_ = lean_ctor_get(v_val_1358_, 3);
v___x_1417_ = lean_array_get_size(v_x_1360_);
v___x_1418_ = lean_nat_dec_lt(v___x_1417_, v_arity_1396_);
if (v___x_1418_ == 0)
{
v___y_1399_ = v___y_1365_;
v___y_1400_ = v___y_1366_;
v___y_1401_ = v___y_1367_;
v___y_1402_ = v___y_1368_;
goto v___jp_1398_;
}
else
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
lean_dec(v_declName_1362_);
lean_dec(v_mvarId_1361_);
lean_dec_ref(v_val_1358_);
v___x_1419_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1);
v___x_1420_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1419_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___x_1420_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1420_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
v___jp_1370_:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; uint8_t v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1377_ = lean_array_get_borrowed(v___x_1359_, v_x_1360_, v___y_1371_);
lean_dec(v___y_1371_);
v___x_1378_ = l_Lean_Expr_fvarId_x21(v___x_1377_);
v___x_1379_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__0));
v___x_1380_ = 0;
v___x_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1381_, 0, v___y_1372_);
v___x_1382_ = l_Lean_MVarId_cases(v_mvarId_1361_, v___x_1378_, v___x_1379_, v___x_1380_, v___x_1381_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; size_t v_sz_1384_; size_t v___x_1385_; lean_object* v___x_1386_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_a_1383_);
lean_dec_ref_known(v___x_1382_, 1);
v_sz_1384_ = lean_array_size(v_a_1383_);
v___x_1385_ = ((size_t)0ULL);
v___x_1386_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(v_declName_1362_, v_val_1358_, v___x_1363_, v_sz_1384_, v___x_1385_, v_a_1383_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_);
return v___x_1386_;
}
else
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
lean_dec(v_declName_1362_);
lean_dec_ref(v_val_1358_);
v_a_1387_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1382_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1382_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
v___jp_1398_:
{
lean_object* v___x_1403_; uint8_t v___x_1404_; 
v___x_1403_ = lean_array_get_borrowed(v___x_1359_, v_x_1360_, v_majorPos_1395_);
v___x_1404_ = l_Lean_Expr_isFVar(v___x_1403_);
if (v___x_1404_ == 0)
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1416_; 
lean_dec(v_declName_1362_);
lean_dec(v_mvarId_1361_);
lean_dec_ref(v_val_1358_);
v___x_1405_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2);
lean_inc(v___x_1403_);
v___x_1406_ = l_Lean_indentExpr(v___x_1403_);
v___x_1407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1405_);
lean_ctor_set(v___x_1407_, 1, v___x_1406_);
v___x_1408_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1407_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1411_ = v___x_1408_;
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1408_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
if (v_isShared_1412_ == 0)
{
v___x_1414_ = v___x_1411_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_a_1409_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
else
{
lean_inc_ref(v_insterestingCtors_1397_);
lean_inc(v_majorPos_1395_);
v___y_1371_ = v_majorPos_1395_;
v___y_1372_ = v_insterestingCtors_1397_;
v___y_1373_ = v___y_1399_;
v___y_1374_ = v___y_1400_;
v___y_1375_ = v___y_1401_;
v___y_1376_ = v___y_1402_;
goto v___jp_1370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___boxed(lean_object* v_val_1429_, lean_object* v___x_1430_, lean_object* v_x_1431_, lean_object* v_mvarId_1432_, lean_object* v_declName_1433_, lean_object* v___x_1434_, lean_object* v_____r_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
uint8_t v___x_31588__boxed_1441_; lean_object* v_res_1442_; 
v___x_31588__boxed_1441_ = lean_unbox(v___x_1434_);
v_res_1442_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(v_val_1429_, v___x_1430_, v_x_1431_, v_mvarId_1432_, v_declName_1433_, v___x_31588__boxed_1441_, v_____r_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec_ref(v_x_1431_);
lean_dec_ref(v___x_1430_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(lean_object* v_cls_1445_, lean_object* v_msg_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v_ref_1452_; lean_object* v___x_1453_; lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1498_; 
v_ref_1452_ = lean_ctor_get(v___y_1449_, 4);
v___x_1453_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msg_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1456_ = v___x_1453_;
v_isShared_1457_ = v_isSharedCheck_1498_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1453_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1498_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1458_; lean_object* v_traceState_1459_; lean_object* v_env_1460_; lean_object* v_nextMacroScope_1461_; lean_object* v_ngen_1462_; lean_object* v_auxDeclNGen_1463_; lean_object* v_cache_1464_; lean_object* v_messages_1465_; lean_object* v_infoState_1466_; lean_object* v_snapshotTasks_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1497_; 
v___x_1458_ = lean_st_ref_take(v___y_1450_);
v_traceState_1459_ = lean_ctor_get(v___x_1458_, 4);
v_env_1460_ = lean_ctor_get(v___x_1458_, 0);
v_nextMacroScope_1461_ = lean_ctor_get(v___x_1458_, 1);
v_ngen_1462_ = lean_ctor_get(v___x_1458_, 2);
v_auxDeclNGen_1463_ = lean_ctor_get(v___x_1458_, 3);
v_cache_1464_ = lean_ctor_get(v___x_1458_, 5);
v_messages_1465_ = lean_ctor_get(v___x_1458_, 6);
v_infoState_1466_ = lean_ctor_get(v___x_1458_, 7);
v_snapshotTasks_1467_ = lean_ctor_get(v___x_1458_, 8);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1469_ = v___x_1458_;
v_isShared_1470_ = v_isSharedCheck_1497_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_snapshotTasks_1467_);
lean_inc(v_infoState_1466_);
lean_inc(v_messages_1465_);
lean_inc(v_cache_1464_);
lean_inc(v_traceState_1459_);
lean_inc(v_auxDeclNGen_1463_);
lean_inc(v_ngen_1462_);
lean_inc(v_nextMacroScope_1461_);
lean_inc(v_env_1460_);
lean_dec(v___x_1458_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1497_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
uint64_t v_tid_1471_; lean_object* v_traces_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1496_; 
v_tid_1471_ = lean_ctor_get_uint64(v_traceState_1459_, sizeof(void*)*1);
v_traces_1472_ = lean_ctor_get(v_traceState_1459_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v_traceState_1459_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1474_ = v_traceState_1459_;
v_isShared_1475_ = v_isSharedCheck_1496_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_traces_1472_);
lean_dec(v_traceState_1459_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1496_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1476_; double v___x_1477_; uint8_t v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1486_; 
v___x_1476_ = lean_box(0);
v___x_1477_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0);
v___x_1478_ = 0;
v___x_1479_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__6));
v___x_1480_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1480_, 0, v_cls_1445_);
lean_ctor_set(v___x_1480_, 1, v___x_1476_);
lean_ctor_set(v___x_1480_, 2, v___x_1479_);
lean_ctor_set_float(v___x_1480_, sizeof(void*)*3, v___x_1477_);
lean_ctor_set_float(v___x_1480_, sizeof(void*)*3 + 8, v___x_1477_);
lean_ctor_set_uint8(v___x_1480_, sizeof(void*)*3 + 16, v___x_1478_);
v___x_1481_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___closed__0));
v___x_1482_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1480_);
lean_ctor_set(v___x_1482_, 1, v_a_1454_);
lean_ctor_set(v___x_1482_, 2, v___x_1481_);
lean_inc(v_ref_1452_);
v___x_1483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1483_, 0, v_ref_1452_);
lean_ctor_set(v___x_1483_, 1, v___x_1482_);
v___x_1484_ = l_Lean_PersistentArray_push___redArg(v_traces_1472_, v___x_1483_);
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 0, v___x_1484_);
v___x_1486_ = v___x_1474_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___x_1484_);
lean_ctor_set_uint64(v_reuseFailAlloc_1495_, sizeof(void*)*1, v_tid_1471_);
v___x_1486_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
lean_object* v___x_1488_; 
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 4, v___x_1486_);
v___x_1488_ = v___x_1469_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_env_1460_);
lean_ctor_set(v_reuseFailAlloc_1494_, 1, v_nextMacroScope_1461_);
lean_ctor_set(v_reuseFailAlloc_1494_, 2, v_ngen_1462_);
lean_ctor_set(v_reuseFailAlloc_1494_, 3, v_auxDeclNGen_1463_);
lean_ctor_set(v_reuseFailAlloc_1494_, 4, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1494_, 5, v_cache_1464_);
lean_ctor_set(v_reuseFailAlloc_1494_, 6, v_messages_1465_);
lean_ctor_set(v_reuseFailAlloc_1494_, 7, v_infoState_1466_);
lean_ctor_set(v_reuseFailAlloc_1494_, 8, v_snapshotTasks_1467_);
v___x_1488_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1492_; 
v___x_1489_ = lean_st_ref_put(v___y_1450_, v___x_1488_);
v___x_1490_ = lean_box(0);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 0, v___x_1490_);
v___x_1492_ = v___x_1456_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1490_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___boxed(lean_object* v_cls_1499_, lean_object* v_msg_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v_cls_1499_, v_msg_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5(lean_object* v_declName_1507_, lean_object* v_val_1508_, uint8_t v___x_1509_, uint8_t v___x_1510_, size_t v_sz_1511_, size_t v_i_1512_, lean_object* v_bs_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
uint8_t v___x_1519_; 
v___x_1519_ = lean_usize_dec_lt(v_i_1512_, v_sz_1511_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1520_; 
lean_dec_ref(v_val_1508_);
lean_dec(v_declName_1507_);
v___x_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1520_, 0, v_bs_1513_);
return v___x_1520_;
}
else
{
lean_object* v_v_1521_; lean_object* v_toInductionSubgoal_1522_; lean_object* v_ctorName_1523_; lean_object* v_mvarId_1524_; lean_object* v_fields_1525_; lean_object* v___f_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v_bs_x27_1529_; uint8_t v___y_1531_; 
v_v_1521_ = lean_array_uget_borrowed(v_bs_1513_, v_i_1512_);
v_toInductionSubgoal_1522_ = lean_ctor_get(v_v_1521_, 0);
v_ctorName_1523_ = lean_ctor_get(v_v_1521_, 1);
lean_inc(v_ctorName_1523_);
v_mvarId_1524_ = lean_ctor_get(v_toInductionSubgoal_1522_, 0);
lean_inc(v_mvarId_1524_);
v_fields_1525_ = lean_ctor_get(v_toInductionSubgoal_1522_, 1);
lean_inc_ref(v_fields_1525_);
v___f_1526_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0));
v___x_1527_ = l_Lean_instInhabitedExpr;
v___x_1528_ = lean_unsigned_to_nat(0u);
v_bs_x27_1529_ = lean_array_uset(v_bs_1513_, v_i_1512_, v___x_1528_);
if (lean_obj_tag(v_ctorName_1523_) == 0)
{
v___y_1531_ = v___x_1510_;
goto v___jp_1530_;
}
else
{
lean_dec_ref_known(v_ctorName_1523_, 1);
v___y_1531_ = v___x_1509_;
goto v___jp_1530_;
}
v___jp_1530_:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___y_1534_; lean_object* v___x_1535_; 
v___x_1532_ = lean_box(v___y_1531_);
v___x_1533_ = lean_box(v___x_1509_);
lean_inc_ref(v_val_1508_);
lean_inc(v_declName_1507_);
lean_inc(v_mvarId_1524_);
v___y_1534_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed), 13, 8);
lean_closure_set(v___y_1534_, 0, v___x_1532_);
lean_closure_set(v___y_1534_, 1, v_mvarId_1524_);
lean_closure_set(v___y_1534_, 2, v___f_1526_);
lean_closure_set(v___y_1534_, 3, v_declName_1507_);
lean_closure_set(v___y_1534_, 4, v_val_1508_);
lean_closure_set(v___y_1534_, 5, v___x_1527_);
lean_closure_set(v___y_1534_, 6, v_fields_1525_);
lean_closure_set(v___y_1534_, 7, v___x_1533_);
v___x_1535_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1524_, v___y_1534_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; size_t v___x_1537_; size_t v___x_1538_; lean_object* v___x_1539_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1536_);
lean_dec_ref_known(v___x_1535_, 1);
v___x_1537_ = ((size_t)1ULL);
v___x_1538_ = lean_usize_add(v_i_1512_, v___x_1537_);
v___x_1539_ = lean_array_uset(v_bs_x27_1529_, v_i_1512_, v_a_1536_);
v_i_1512_ = v___x_1538_;
v_bs_1513_ = v___x_1539_;
goto _start;
}
else
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
lean_dec_ref(v_bs_x27_1529_);
lean_dec_ref(v_val_1508_);
lean_dec(v_declName_1507_);
v_a_1541_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1535_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1535_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5___boxed(lean_object* v_declName_1549_, lean_object* v_val_1550_, lean_object* v___x_1551_, lean_object* v___x_1552_, lean_object* v_sz_1553_, lean_object* v_i_1554_, lean_object* v_bs_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
uint8_t v___x_31832__boxed_1561_; uint8_t v___x_31833__boxed_1562_; size_t v_sz_boxed_1563_; size_t v_i_boxed_1564_; lean_object* v_res_1565_; 
v___x_31832__boxed_1561_ = lean_unbox(v___x_1551_);
v___x_31833__boxed_1562_ = lean_unbox(v___x_1552_);
v_sz_boxed_1563_ = lean_unbox_usize(v_sz_1553_);
lean_dec(v_sz_1553_);
v_i_boxed_1564_ = lean_unbox_usize(v_i_1554_);
lean_dec(v_i_1554_);
v_res_1565_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5(v_declName_1549_, v_val_1550_, v___x_31832__boxed_1561_, v___x_31833__boxed_1562_, v_sz_boxed_1563_, v_i_boxed_1564_, v_bs_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(lean_object* v_val_1566_, lean_object* v___x_1567_, lean_object* v_x_1568_, lean_object* v_mvarId_1569_, uint8_t v___x_1570_, lean_object* v_declName_1571_, uint8_t v_hasTrace_1572_, lean_object* v_____r_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v_majorPos_1603_; lean_object* v_arity_1604_; lean_object* v_insterestingCtors_1605_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___x_1625_; uint8_t v___x_1626_; 
v_majorPos_1603_ = lean_ctor_get(v_val_1566_, 1);
v_arity_1604_ = lean_ctor_get(v_val_1566_, 2);
v_insterestingCtors_1605_ = lean_ctor_get(v_val_1566_, 3);
v___x_1625_ = lean_array_get_size(v_x_1568_);
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
lean_dec(v_declName_1571_);
lean_dec(v_mvarId_1569_);
lean_dec_ref(v_val_1566_);
v___x_1627_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1);
v___x_1628_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1627_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
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
v___x_1586_ = lean_array_get_borrowed(v___x_1567_, v_x_1568_, v___y_1581_);
lean_dec(v___y_1581_);
v___x_1587_ = l_Lean_Expr_fvarId_x21(v___x_1586_);
v___x_1588_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__0));
v___x_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1589_, 0, v___y_1580_);
v___x_1590_ = l_Lean_MVarId_cases(v_mvarId_1569_, v___x_1587_, v___x_1588_, v___x_1570_, v___x_1589_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; size_t v_sz_1592_; size_t v___x_1593_; lean_object* v___x_1594_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1591_);
lean_dec_ref_known(v___x_1590_, 1);
v_sz_1592_ = lean_array_size(v_a_1591_);
v___x_1593_ = ((size_t)0ULL);
v___x_1594_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5(v_declName_1571_, v_val_1566_, v___x_1570_, v_hasTrace_1572_, v_sz_1592_, v___x_1593_, v_a_1591_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
return v___x_1594_;
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
lean_dec(v_declName_1571_);
lean_dec_ref(v_val_1566_);
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
v___x_1611_ = lean_array_get_borrowed(v___x_1567_, v_x_1568_, v_majorPos_1603_);
v___x_1612_ = l_Lean_Expr_isFVar(v___x_1611_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
lean_dec(v_declName_1571_);
lean_dec(v_mvarId_1569_);
lean_dec_ref(v_val_1566_);
v___x_1613_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2);
lean_inc(v___x_1611_);
v___x_1614_ = l_Lean_indentExpr(v___x_1611_);
v___x_1615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1613_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
v___x_1616_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1615_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
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
lean_inc(v_majorPos_1603_);
lean_inc_ref(v_insterestingCtors_1605_);
v___y_1580_ = v_insterestingCtors_1605_;
v___y_1581_ = v_majorPos_1603_;
v___y_1582_ = v___y_1607_;
v___y_1583_ = v___y_1608_;
v___y_1584_ = v___y_1609_;
v___y_1585_ = v___y_1610_;
goto v___jp_1579_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___boxed(lean_object* v_val_1637_, lean_object* v___x_1638_, lean_object* v_x_1639_, lean_object* v_mvarId_1640_, lean_object* v___x_1641_, lean_object* v_declName_1642_, lean_object* v_hasTrace_1643_, lean_object* v_____r_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
uint8_t v___x_31917__boxed_1650_; uint8_t v_hasTrace_boxed_1651_; lean_object* v_res_1652_; 
v___x_31917__boxed_1650_ = lean_unbox(v___x_1641_);
v_hasTrace_boxed_1651_ = lean_unbox(v_hasTrace_1643_);
v_res_1652_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(v_val_1637_, v___x_1638_, v_x_1639_, v_mvarId_1640_, v___x_31917__boxed_1650_, v_declName_1642_, v_hasTrace_boxed_1651_, v_____r_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec_ref(v_x_1639_);
lean_dec_ref(v___x_1638_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(lean_object* v___x_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v_options_1659_; uint8_t v_hasTrace_1660_; 
v_options_1659_ = lean_ctor_get(v___y_1656_, 1);
v_hasTrace_1660_ = lean_ctor_get_uint8(v_options_1659_, sizeof(void*)*1);
if (v_hasTrace_1660_ == 0)
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
lean_dec(v___x_1653_);
v___x_1661_ = lean_box(v_hasTrace_1660_);
v___x_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1661_);
return v___x_1662_;
}
else
{
lean_object* v_toCold_1663_; lean_object* v_inheritedTraceOptions_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; uint8_t v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v_toCold_1663_ = lean_ctor_get(v___y_1656_, 0);
v_inheritedTraceOptions_1664_ = lean_ctor_get(v_toCold_1663_, 4);
v___x_1665_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__8));
v___x_1666_ = l_Lean_Name_append(v___x_1665_, v___x_1653_);
v___x_1667_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1664_, v_options_1659_, v___x_1666_);
lean_dec(v___x_1666_);
v___x_1668_ = lean_box(v___x_1667_);
v___x_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1668_);
return v___x_1669_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0___boxed(lean_object* v___x_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v___x_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
return v_res_1676_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1(void){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__0));
v___x_1679_ = l_Lean_stringToMessageData(v___x_1678_);
return v___x_1679_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3(void){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1681_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__2));
v___x_1682_ = l_Lean_stringToMessageData(v___x_1681_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6(lean_object* v_mvarId_1683_, lean_object* v_x_1684_, lean_object* v_x_1685_, lean_object* v_x_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
if (lean_obj_tag(v_x_1684_) == 5)
{
lean_object* v_fn_1692_; lean_object* v_arg_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v_fn_1692_ = lean_ctor_get(v_x_1684_, 0);
lean_inc_ref(v_fn_1692_);
v_arg_1693_ = lean_ctor_get(v_x_1684_, 1);
lean_inc_ref(v_arg_1693_);
lean_dec_ref_known(v_x_1684_, 2);
v___x_1694_ = lean_array_set(v_x_1685_, v_x_1686_, v_arg_1693_);
v___x_1695_ = lean_unsigned_to_nat(1u);
v___x_1696_ = lean_nat_sub(v_x_1686_, v___x_1695_);
lean_dec(v_x_1686_);
v_x_1684_ = v_fn_1692_;
v_x_1685_ = v___x_1694_;
v_x_1686_ = v___x_1696_;
goto _start;
}
else
{
lean_dec(v_x_1686_);
if (lean_obj_tag(v_x_1684_) == 4)
{
lean_object* v_declName_1698_; lean_object* v___x_1699_; 
v_declName_1698_ = lean_ctor_get(v_x_1684_, 0);
lean_inc_n(v_declName_1698_, 2);
lean_dec_ref_known(v_x_1684_, 2);
v___x_1699_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_declName_1698_, v___y_1690_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
lean_inc(v_a_1700_);
lean_dec_ref_known(v___x_1699_, 1);
if (lean_obj_tag(v_a_1700_) == 1)
{
lean_object* v_options_1701_; lean_object* v_val_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_2013_; 
v_options_1701_ = lean_ctor_get(v___y_1689_, 1);
v_val_1702_ = lean_ctor_get(v_a_1700_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v_a_1700_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_1704_ = v_a_1700_;
v_isShared_1705_ = v_isSharedCheck_2013_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_val_1702_);
lean_dec(v_a_1700_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_2013_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v_toCold_1706_; uint8_t v_hasTrace_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___y_1711_; lean_object* v___y_1712_; uint8_t v___y_1713_; lean_object* v___y_1746_; lean_object* v_a_1747_; lean_object* v___y_1751_; lean_object* v___y_1754_; lean_object* v___y_1755_; uint8_t v___y_1756_; lean_object* v___y_1789_; lean_object* v_a_1790_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; 
v_toCold_1706_ = lean_ctor_get(v___y_1689_, 0);
v_hasTrace_1707_ = lean_ctor_get_uint8(v_options_1701_, sizeof(void*)*1);
v___x_1708_ = l_Lean_instInhabitedExpr;
v___x_1709_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5));
if (v_hasTrace_1707_ == 0)
{
lean_object* v_majorPos_1820_; lean_object* v_arity_1821_; lean_object* v_insterestingCtors_1822_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___x_1842_; uint8_t v___x_1843_; 
v_majorPos_1820_ = lean_ctor_get(v_val_1702_, 1);
v_arity_1821_ = lean_ctor_get(v_val_1702_, 2);
v_insterestingCtors_1822_ = lean_ctor_get(v_val_1702_, 3);
v___x_1842_ = lean_array_get_size(v_x_1685_);
v___x_1843_ = lean_nat_dec_lt(v___x_1842_, v_arity_1821_);
if (v___x_1843_ == 0)
{
v___y_1824_ = v___y_1687_;
v___y_1825_ = v___y_1688_;
v___y_1826_ = v___y_1689_;
v___y_1827_ = v___y_1690_;
goto v___jp_1823_;
}
else
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
lean_del_object(v___x_1704_);
lean_dec(v_val_1702_);
lean_dec(v_declName_1698_);
lean_dec_ref(v_x_1685_);
lean_dec(v_mvarId_1683_);
v___x_1844_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1);
v___x_1845_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1844_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1848_ = v___x_1845_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1845_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
lean_inc(v_a_1846_);
if (v_isShared_1849_ == 0)
{
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_a_1846_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
v___y_1789_ = v___x_1851_;
v_a_1790_ = v_a_1846_;
goto v___jp_1788_;
}
}
}
v___jp_1823_:
{
lean_object* v___x_1828_; uint8_t v___x_1829_; 
v___x_1828_ = lean_array_get_borrowed(v___x_1708_, v_x_1685_, v_majorPos_1820_);
v___x_1829_ = l_Lean_Expr_isFVar(v___x_1828_);
if (v___x_1829_ == 0)
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1841_; 
lean_inc(v___x_1828_);
lean_del_object(v___x_1704_);
lean_dec(v_val_1702_);
lean_dec(v_declName_1698_);
lean_dec_ref(v_x_1685_);
lean_dec(v_mvarId_1683_);
v___x_1830_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2);
v___x_1831_ = l_Lean_indentExpr(v___x_1828_);
v___x_1832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1830_);
lean_ctor_set(v___x_1832_, 1, v___x_1831_);
v___x_1833_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1832_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1836_ = v___x_1833_;
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1833_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1839_; 
lean_inc(v_a_1834_);
if (v_isShared_1837_ == 0)
{
v___x_1839_ = v___x_1836_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1834_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
v___y_1789_ = v___x_1839_;
v_a_1790_ = v_a_1834_;
goto v___jp_1788_;
}
}
}
else
{
lean_inc(v_majorPos_1820_);
lean_inc_ref(v_insterestingCtors_1822_);
v___y_1794_ = v_insterestingCtors_1822_;
v___y_1795_ = v_majorPos_1820_;
v___y_1796_ = v___y_1824_;
v___y_1797_ = v___y_1825_;
v___y_1798_ = v___y_1826_;
v___y_1799_ = v___y_1827_;
goto v___jp_1793_;
}
}
}
else
{
lean_object* v_inheritedTraceOptions_1854_; lean_object* v___f_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; uint8_t v___x_1858_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v_a_1862_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v_a_1877_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; uint8_t v___y_1883_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v_a_1896_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v_a_1915_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v_a_1927_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; uint8_t v___y_1933_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v_a_1946_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; 
lean_del_object(v___x_1704_);
v_inheritedTraceOptions_1854_ = lean_ctor_get(v_toCold_1706_, 4);
v___f_1855_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1));
v___x_1856_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__6));
v___x_1857_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9);
v___x_1858_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1854_, v_options_1701_, v___x_1857_);
if (v___x_1858_ == 0)
{
lean_object* v___x_1995_; uint8_t v___x_1996_; 
v___x_1995_ = l_Lean_trace_profiler;
v___x_1996_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_options_1701_, v___x_1995_);
if (v___x_1996_ == 0)
{
if (v___x_1858_ == 0)
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = lean_box(0);
v___x_1998_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(v_val_1702_, v___x_1708_, v_x_1685_, v_mvarId_1683_, v___x_1996_, v_declName_1698_, v_hasTrace_1707_, v___x_1997_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
lean_dec_ref(v_x_1685_);
v___y_1751_ = v___x_1998_;
goto v___jp_1750_;
}
else
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_1999_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3);
lean_inc(v_mvarId_1683_);
v___x_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2000_, 0, v_mvarId_1683_);
v___x_2001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_1999_);
lean_ctor_set(v___x_2001_, 1, v___x_2000_);
v___x_2002_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1709_, v___x_2001_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; lean_object* v___x_2004_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2003_);
lean_dec_ref_known(v___x_2002_, 1);
v___x_2004_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(v_val_1702_, v___x_1708_, v_x_1685_, v_mvarId_1683_, v___x_1996_, v_declName_1698_, v_hasTrace_1707_, v_a_2003_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
lean_dec_ref(v_x_1685_);
v___y_1751_ = v___x_2004_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2012_; 
lean_dec(v_val_1702_);
lean_dec(v_declName_1698_);
lean_dec_ref(v_x_1685_);
lean_dec(v_mvarId_1683_);
v_a_2005_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2007_ = v___x_2002_;
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_2002_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
lean_inc(v_a_2005_);
if (v_isShared_2008_ == 0)
{
v___x_2010_ = v___x_2007_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2005_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
v___y_1746_ = v___x_2010_;
v_a_1747_ = v_a_2005_;
goto v___jp_1745_;
}
}
}
}
}
else
{
goto v___jp_1962_;
}
}
else
{
goto v___jp_1962_;
}
v___jp_1859_:
{
lean_object* v___x_1863_; double v___x_1864_; double v___x_1865_; double v___x_1866_; double v___x_1867_; double v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1863_ = lean_io_mono_nanos_now();
v___x_1864_ = lean_float_of_nat(v___y_1861_);
v___x_1865_ = lean_float_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10);
v___x_1866_ = lean_float_div(v___x_1864_, v___x_1865_);
v___x_1867_ = lean_float_of_nat(v___x_1863_);
v___x_1868_ = lean_float_div(v___x_1867_, v___x_1865_);
v___x_1869_ = lean_box_float(v___x_1866_);
v___x_1870_ = lean_box_float(v___x_1868_);
v___x_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1869_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
v___x_1872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1872_, 0, v_a_1862_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
v___x_1873_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_1709_, v_hasTrace_1707_, v___x_1856_, v_options_1701_, v___x_1858_, v___y_1860_, v___f_1855_, v___x_1872_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
return v___x_1873_;
}
v___jp_1874_:
{
lean_object* v___x_1878_; 
v___x_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1878_, 0, v_a_1877_);
v___y_1860_ = v___y_1876_;
v___y_1861_ = v___y_1875_;
v_a_1862_ = v___x_1878_;
goto v___jp_1859_;
}
v___jp_1879_:
{
if (v___y_1883_ == 0)
{
lean_object* v___x_1884_; lean_object* v_a_1885_; uint8_t v___x_1886_; 
v___x_1884_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v___x_1709_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_a_1885_);
lean_dec_ref(v___x_1884_);
v___x_1886_ = lean_unbox(v_a_1885_);
lean_dec(v_a_1885_);
if (v___x_1886_ == 0)
{
v___y_1875_ = v___y_1881_;
v___y_1876_ = v___y_1880_;
v_a_1877_ = v___y_1882_;
goto v___jp_1874_;
}
else
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1887_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1);
lean_inc_ref(v___y_1882_);
v___x_1888_ = l_Lean_Exception_toMessageData(v___y_1882_);
v___x_1889_ = l_Lean_indentD(v___x_1888_);
v___x_1890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1887_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
v___x_1891_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1709_, v___x_1890_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_dec_ref_known(v___x_1891_, 1);
v___y_1875_ = v___y_1881_;
v___y_1876_ = v___y_1880_;
v_a_1877_ = v___y_1882_;
goto v___jp_1874_;
}
else
{
lean_object* v_a_1892_; 
lean_dec_ref(v___y_1882_);
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_a_1892_);
lean_dec_ref_known(v___x_1891_, 1);
v___y_1875_ = v___y_1881_;
v___y_1876_ = v___y_1880_;
v_a_1877_ = v_a_1892_;
goto v___jp_1874_;
}
}
}
else
{
v___y_1875_ = v___y_1881_;
v___y_1876_ = v___y_1880_;
v_a_1877_ = v___y_1882_;
goto v___jp_1874_;
}
}
v___jp_1893_:
{
uint8_t v___x_1897_; 
v___x_1897_ = l_Lean_Exception_isInterrupt(v_a_1896_);
if (v___x_1897_ == 0)
{
uint8_t v___x_1898_; 
lean_inc_ref(v_a_1896_);
v___x_1898_ = l_Lean_Exception_isRuntime(v_a_1896_);
v___y_1880_ = v___y_1895_;
v___y_1881_ = v___y_1894_;
v___y_1882_ = v_a_1896_;
v___y_1883_ = v___x_1898_;
goto v___jp_1879_;
}
else
{
v___y_1880_ = v___y_1895_;
v___y_1881_ = v___y_1894_;
v___y_1882_ = v_a_1896_;
v___y_1883_ = v___x_1897_;
goto v___jp_1879_;
}
}
v___jp_1899_:
{
if (lean_obj_tag(v___y_1902_) == 0)
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1910_; 
v_a_1903_ = lean_ctor_get(v___y_1902_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___y_1902_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1905_ = v___y_1902_;
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___y_1902_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
lean_ctor_set_tag(v___x_1905_, 1);
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
v___y_1860_ = v___y_1901_;
v___y_1861_ = v___y_1900_;
v_a_1862_ = v___x_1908_;
goto v___jp_1859_;
}
}
}
else
{
lean_object* v_a_1911_; 
v_a_1911_ = lean_ctor_get(v___y_1902_, 0);
lean_inc(v_a_1911_);
lean_dec_ref_known(v___y_1902_, 1);
v___y_1894_ = v___y_1900_;
v___y_1895_ = v___y_1901_;
v_a_1896_ = v_a_1911_;
goto v___jp_1893_;
}
}
v___jp_1912_:
{
lean_object* v___x_1916_; double v___x_1917_; double v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1916_ = lean_io_get_num_heartbeats();
v___x_1917_ = lean_float_of_nat(v___y_1914_);
v___x_1918_ = lean_float_of_nat(v___x_1916_);
v___x_1919_ = lean_box_float(v___x_1917_);
v___x_1920_ = lean_box_float(v___x_1918_);
v___x_1921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1919_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
v___x_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1922_, 0, v_a_1915_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_1709_, v_hasTrace_1707_, v___x_1856_, v_options_1701_, v___x_1858_, v___y_1913_, v___f_1855_, v___x_1922_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
return v___x_1923_;
}
v___jp_1924_:
{
lean_object* v___x_1928_; 
v___x_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1928_, 0, v_a_1927_);
v___y_1913_ = v___y_1925_;
v___y_1914_ = v___y_1926_;
v_a_1915_ = v___x_1928_;
goto v___jp_1912_;
}
v___jp_1929_:
{
if (v___y_1933_ == 0)
{
lean_object* v___x_1934_; lean_object* v_a_1935_; uint8_t v___x_1936_; 
v___x_1934_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v___x_1709_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1935_);
lean_dec_ref(v___x_1934_);
v___x_1936_ = lean_unbox(v_a_1935_);
lean_dec(v_a_1935_);
if (v___x_1936_ == 0)
{
v___y_1925_ = v___y_1931_;
v___y_1926_ = v___y_1932_;
v_a_1927_ = v___y_1930_;
goto v___jp_1924_;
}
else
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1937_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1);
lean_inc_ref(v___y_1930_);
v___x_1938_ = l_Lean_Exception_toMessageData(v___y_1930_);
v___x_1939_ = l_Lean_indentD(v___x_1938_);
v___x_1940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1937_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
v___x_1941_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1709_, v___x_1940_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_dec_ref_known(v___x_1941_, 1);
v___y_1925_ = v___y_1931_;
v___y_1926_ = v___y_1932_;
v_a_1927_ = v___y_1930_;
goto v___jp_1924_;
}
else
{
lean_object* v_a_1942_; 
lean_dec_ref(v___y_1930_);
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_a_1942_);
lean_dec_ref_known(v___x_1941_, 1);
v___y_1925_ = v___y_1931_;
v___y_1926_ = v___y_1932_;
v_a_1927_ = v_a_1942_;
goto v___jp_1924_;
}
}
}
else
{
v___y_1925_ = v___y_1931_;
v___y_1926_ = v___y_1932_;
v_a_1927_ = v___y_1930_;
goto v___jp_1924_;
}
}
v___jp_1943_:
{
uint8_t v___x_1947_; 
v___x_1947_ = l_Lean_Exception_isInterrupt(v_a_1946_);
if (v___x_1947_ == 0)
{
uint8_t v___x_1948_; 
lean_inc_ref(v_a_1946_);
v___x_1948_ = l_Lean_Exception_isRuntime(v_a_1946_);
v___y_1930_ = v_a_1946_;
v___y_1931_ = v___y_1944_;
v___y_1932_ = v___y_1945_;
v___y_1933_ = v___x_1948_;
goto v___jp_1929_;
}
else
{
v___y_1930_ = v_a_1946_;
v___y_1931_ = v___y_1944_;
v___y_1932_ = v___y_1945_;
v___y_1933_ = v___x_1947_;
goto v___jp_1929_;
}
}
v___jp_1949_:
{
if (lean_obj_tag(v___y_1952_) == 0)
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
v_a_1953_ = lean_ctor_get(v___y_1952_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___y_1952_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v___y_1952_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___y_1952_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
lean_ctor_set_tag(v___x_1955_, 1);
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1953_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
v___y_1913_ = v___y_1950_;
v___y_1914_ = v___y_1951_;
v_a_1915_ = v___x_1958_;
goto v___jp_1912_;
}
}
}
else
{
lean_object* v_a_1961_; 
v_a_1961_ = lean_ctor_get(v___y_1952_, 0);
lean_inc(v_a_1961_);
lean_dec_ref_known(v___y_1952_, 1);
v___y_1944_ = v___y_1950_;
v___y_1945_ = v___y_1951_;
v_a_1946_ = v_a_1961_;
goto v___jp_1943_;
}
}
v___jp_1962_:
{
lean_object* v___x_1963_; lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1994_; 
v___x_1963_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___y_1690_);
v_a_1964_ = lean_ctor_get(v___x_1963_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1966_ = v___x_1963_;
v_isShared_1967_ = v_isSharedCheck_1994_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1963_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1994_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1968_; uint8_t v___x_1969_; 
v___x_1968_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1969_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_options_1701_, v___x_1968_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; 
v___x_1970_ = lean_io_mono_nanos_now();
if (v___x_1858_ == 0)
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
lean_del_object(v___x_1966_);
v___x_1971_ = lean_box(0);
v___x_1972_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(v_val_1702_, v___x_1708_, v_x_1685_, v_mvarId_1683_, v___x_1969_, v_declName_1698_, v_hasTrace_1707_, v___x_1971_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
lean_dec_ref(v_x_1685_);
v___y_1900_ = v___x_1970_;
v___y_1901_ = v_a_1964_;
v___y_1902_ = v___x_1972_;
goto v___jp_1899_;
}
else
{
lean_object* v___x_1973_; lean_object* v___x_1975_; 
v___x_1973_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3);
lean_inc(v_mvarId_1683_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set_tag(v___x_1966_, 1);
lean_ctor_set(v___x_1966_, 0, v_mvarId_1683_);
v___x_1975_ = v___x_1966_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_mvarId_1683_);
v___x_1975_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1973_);
lean_ctor_set(v___x_1976_, 1, v___x_1975_);
v___x_1977_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1709_, v___x_1976_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v___x_1979_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_a_1978_);
lean_dec_ref_known(v___x_1977_, 1);
v___x_1979_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(v_val_1702_, v___x_1708_, v_x_1685_, v_mvarId_1683_, v___x_1969_, v_declName_1698_, v_hasTrace_1707_, v_a_1978_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
lean_dec_ref(v_x_1685_);
v___y_1900_ = v___x_1970_;
v___y_1901_ = v_a_1964_;
v___y_1902_ = v___x_1979_;
goto v___jp_1899_;
}
else
{
lean_object* v_a_1980_; 
lean_dec(v_val_1702_);
lean_dec(v_declName_1698_);
lean_dec_ref(v_x_1685_);
lean_dec(v_mvarId_1683_);
v_a_1980_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_a_1980_);
lean_dec_ref_known(v___x_1977_, 1);
v___y_1894_ = v___x_1970_;
v___y_1895_ = v_a_1964_;
v_a_1896_ = v_a_1980_;
goto v___jp_1893_;
}
}
}
}
else
{
lean_object* v___x_1982_; 
v___x_1982_ = lean_io_get_num_heartbeats();
if (v___x_1858_ == 0)
{
lean_object* v___x_1983_; lean_object* v___x_1984_; 
lean_del_object(v___x_1966_);
v___x_1983_ = lean_box(0);
v___x_1984_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(v_val_1702_, v___x_1708_, v_x_1685_, v_mvarId_1683_, v_declName_1698_, v___x_1969_, v___x_1983_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
lean_dec_ref(v_x_1685_);
v___y_1950_ = v_a_1964_;
v___y_1951_ = v___x_1982_;
v___y_1952_ = v___x_1984_;
goto v___jp_1949_;
}
else
{
lean_object* v___x_1985_; lean_object* v___x_1987_; 
v___x_1985_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3);
lean_inc(v_mvarId_1683_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set_tag(v___x_1966_, 1);
lean_ctor_set(v___x_1966_, 0, v_mvarId_1683_);
v___x_1987_ = v___x_1966_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_mvarId_1683_);
v___x_1987_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1985_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
v___x_1989_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1709_, v___x_1988_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; lean_object* v___x_1991_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
lean_inc(v_a_1990_);
lean_dec_ref_known(v___x_1989_, 1);
v___x_1991_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(v_val_1702_, v___x_1708_, v_x_1685_, v_mvarId_1683_, v_declName_1698_, v___x_1969_, v_a_1990_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
lean_dec_ref(v_x_1685_);
v___y_1950_ = v_a_1964_;
v___y_1951_ = v___x_1982_;
v___y_1952_ = v___x_1991_;
goto v___jp_1949_;
}
else
{
lean_object* v_a_1992_; 
lean_dec(v_val_1702_);
lean_dec(v_declName_1698_);
lean_dec_ref(v_x_1685_);
lean_dec(v_mvarId_1683_);
v_a_1992_ = lean_ctor_get(v___x_1989_, 0);
lean_inc(v_a_1992_);
lean_dec_ref_known(v___x_1989_, 1);
v___y_1944_ = v_a_1964_;
v___y_1945_ = v___x_1982_;
v_a_1946_ = v_a_1992_;
goto v___jp_1943_;
}
}
}
}
}
}
}
v___jp_1710_:
{
if (v___y_1713_ == 0)
{
lean_object* v___x_1714_; lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1744_; 
lean_dec_ref(v___y_1712_);
v___x_1714_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v___x_1709_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1717_ = v___x_1714_;
v_isShared_1718_ = v_isSharedCheck_1744_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1714_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1744_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
uint8_t v___x_1719_; 
v___x_1719_ = lean_unbox(v_a_1715_);
lean_dec(v_a_1715_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1721_; 
if (v_isShared_1718_ == 0)
{
lean_ctor_set_tag(v___x_1717_, 1);
lean_ctor_set(v___x_1717_, 0, v___y_1711_);
v___x_1721_ = v___x_1717_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___y_1711_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
else
{
lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
lean_del_object(v___x_1717_);
v___x_1723_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1);
lean_inc_ref(v___y_1711_);
v___x_1724_ = l_Lean_Exception_toMessageData(v___y_1711_);
v___x_1725_ = l_Lean_indentD(v___x_1724_);
v___x_1726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1723_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
v___x_1727_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1709_, v___x_1726_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1734_ == 0)
{
lean_object* v_unused_1735_; 
v_unused_1735_ = lean_ctor_get(v___x_1727_, 0);
lean_dec(v_unused_1735_);
v___x_1729_ = v___x_1727_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_dec(v___x_1727_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
lean_ctor_set_tag(v___x_1729_, 1);
lean_ctor_set(v___x_1729_, 0, v___y_1711_);
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___y_1711_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
else
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
lean_dec_ref(v___y_1711_);
v_a_1736_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1727_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1727_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_1711_);
return v___y_1712_;
}
}
v___jp_1745_:
{
uint8_t v___x_1748_; 
v___x_1748_ = l_Lean_Exception_isInterrupt(v_a_1747_);
if (v___x_1748_ == 0)
{
uint8_t v___x_1749_; 
lean_inc_ref(v_a_1747_);
v___x_1749_ = l_Lean_Exception_isRuntime(v_a_1747_);
v___y_1711_ = v_a_1747_;
v___y_1712_ = v___y_1746_;
v___y_1713_ = v___x_1749_;
goto v___jp_1710_;
}
else
{
v___y_1711_ = v_a_1747_;
v___y_1712_ = v___y_1746_;
v___y_1713_ = v___x_1748_;
goto v___jp_1710_;
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
v___y_1746_ = v___y_1751_;
v_a_1747_ = v_a_1752_;
goto v___jp_1745_;
}
}
v___jp_1753_:
{
if (v___y_1756_ == 0)
{
lean_object* v___x_1757_; lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1787_; 
lean_dec_ref(v___y_1755_);
v___x_1757_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v___x_1709_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1760_ = v___x_1757_;
v_isShared_1761_ = v_isSharedCheck_1787_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1757_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1787_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
uint8_t v___x_1762_; 
v___x_1762_ = lean_unbox(v_a_1758_);
lean_dec(v_a_1758_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1764_; 
if (v_isShared_1761_ == 0)
{
lean_ctor_set_tag(v___x_1760_, 1);
lean_ctor_set(v___x_1760_, 0, v___y_1754_);
v___x_1764_ = v___x_1760_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___y_1754_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
else
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
lean_del_object(v___x_1760_);
v___x_1766_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1);
lean_inc_ref(v___y_1754_);
v___x_1767_ = l_Lean_Exception_toMessageData(v___y_1754_);
v___x_1768_ = l_Lean_indentD(v___x_1767_);
v___x_1769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1766_);
lean_ctor_set(v___x_1769_, 1, v___x_1768_);
v___x_1770_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1709_, v___x_1769_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1777_ == 0)
{
lean_object* v_unused_1778_; 
v_unused_1778_ = lean_ctor_get(v___x_1770_, 0);
lean_dec(v_unused_1778_);
v___x_1772_ = v___x_1770_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_dec(v___x_1770_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
lean_ctor_set_tag(v___x_1772_, 1);
lean_ctor_set(v___x_1772_, 0, v___y_1754_);
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___y_1754_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_dec_ref(v___y_1754_);
v_a_1779_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1770_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1770_);
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
}
}
}
else
{
lean_dec_ref(v___y_1754_);
return v___y_1755_;
}
}
v___jp_1788_:
{
uint8_t v___x_1791_; 
v___x_1791_ = l_Lean_Exception_isInterrupt(v_a_1790_);
if (v___x_1791_ == 0)
{
uint8_t v___x_1792_; 
lean_inc_ref(v_a_1790_);
v___x_1792_ = l_Lean_Exception_isRuntime(v_a_1790_);
v___y_1754_ = v_a_1790_;
v___y_1755_ = v___y_1789_;
v___y_1756_ = v___x_1792_;
goto v___jp_1753_;
}
else
{
v___y_1754_ = v_a_1790_;
v___y_1755_ = v___y_1789_;
v___y_1756_ = v___x_1791_;
goto v___jp_1753_;
}
}
v___jp_1793_:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1804_; 
v___x_1800_ = lean_array_get(v___x_1708_, v_x_1685_, v___y_1795_);
lean_dec(v___y_1795_);
lean_dec_ref(v_x_1685_);
v___x_1801_ = l_Lean_Expr_fvarId_x21(v___x_1800_);
lean_dec(v___x_1800_);
v___x_1802_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__0));
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 0, v___y_1794_);
v___x_1804_ = v___x_1704_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___y_1794_);
v___x_1804_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
lean_object* v___x_1805_; 
v___x_1805_ = l_Lean_MVarId_cases(v_mvarId_1683_, v___x_1801_, v___x_1802_, v_hasTrace_1707_, v___x_1804_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; size_t v_sz_1807_; size_t v___x_1808_; lean_object* v___x_1809_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_a_1806_);
lean_dec_ref_known(v___x_1805_, 1);
v_sz_1807_ = lean_array_size(v_a_1806_);
v___x_1808_ = ((size_t)0ULL);
v___x_1809_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(v_declName_1698_, v_val_1702_, v_hasTrace_1707_, v_sz_1807_, v___x_1808_, v_a_1806_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
if (lean_obj_tag(v___x_1809_) == 0)
{
return v___x_1809_;
}
else
{
lean_object* v_a_1810_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_a_1810_);
v___y_1789_ = v___x_1809_;
v_a_1790_ = v_a_1810_;
goto v___jp_1788_;
}
}
else
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_dec(v_val_1702_);
lean_dec(v_declName_1698_);
v_a_1811_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1805_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1805_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
lean_inc(v_a_1811_);
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
v___y_1789_ = v___x_1816_;
v_a_1790_ = v_a_1811_;
goto v___jp_1788_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
lean_dec(v_a_1700_);
lean_dec(v_declName_1698_);
lean_dec_ref(v_x_1685_);
lean_dec(v_mvarId_1683_);
v___x_2014_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12);
v___x_2015_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_2014_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
return v___x_2015_;
}
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
lean_dec(v_declName_1698_);
lean_dec_ref(v_x_1685_);
lean_dec(v_mvarId_1683_);
v_a_2016_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_1699_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_1699_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
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
return v___x_2021_;
}
}
}
}
else
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
lean_dec_ref(v_x_1685_);
lean_dec_ref(v_x_1684_);
lean_dec(v_mvarId_1683_);
v___x_2024_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14);
v___x_2025_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_2024_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
return v___x_2025_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___boxed(lean_object* v_mvarId_2026_, lean_object* v_x_2027_, lean_object* v_x_2028_, lean_object* v_x_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6(v_mvarId_2026_, v_x_2027_, v_x_2028_, v_x_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitSparseCasesOn(lean_object* v_mvarId_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_){
_start:
{
lean_object* v___x_2042_; 
lean_inc(v_mvarId_2036_);
v___x_2042_ = l_Lean_MVarId_getType(v_mvarId_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v_a_2043_; lean_object* v___x_2044_; 
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_a_2043_);
lean_dec_ref_known(v___x_2042_, 1);
v___x_2044_ = l_Lean_Meta_matchEqHEqLHS_x3f(v_a_2043_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_a_2045_; 
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_a_2045_);
lean_dec_ref_known(v___x_2044_, 1);
if (lean_obj_tag(v_a_2045_) == 1)
{
lean_object* v_val_2046_; lean_object* v_snd_2047_; lean_object* v_dummy_2048_; lean_object* v_nargs_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v_val_2046_ = lean_ctor_get(v_a_2045_, 0);
lean_inc(v_val_2046_);
lean_dec_ref_known(v_a_2045_, 1);
v_snd_2047_ = lean_ctor_get(v_val_2046_, 1);
lean_inc(v_snd_2047_);
lean_dec(v_val_2046_);
v_dummy_2048_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0);
v_nargs_2049_ = l_Lean_Expr_getAppNumArgs(v_snd_2047_);
lean_inc(v_nargs_2049_);
v___x_2050_ = lean_mk_array(v_nargs_2049_, v_dummy_2048_);
v___x_2051_ = lean_unsigned_to_nat(1u);
v___x_2052_ = lean_nat_sub(v_nargs_2049_, v___x_2051_);
lean_dec(v_nargs_2049_);
v___x_2053_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6(v_mvarId_2036_, v_snd_2047_, v___x_2050_, v___x_2052_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_);
return v___x_2053_;
}
else
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
lean_dec(v_a_2045_);
lean_dec(v_mvarId_2036_);
v___x_2054_ = lean_obj_once(&l_Lean_Meta_reduceSparseCasesOn___closed__1, &l_Lean_Meta_reduceSparseCasesOn___closed__1_once, _init_l_Lean_Meta_reduceSparseCasesOn___closed__1);
v___x_2055_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_2054_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_);
return v___x_2055_;
}
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
lean_dec(v_mvarId_2036_);
v_a_2056_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_2044_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2044_);
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
else
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
lean_dec(v_mvarId_2036_);
v_a_2064_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2066_ = v___x_2042_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2042_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitSparseCasesOn___boxed(lean_object* v_mvarId_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l_Lean_Meta_splitSparseCasesOn(v_mvarId_2072_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_);
lean_dec(v_a_2076_);
lean_dec_ref(v_a_2075_);
lean_dec(v_a_2074_);
lean_dec_ref(v_a_2073_);
return v_res_2078_;
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
