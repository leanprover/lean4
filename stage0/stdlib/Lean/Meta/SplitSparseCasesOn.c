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
double lean_float_of_nat(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSparseCasesOnInfo___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t lean_bool_not(uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11___boxed(lean_object*);
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
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__7;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__8 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__8_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__8_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(lean_object*, lean_object*, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__0_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Major premise is not a free variable:"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__1_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(lean_object*, lean_object*, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5(lean_object*, lean_object*, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_84_ = lean_st_ref_set(v___y_57_, v___x_83_);
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
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_10955__overap_213_; lean_object* v___x_214_; 
v___x_211_ = lean_box(0);
v___x_212_ = l_instInhabitedOfMonad___redArg(v___x_210_, v___x_211_);
v___x_10955__overap_213_ = lean_panic_fn_borrowed(v___x_212_, v_msg_156_);
lean_dec(v___x_212_);
lean_inc(v___y_160_);
lean_inc_ref(v___y_159_);
lean_inc(v___y_158_);
lean_inc_ref(v___y_157_);
v___x_214_ = lean_apply_5(v___x_10955__overap_213_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, lean_box(0));
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
uint8_t v___x_14726__boxed_560_; lean_object* v_res_561_; 
v___x_14726__boxed_560_ = lean_unbox(v___x_553_);
v_res_561_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(v___x_14726__boxed_560_, v___f_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12(lean_object* v_opts_580_, lean_object* v_opt_581_){
_start:
{
lean_object* v_name_582_; lean_object* v_defValue_583_; lean_object* v_map_584_; lean_object* v___x_585_; 
v_name_582_ = lean_ctor_get(v_opt_581_, 0);
v_defValue_583_ = lean_ctor_get(v_opt_581_, 1);
v_map_584_ = lean_ctor_get(v_opts_580_, 0);
v___x_585_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_584_, v_name_582_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_inc(v_defValue_583_);
return v_defValue_583_;
}
else
{
lean_object* v_val_586_; 
v_val_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_val_586_);
lean_dec_ref_known(v___x_585_, 1);
if (lean_obj_tag(v_val_586_) == 3)
{
lean_object* v_v_587_; 
v_v_587_ = lean_ctor_get(v_val_586_, 0);
lean_inc(v_v_587_);
lean_dec_ref_known(v_val_586_, 1);
return v_v_587_;
}
else
{
lean_dec(v_val_586_);
lean_inc(v_defValue_583_);
return v_defValue_583_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12___boxed(lean_object* v_opts_588_, lean_object* v_opt_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__12(v_opts_588_, v_opt_589_);
lean_dec_ref(v_opt_589_);
lean_dec_ref(v_opts_588_);
return v_res_590_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11(lean_object* v_e_591_){
_start:
{
if (lean_obj_tag(v_e_591_) == 0)
{
uint8_t v___x_592_; 
v___x_592_ = 2;
return v___x_592_;
}
else
{
uint8_t v___x_593_; 
v___x_593_ = 0;
return v___x_593_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11___boxed(lean_object* v_e_594_){
_start:
{
uint8_t v_res_595_; lean_object* v_r_596_; 
v_res_595_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11(v_e_594_);
lean_dec_ref(v_e_594_);
v_r_596_ = lean_box(v_res_595_);
return v_r_596_;
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
v___x_699_ = lean_st_ref_set(v___y_643_, v___x_698_);
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
v_result_763_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__11(v_fst_740_);
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
v___x_801_ = lean_st_ref_set(v___y_738_, v___x_800_);
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
static double _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__7(void){
_start:
{
lean_object* v___x_849_; double v___x_850_; 
v___x_849_ = lean_unsigned_to_nat(1000000000u);
v___x_850_ = lean_float_of_nat(v___x_849_);
return v___x_850_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_854_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5));
v___x_855_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9));
v___x_856_ = l_Lean_Name_append(v___x_855_, v___x_854_);
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
lean_object* v_val_882_; lean_object* v_options_883_; lean_object* v_majorPos_884_; lean_object* v_arity_885_; lean_object* v_insterestingCtors_886_; lean_object* v_inheritedTraceOptions_887_; uint8_t v_hasTrace_888_; lean_object* v___f_889_; lean_object* v___x_890_; lean_object* v___f_891_; lean_object* v___x_892_; uint8_t v___x_893_; uint8_t v___x_894_; 
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
v___x_894_ = lean_bool_not(v_hasTrace_888_);
if (v___x_894_ == 0)
{
lean_object* v___f_895_; lean_object* v___x_896_; uint8_t v___x_897_; lean_object* v___x_898_; lean_object* v___y_900_; lean_object* v___y_901_; uint8_t v___y_902_; lean_object* v_a_903_; lean_object* v___y_916_; lean_object* v___y_917_; uint8_t v___y_918_; lean_object* v_a_919_; uint8_t v___y_929_; uint8_t v_a_971_; 
v___f_895_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1));
v___x_896_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5));
v___x_897_ = 1;
v___x_898_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__6));
if (v_hasTrace_888_ == 0)
{
v_a_971_ = v_hasTrace_888_;
goto v___jp_970_;
}
else
{
lean_object* v___x_975_; uint8_t v___x_976_; 
v___x_975_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10);
v___x_976_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_887_, v_options_883_, v___x_975_);
if (v___x_976_ == 0)
{
v_a_971_ = v___x_976_;
goto v___jp_970_;
}
else
{
v___y_929_ = v___x_976_;
goto v___jp_928_;
}
}
v___jp_899_:
{
lean_object* v___x_904_; double v___x_905_; double v___x_906_; double v___x_907_; double v___x_908_; double v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_904_ = lean_io_mono_nanos_now();
v___x_905_ = lean_float_of_nat(v___y_901_);
v___x_906_ = lean_float_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__7);
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
v___x_914_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_896_, v___x_897_, v___x_898_, v_options_883_, v___y_902_, v___y_900_, v___f_895_, v___x_913_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
return v___x_914_;
}
v___jp_915_:
{
lean_object* v___x_920_; double v___x_921_; double v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_920_ = lean_io_get_num_heartbeats();
v___x_921_ = lean_float_of_nat(v___y_917_);
v___x_922_ = lean_float_of_nat(v___x_920_);
v___x_923_ = lean_box_float(v___x_921_);
v___x_924_ = lean_box_float(v___x_922_);
v___x_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_923_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v_a_919_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
v___x_927_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_896_, v___x_897_, v___x_898_, v_options_883_, v___y_918_, v___y_916_, v___f_895_, v___x_926_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
return v___x_927_;
}
v___jp_928_:
{
lean_object* v___x_930_; lean_object* v_a_931_; lean_object* v___x_932_; uint8_t v___x_933_; 
v___x_930_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___y_871_);
v_a_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_a_931_);
lean_dec_ref(v___x_930_);
v___x_932_ = l_Lean_trace_profiler_useHeartbeats;
v___x_933_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_options_883_, v___x_932_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = lean_io_mono_nanos_now();
v___x_935_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(v___x_893_, v___f_891_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
v_a_936_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_943_ == 0)
{
v___x_938_ = v___x_935_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_935_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
lean_ctor_set_tag(v___x_938_, 1);
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_936_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
v___y_900_ = v_a_931_;
v___y_901_ = v___x_934_;
v___y_902_ = v___y_929_;
v_a_903_ = v___x_941_;
goto v___jp_899_;
}
}
}
else
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_951_; 
v_a_944_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_951_ == 0)
{
v___x_946_ = v___x_935_;
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_935_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
lean_ctor_set_tag(v___x_946_, 0);
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_944_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
v___y_900_ = v_a_931_;
v___y_901_ = v___x_934_;
v___y_902_ = v___y_929_;
v_a_903_ = v___x_949_;
goto v___jp_899_;
}
}
}
}
else
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = lean_io_get_num_heartbeats();
v___x_953_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(v___x_893_, v___f_891_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_953_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_953_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
lean_ctor_set_tag(v___x_956_, 1);
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
v___y_916_ = v_a_931_;
v___y_917_ = v___x_952_;
v___y_918_ = v___y_929_;
v_a_919_ = v___x_959_;
goto v___jp_915_;
}
}
}
else
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
v_a_962_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_969_ == 0)
{
v___x_964_ = v___x_953_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_953_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
lean_ctor_set_tag(v___x_964_, 0);
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_962_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
v___y_916_ = v_a_931_;
v___y_917_ = v___x_952_;
v___y_918_ = v___y_929_;
v_a_919_ = v___x_967_;
goto v___jp_915_;
}
}
}
}
}
v___jp_970_:
{
lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_972_ = l_Lean_trace_profiler;
v___x_973_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_options_883_, v___x_972_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; 
v___x_974_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(v___x_893_, v___f_891_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
return v___x_974_;
}
else
{
v___y_929_ = v_a_971_;
goto v___jp_928_;
}
}
}
else
{
lean_object* v___x_977_; 
v___x_977_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1(v___x_893_, v___f_891_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
return v___x_977_;
}
}
else
{
lean_object* v___x_978_; lean_object* v___x_979_; 
lean_dec(v_a_881_);
lean_dec(v_declName_879_);
lean_dec_ref(v_x_866_);
lean_dec(v_mvarId_864_);
lean_dec_ref(v_snd_863_);
v___x_978_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12);
v___x_979_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_978_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
return v___x_979_;
}
}
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
lean_dec(v_declName_879_);
lean_dec_ref(v_x_866_);
lean_dec(v_mvarId_864_);
lean_dec_ref(v_snd_863_);
v_a_980_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_880_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_880_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
else
{
lean_object* v___x_988_; lean_object* v___x_989_; 
lean_dec_ref(v_x_866_);
lean_dec_ref(v_x_865_);
lean_dec(v_mvarId_864_);
lean_dec_ref(v_snd_863_);
v___x_988_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14);
v___x_989_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_988_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
return v___x_989_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___boxed(lean_object* v_snd_990_, lean_object* v_mvarId_991_, lean_object* v_x_992_, lean_object* v_x_993_, lean_object* v_x_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7(v_snd_990_, v_mvarId_991_, v_x_992_, v_x_993_, v_x_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
return v_res_1000_;
}
}
static lean_object* _init_l_Lean_Meta_reduceSparseCasesOn___closed__1(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = ((lean_object*)(l_Lean_Meta_reduceSparseCasesOn___closed__0));
v___x_1003_ = l_Lean_stringToMessageData(v___x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceSparseCasesOn(lean_object* v_mvarId_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v___x_1010_; 
lean_inc(v_mvarId_1004_);
v___x_1010_ = l_Lean_MVarId_getType(v_mvarId_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v___x_1012_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_a_1011_);
lean_dec_ref_known(v___x_1010_, 1);
v___x_1012_ = l_Lean_Meta_matchEqHEqLHS_x3f(v_a_1011_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
lean_dec_ref_known(v___x_1012_, 1);
if (lean_obj_tag(v_a_1013_) == 1)
{
lean_object* v_val_1014_; lean_object* v_snd_1015_; lean_object* v_dummy_1016_; lean_object* v_nargs_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v_val_1014_ = lean_ctor_get(v_a_1013_, 0);
lean_inc(v_val_1014_);
lean_dec_ref_known(v_a_1013_, 1);
v_snd_1015_ = lean_ctor_get(v_val_1014_, 1);
lean_inc_n(v_snd_1015_, 2);
lean_dec(v_val_1014_);
v_dummy_1016_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0);
v_nargs_1017_ = l_Lean_Expr_getAppNumArgs(v_snd_1015_);
lean_inc(v_nargs_1017_);
v___x_1018_ = lean_mk_array(v_nargs_1017_, v_dummy_1016_);
v___x_1019_ = lean_unsigned_to_nat(1u);
v___x_1020_ = lean_nat_sub(v_nargs_1017_, v___x_1019_);
lean_dec(v_nargs_1017_);
v___x_1021_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7(v_snd_1015_, v_mvarId_1004_, v_snd_1015_, v___x_1018_, v___x_1020_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_);
return v___x_1021_;
}
else
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
lean_dec(v_a_1013_);
lean_dec(v_mvarId_1004_);
v___x_1022_ = lean_obj_once(&l_Lean_Meta_reduceSparseCasesOn___closed__1, &l_Lean_Meta_reduceSparseCasesOn___closed__1_once, _init_l_Lean_Meta_reduceSparseCasesOn___closed__1);
v___x_1023_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1022_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_);
return v___x_1023_;
}
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
lean_dec(v_mvarId_1004_);
v_a_1024_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1012_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1012_);
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
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec(v_mvarId_1004_);
v_a_1032_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_1010_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1010_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceSparseCasesOn___boxed(lean_object* v_mvarId_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Lean_Meta_reduceSparseCasesOn(v_mvarId_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
lean_dec(v_a_1044_);
lean_dec_ref(v_a_1043_);
lean_dec(v_a_1042_);
lean_dec_ref(v_a_1041_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3(lean_object* v_00_u03b1_1047_, lean_object* v_msg_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v_msg_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___boxed(lean_object* v_00_u03b1_1055_, lean_object* v_msg_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3(v_00_u03b1_1055_, v_msg_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10(lean_object* v_00_u03b1_1063_, lean_object* v_x_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___redArg(v_x_1064_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10___boxed(lean_object* v_00_u03b1_1071_, lean_object* v_x_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6_spec__10(v_00_u03b1_1071_, v_x_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(lean_object* v_mvarId_1079_, lean_object* v_x_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1079_, v_x_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1086_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1086_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
v_a_1095_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1086_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1086_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg___boxed(lean_object* v_mvarId_1103_, lean_object* v_x_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1103_, v_x_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2(lean_object* v_00_u03b1_1111_, lean_object* v_mvarId_1112_, lean_object* v_x_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1112_, v_x_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___boxed(lean_object* v_00_u03b1_1120_, lean_object* v_mvarId_1121_, lean_object* v_x_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2(v_00_u03b1_1120_, v_mvarId_1121_, v_x_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_splitSparseCasesOn_spec__1(lean_object* v_a_1129_, lean_object* v_a_1130_){
_start:
{
if (lean_obj_tag(v_a_1129_) == 0)
{
lean_object* v___x_1131_; 
v___x_1131_ = l_List_reverse___redArg(v_a_1130_);
return v___x_1131_;
}
else
{
lean_object* v_head_1132_; lean_object* v_tail_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1142_; 
v_head_1132_ = lean_ctor_get(v_a_1129_, 0);
v_tail_1133_ = lean_ctor_get(v_a_1129_, 1);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_a_1129_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1135_ = v_a_1129_;
v_isShared_1136_ = v_isSharedCheck_1142_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_tail_1133_);
lean_inc(v_head_1132_);
lean_dec(v_a_1129_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1142_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1137_; lean_object* v___x_1139_; 
v___x_1137_ = l_Lean_MessageData_ofExpr(v_head_1132_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 1, v_a_1130_);
lean_ctor_set(v___x_1135_, 0, v___x_1137_);
v___x_1139_ = v___x_1135_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1137_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_a_1130_);
v___x_1139_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
v_a_1129_ = v_tail_1133_;
v_a_1130_ = v___x_1139_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__0));
v___x_1145_ = l_Lean_stringToMessageData(v___x_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0(uint8_t v___y_1146_, lean_object* v_mvarId_1147_, lean_object* v___f_1148_, lean_object* v_declName_1149_, lean_object* v_val_1150_, lean_object* v___x_1151_, lean_object* v_fields_1152_, uint8_t v___x_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; 
if (v___y_1146_ == 0)
{
lean_object* v___x_1215_; 
lean_dec_ref(v_fields_1152_);
lean_dec_ref(v_val_1150_);
lean_dec(v_declName_1149_);
v___x_1215_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_1147_, v___f_1148_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
return v___x_1215_;
}
else
{
lean_object* v___x_1216_; lean_object* v___x_1217_; uint8_t v___x_1218_; 
lean_dec_ref(v___f_1148_);
v___x_1216_ = lean_array_get_size(v_fields_1152_);
v___x_1217_ = lean_unsigned_to_nat(1u);
v___x_1218_ = lean_nat_dec_eq(v___x_1216_, v___x_1217_);
if (v___x_1218_ == 0)
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1219_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___closed__1);
lean_inc_ref(v_fields_1152_);
v___x_1220_ = lean_array_to_list(v_fields_1152_);
v___x_1221_ = lean_box(0);
v___x_1222_ = l_List_mapTR_loop___at___00Lean_Meta_splitSparseCasesOn_spec__1(v___x_1220_, v___x_1221_);
v___x_1223_ = l_Lean_MessageData_ofList(v___x_1222_);
v___x_1224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1219_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
v___x_1225_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1224_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_dec_ref_known(v___x_1225_, 1);
v___y_1160_ = v___y_1154_;
v___y_1161_ = v___y_1155_;
v___y_1162_ = v___y_1156_;
v___y_1163_ = v___y_1157_;
goto v___jp_1159_;
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
lean_dec_ref(v_fields_1152_);
lean_dec_ref(v_val_1150_);
lean_dec(v_declName_1149_);
lean_dec(v_mvarId_1147_);
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1225_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1225_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
else
{
v___y_1160_ = v___y_1154_;
v___y_1161_ = v___y_1155_;
v___y_1162_ = v___y_1156_;
v___y_1163_ = v___y_1157_;
goto v___jp_1159_;
}
}
v___jp_1159_:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_Lean_Meta_getSparseCasesOnEq(v_declName_1149_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; lean_object* v___x_1166_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_a_1165_);
lean_dec_ref_known(v___x_1164_, 1);
lean_inc(v_mvarId_1147_);
v___x_1166_ = l_Lean_MVarId_getType(v_mvarId_1147_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v___x_1168_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_a_1167_);
lean_dec_ref_known(v___x_1166_, 1);
v___x_1168_ = l_Lean_Meta_matchEqHEqLHS_x3f(v_a_1167_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_a_1169_);
lean_dec_ref_known(v___x_1168_, 1);
if (lean_obj_tag(v_a_1169_) == 1)
{
lean_object* v_val_1170_; lean_object* v_snd_1171_; lean_object* v_arity_1172_; lean_object* v___x_1173_; lean_object* v_nargs_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v_dummy_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v_val_1170_ = lean_ctor_get(v_a_1169_, 0);
lean_inc(v_val_1170_);
lean_dec_ref_known(v_a_1169_, 1);
v_snd_1171_ = lean_ctor_get(v_val_1170_, 1);
lean_inc(v_snd_1171_);
lean_dec(v_val_1170_);
v_arity_1172_ = lean_ctor_get(v_val_1150_, 2);
lean_inc(v_arity_1172_);
lean_dec_ref(v_val_1150_);
v___x_1173_ = l_Lean_Expr_getAppFn(v_snd_1171_);
v_nargs_1174_ = l_Lean_Expr_getAppNumArgs(v_snd_1171_);
v___x_1175_ = l_Lean_Expr_constLevels_x21(v___x_1173_);
lean_dec_ref(v___x_1173_);
v___x_1176_ = l_Lean_mkConst(v_a_1165_, v___x_1175_);
v_dummy_1177_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0);
lean_inc(v_nargs_1174_);
v___x_1178_ = lean_mk_array(v_nargs_1174_, v_dummy_1177_);
v___x_1179_ = lean_unsigned_to_nat(1u);
v___x_1180_ = lean_nat_sub(v_nargs_1174_, v___x_1179_);
lean_dec(v_nargs_1174_);
v___x_1181_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_snd_1171_, v___x_1178_, v___x_1180_);
v___x_1182_ = lean_unsigned_to_nat(0u);
v___x_1183_ = l_Array_toSubarray___redArg(v___x_1181_, v___x_1182_, v_arity_1172_);
v___x_1184_ = l_Subarray_copy___redArg(v___x_1183_);
v___x_1185_ = l_Lean_mkAppN(v___x_1176_, v___x_1184_);
lean_dec_ref(v___x_1184_);
v___x_1186_ = lean_array_get(v___x_1151_, v_fields_1152_, v___x_1182_);
lean_dec_ref(v_fields_1152_);
v___x_1187_ = l_Lean_Expr_app___override(v___x_1185_, v___x_1186_);
v___x_1188_ = l___private_Lean_Meta_SplitSparseCasesOn_0__Lean_Meta_rewriteGoalUsingEq(v_mvarId_1147_, v___x_1187_, v___x_1153_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
return v___x_1188_;
}
else
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
lean_dec(v_a_1169_);
lean_dec(v_a_1165_);
lean_dec_ref(v_fields_1152_);
lean_dec_ref(v_val_1150_);
lean_dec(v_mvarId_1147_);
v___x_1189_ = lean_obj_once(&l_Lean_Meta_reduceSparseCasesOn___closed__1, &l_Lean_Meta_reduceSparseCasesOn___closed__1_once, _init_l_Lean_Meta_reduceSparseCasesOn___closed__1);
v___x_1190_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1189_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
return v___x_1190_;
}
}
else
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
lean_dec(v_a_1165_);
lean_dec_ref(v_fields_1152_);
lean_dec_ref(v_val_1150_);
lean_dec(v_mvarId_1147_);
v_a_1191_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___x_1168_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1168_);
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
else
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
lean_dec(v_a_1165_);
lean_dec_ref(v_fields_1152_);
lean_dec_ref(v_val_1150_);
lean_dec(v_mvarId_1147_);
v_a_1199_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1201_ = v___x_1166_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1166_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1199_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
else
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
lean_dec_ref(v_fields_1152_);
lean_dec_ref(v_val_1150_);
lean_dec(v_mvarId_1147_);
v_a_1207_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_1164_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1164_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed(lean_object* v___y_1234_, lean_object* v_mvarId_1235_, lean_object* v___f_1236_, lean_object* v_declName_1237_, lean_object* v_val_1238_, lean_object* v___x_1239_, lean_object* v_fields_1240_, lean_object* v___x_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
uint8_t v___y_33787__boxed_1247_; uint8_t v___x_33792__boxed_1248_; lean_object* v_res_1249_; 
v___y_33787__boxed_1247_ = lean_unbox(v___y_1234_);
v___x_33792__boxed_1248_ = lean_unbox(v___x_1241_);
v_res_1249_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0(v___y_33787__boxed_1247_, v_mvarId_1235_, v___f_1236_, v_declName_1237_, v_val_1238_, v___x_1239_, v_fields_1240_, v___x_33792__boxed_1248_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec_ref(v___x_1239_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(lean_object* v_declName_1250_, lean_object* v_val_1251_, uint8_t v___x_1252_, uint8_t v___x_1253_, size_t v_sz_1254_, size_t v_i_1255_, lean_object* v_bs_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
uint8_t v___x_1262_; 
v___x_1262_ = lean_usize_dec_lt(v_i_1255_, v_sz_1254_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; 
lean_dec_ref(v_val_1251_);
lean_dec(v_declName_1250_);
v___x_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1263_, 0, v_bs_1256_);
return v___x_1263_;
}
else
{
lean_object* v_v_1264_; lean_object* v_toInductionSubgoal_1265_; lean_object* v_ctorName_1266_; lean_object* v_mvarId_1267_; lean_object* v_fields_1268_; lean_object* v___f_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v_bs_x27_1272_; uint8_t v___y_1274_; 
v_v_1264_ = lean_array_uget_borrowed(v_bs_1256_, v_i_1255_);
v_toInductionSubgoal_1265_ = lean_ctor_get(v_v_1264_, 0);
v_ctorName_1266_ = lean_ctor_get(v_v_1264_, 1);
lean_inc(v_ctorName_1266_);
v_mvarId_1267_ = lean_ctor_get(v_toInductionSubgoal_1265_, 0);
lean_inc(v_mvarId_1267_);
v_fields_1268_ = lean_ctor_get(v_toInductionSubgoal_1265_, 1);
lean_inc_ref(v_fields_1268_);
v___f_1269_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0));
v___x_1270_ = l_Lean_instInhabitedExpr;
v___x_1271_ = lean_unsigned_to_nat(0u);
v_bs_x27_1272_ = lean_array_uset(v_bs_1256_, v_i_1255_, v___x_1271_);
if (lean_obj_tag(v_ctorName_1266_) == 0)
{
v___y_1274_ = v___x_1253_;
goto v___jp_1273_;
}
else
{
lean_dec_ref_known(v_ctorName_1266_, 1);
v___y_1274_ = v___x_1252_;
goto v___jp_1273_;
}
v___jp_1273_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___y_1277_; lean_object* v___x_1278_; 
v___x_1275_ = lean_box(v___y_1274_);
v___x_1276_ = lean_box(v___x_1252_);
lean_inc_ref(v_val_1251_);
lean_inc(v_declName_1250_);
lean_inc(v_mvarId_1267_);
v___y_1277_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed), 13, 8);
lean_closure_set(v___y_1277_, 0, v___x_1275_);
lean_closure_set(v___y_1277_, 1, v_mvarId_1267_);
lean_closure_set(v___y_1277_, 2, v___f_1269_);
lean_closure_set(v___y_1277_, 3, v_declName_1250_);
lean_closure_set(v___y_1277_, 4, v_val_1251_);
lean_closure_set(v___y_1277_, 5, v___x_1270_);
lean_closure_set(v___y_1277_, 6, v_fields_1268_);
lean_closure_set(v___y_1277_, 7, v___x_1276_);
v___x_1278_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1267_, v___y_1277_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; size_t v___x_1280_; size_t v___x_1281_; lean_object* v___x_1282_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
lean_dec_ref_known(v___x_1278_, 1);
v___x_1280_ = ((size_t)1ULL);
v___x_1281_ = lean_usize_add(v_i_1255_, v___x_1280_);
v___x_1282_ = lean_array_uset(v_bs_x27_1272_, v_i_1255_, v_a_1279_);
v_i_1255_ = v___x_1281_;
v_bs_1256_ = v___x_1282_;
goto _start;
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_dec_ref(v_bs_x27_1272_);
lean_dec_ref(v_val_1251_);
lean_dec(v_declName_1250_);
v_a_1284_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1278_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1278_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4___boxed(lean_object* v_declName_1292_, lean_object* v_val_1293_, lean_object* v___x_1294_, lean_object* v___x_1295_, lean_object* v_sz_1296_, lean_object* v_i_1297_, lean_object* v_bs_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
uint8_t v___x_33971__boxed_1304_; uint8_t v___x_33972__boxed_1305_; size_t v_sz_boxed_1306_; size_t v_i_boxed_1307_; lean_object* v_res_1308_; 
v___x_33971__boxed_1304_ = lean_unbox(v___x_1294_);
v___x_33972__boxed_1305_ = lean_unbox(v___x_1295_);
v_sz_boxed_1306_ = lean_unbox_usize(v_sz_1296_);
lean_dec(v_sz_1296_);
v_i_boxed_1307_ = lean_unbox_usize(v_i_1297_);
lean_dec(v_i_1297_);
v_res_1308_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(v_declName_1292_, v_val_1293_, v___x_33971__boxed_1304_, v___x_33972__boxed_1305_, v_sz_boxed_1306_, v_i_boxed_1307_, v_bs_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
return v_res_1308_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__1));
v___x_1313_ = l_Lean_stringToMessageData(v___x_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(lean_object* v_val_1314_, lean_object* v___x_1315_, lean_object* v_x_1316_, lean_object* v_mvarId_1317_, uint8_t v___x_1318_, lean_object* v_declName_1319_, uint8_t v___x_1320_, lean_object* v_____r_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v_majorPos_1351_; lean_object* v_arity_1352_; lean_object* v_insterestingCtors_1353_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___x_1373_; uint8_t v___x_1374_; 
v_majorPos_1351_ = lean_ctor_get(v_val_1314_, 1);
v_arity_1352_ = lean_ctor_get(v_val_1314_, 2);
v_insterestingCtors_1353_ = lean_ctor_get(v_val_1314_, 3);
v___x_1373_ = lean_array_get_size(v_x_1316_);
v___x_1374_ = lean_nat_dec_lt(v___x_1373_, v_arity_1352_);
if (v___x_1374_ == 0)
{
v___y_1355_ = v___y_1322_;
v___y_1356_ = v___y_1323_;
v___y_1357_ = v___y_1324_;
v___y_1358_ = v___y_1325_;
goto v___jp_1354_;
}
else
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
lean_dec(v_declName_1319_);
lean_dec(v_mvarId_1317_);
lean_dec_ref(v_val_1314_);
v___x_1375_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1);
v___x_1376_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1375_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1376_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1376_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
v___jp_1327_:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1334_ = lean_array_get_borrowed(v___x_1315_, v_x_1316_, v___y_1329_);
lean_dec(v___y_1329_);
v___x_1335_ = l_Lean_Expr_fvarId_x21(v___x_1334_);
v___x_1336_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__0));
v___x_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1337_, 0, v___y_1328_);
v___x_1338_ = l_Lean_MVarId_cases(v_mvarId_1317_, v___x_1335_, v___x_1336_, v___x_1318_, v___x_1337_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v_a_1339_; size_t v_sz_1340_; size_t v___x_1341_; lean_object* v___x_1342_; 
v_a_1339_ = lean_ctor_get(v___x_1338_, 0);
lean_inc(v_a_1339_);
lean_dec_ref_known(v___x_1338_, 1);
v_sz_1340_ = lean_array_size(v_a_1339_);
v___x_1341_ = ((size_t)0ULL);
v___x_1342_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__4(v_declName_1319_, v_val_1314_, v___x_1318_, v___x_1320_, v_sz_1340_, v___x_1341_, v_a_1339_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
return v___x_1342_;
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
lean_dec(v_declName_1319_);
lean_dec_ref(v_val_1314_);
v_a_1343_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1338_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1338_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
v___jp_1354_:
{
lean_object* v___x_1359_; uint8_t v___x_1360_; 
v___x_1359_ = lean_array_get_borrowed(v___x_1315_, v_x_1316_, v_majorPos_1351_);
v___x_1360_ = l_Lean_Expr_isFVar(v___x_1359_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_dec(v_declName_1319_);
lean_dec(v_mvarId_1317_);
lean_dec_ref(v_val_1314_);
v___x_1361_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2);
lean_inc(v___x_1359_);
v___x_1362_ = l_Lean_indentExpr(v___x_1359_);
v___x_1363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1361_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
v___x_1364_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1363_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1364_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1364_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
else
{
lean_inc(v_majorPos_1351_);
lean_inc_ref(v_insterestingCtors_1353_);
v___y_1328_ = v_insterestingCtors_1353_;
v___y_1329_ = v_majorPos_1351_;
v___y_1330_ = v___y_1355_;
v___y_1331_ = v___y_1356_;
v___y_1332_ = v___y_1357_;
v___y_1333_ = v___y_1358_;
goto v___jp_1327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___boxed(lean_object* v_val_1385_, lean_object* v___x_1386_, lean_object* v_x_1387_, lean_object* v_mvarId_1388_, lean_object* v___x_1389_, lean_object* v_declName_1390_, lean_object* v___x_1391_, lean_object* v_____r_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
uint8_t v___x_34061__boxed_1398_; uint8_t v___x_34063__boxed_1399_; lean_object* v_res_1400_; 
v___x_34061__boxed_1398_ = lean_unbox(v___x_1389_);
v___x_34063__boxed_1399_ = lean_unbox(v___x_1391_);
v_res_1400_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(v_val_1385_, v___x_1386_, v_x_1387_, v_mvarId_1388_, v___x_34061__boxed_1398_, v_declName_1390_, v___x_34063__boxed_1399_, v_____r_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec_ref(v_x_1387_);
lean_dec_ref(v___x_1386_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(lean_object* v_cls_1403_, lean_object* v_msg_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v_ref_1410_; lean_object* v___x_1411_; lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1456_; 
v_ref_1410_ = lean_ctor_get(v___y_1407_, 5);
v___x_1411_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3_spec__5(v_msg_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1414_ = v___x_1411_;
v_isShared_1415_ = v_isSharedCheck_1456_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1411_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1456_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1416_; lean_object* v_traceState_1417_; lean_object* v_env_1418_; lean_object* v_nextMacroScope_1419_; lean_object* v_ngen_1420_; lean_object* v_auxDeclNGen_1421_; lean_object* v_cache_1422_; lean_object* v_messages_1423_; lean_object* v_infoState_1424_; lean_object* v_snapshotTasks_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1455_; 
v___x_1416_ = lean_st_ref_take(v___y_1408_);
v_traceState_1417_ = lean_ctor_get(v___x_1416_, 4);
v_env_1418_ = lean_ctor_get(v___x_1416_, 0);
v_nextMacroScope_1419_ = lean_ctor_get(v___x_1416_, 1);
v_ngen_1420_ = lean_ctor_get(v___x_1416_, 2);
v_auxDeclNGen_1421_ = lean_ctor_get(v___x_1416_, 3);
v_cache_1422_ = lean_ctor_get(v___x_1416_, 5);
v_messages_1423_ = lean_ctor_get(v___x_1416_, 6);
v_infoState_1424_ = lean_ctor_get(v___x_1416_, 7);
v_snapshotTasks_1425_ = lean_ctor_get(v___x_1416_, 8);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1427_ = v___x_1416_;
v_isShared_1428_ = v_isSharedCheck_1455_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_snapshotTasks_1425_);
lean_inc(v_infoState_1424_);
lean_inc(v_messages_1423_);
lean_inc(v_cache_1422_);
lean_inc(v_traceState_1417_);
lean_inc(v_auxDeclNGen_1421_);
lean_inc(v_ngen_1420_);
lean_inc(v_nextMacroScope_1419_);
lean_inc(v_env_1418_);
lean_dec(v___x_1416_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1455_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
uint64_t v_tid_1429_; lean_object* v_traces_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1454_; 
v_tid_1429_ = lean_ctor_get_uint64(v_traceState_1417_, sizeof(void*)*1);
v_traces_1430_ = lean_ctor_get(v_traceState_1417_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_traceState_1417_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1432_ = v_traceState_1417_;
v_isShared_1433_ = v_isSharedCheck_1454_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_traces_1430_);
lean_dec(v_traceState_1417_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1454_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1434_; double v___x_1435_; uint8_t v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1444_; 
v___x_1434_ = lean_box(0);
v___x_1435_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6___closed__0);
v___x_1436_ = 0;
v___x_1437_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__6));
v___x_1438_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1438_, 0, v_cls_1403_);
lean_ctor_set(v___x_1438_, 1, v___x_1434_);
lean_ctor_set(v___x_1438_, 2, v___x_1437_);
lean_ctor_set_float(v___x_1438_, sizeof(void*)*3, v___x_1435_);
lean_ctor_set_float(v___x_1438_, sizeof(void*)*3 + 8, v___x_1435_);
lean_ctor_set_uint8(v___x_1438_, sizeof(void*)*3 + 16, v___x_1436_);
v___x_1439_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___closed__0));
v___x_1440_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1438_);
lean_ctor_set(v___x_1440_, 1, v_a_1412_);
lean_ctor_set(v___x_1440_, 2, v___x_1439_);
lean_inc(v_ref_1410_);
v___x_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1441_, 0, v_ref_1410_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
v___x_1442_ = l_Lean_PersistentArray_push___redArg(v_traces_1430_, v___x_1441_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 0, v___x_1442_);
v___x_1444_ = v___x_1432_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1442_);
lean_ctor_set_uint64(v_reuseFailAlloc_1453_, sizeof(void*)*1, v_tid_1429_);
v___x_1444_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v___x_1446_; 
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 4, v___x_1444_);
v___x_1446_ = v___x_1427_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_env_1418_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_nextMacroScope_1419_);
lean_ctor_set(v_reuseFailAlloc_1452_, 2, v_ngen_1420_);
lean_ctor_set(v_reuseFailAlloc_1452_, 3, v_auxDeclNGen_1421_);
lean_ctor_set(v_reuseFailAlloc_1452_, 4, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1452_, 5, v_cache_1422_);
lean_ctor_set(v_reuseFailAlloc_1452_, 6, v_messages_1423_);
lean_ctor_set(v_reuseFailAlloc_1452_, 7, v_infoState_1424_);
lean_ctor_set(v_reuseFailAlloc_1452_, 8, v_snapshotTasks_1425_);
v___x_1446_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1450_; 
v___x_1447_ = lean_st_ref_set(v___y_1408_, v___x_1446_);
v___x_1448_ = lean_box(0);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 0, v___x_1448_);
v___x_1450_ = v___x_1414_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1448_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0___boxed(lean_object* v_cls_1457_, lean_object* v_msg_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v_cls_1457_, v_msg_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(lean_object* v_declName_1465_, lean_object* v_val_1466_, uint8_t v___x_1467_, size_t v_sz_1468_, size_t v_i_1469_, lean_object* v_bs_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
uint8_t v___x_1476_; 
v___x_1476_ = lean_usize_dec_lt(v_i_1469_, v_sz_1468_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; 
lean_dec_ref(v_val_1466_);
lean_dec(v_declName_1465_);
v___x_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1477_, 0, v_bs_1470_);
return v___x_1477_;
}
else
{
lean_object* v_v_1478_; lean_object* v_toInductionSubgoal_1479_; lean_object* v_ctorName_1480_; lean_object* v_mvarId_1481_; lean_object* v_fields_1482_; lean_object* v___f_1483_; lean_object* v___x_1484_; uint8_t v___x_1485_; lean_object* v___x_1486_; lean_object* v_bs_x27_1487_; uint8_t v___y_1489_; 
v_v_1478_ = lean_array_uget_borrowed(v_bs_1470_, v_i_1469_);
v_toInductionSubgoal_1479_ = lean_ctor_get(v_v_1478_, 0);
v_ctorName_1480_ = lean_ctor_get(v_v_1478_, 1);
lean_inc(v_ctorName_1480_);
v_mvarId_1481_ = lean_ctor_get(v_toInductionSubgoal_1479_, 0);
lean_inc(v_mvarId_1481_);
v_fields_1482_ = lean_ctor_get(v_toInductionSubgoal_1479_, 1);
lean_inc_ref(v_fields_1482_);
v___f_1483_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0));
v___x_1484_ = l_Lean_instInhabitedExpr;
v___x_1485_ = 0;
v___x_1486_ = lean_unsigned_to_nat(0u);
v_bs_x27_1487_ = lean_array_uset(v_bs_1470_, v_i_1469_, v___x_1486_);
if (lean_obj_tag(v_ctorName_1480_) == 0)
{
if (v___x_1467_ == 0)
{
goto v___jp_1507_;
}
else
{
v___y_1489_ = v___x_1467_;
goto v___jp_1488_;
}
}
else
{
lean_dec_ref_known(v_ctorName_1480_, 1);
goto v___jp_1507_;
}
v___jp_1488_:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___y_1492_; lean_object* v___x_1493_; 
v___x_1490_ = lean_box(v___y_1489_);
v___x_1491_ = lean_box(v___x_1485_);
lean_inc_ref(v_val_1466_);
lean_inc(v_declName_1465_);
lean_inc(v_mvarId_1481_);
v___y_1492_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed), 13, 8);
lean_closure_set(v___y_1492_, 0, v___x_1490_);
lean_closure_set(v___y_1492_, 1, v_mvarId_1481_);
lean_closure_set(v___y_1492_, 2, v___f_1483_);
lean_closure_set(v___y_1492_, 3, v_declName_1465_);
lean_closure_set(v___y_1492_, 4, v_val_1466_);
lean_closure_set(v___y_1492_, 5, v___x_1484_);
lean_closure_set(v___y_1492_, 6, v_fields_1482_);
lean_closure_set(v___y_1492_, 7, v___x_1491_);
v___x_1493_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1481_, v___y_1492_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_a_1494_; size_t v___x_1495_; size_t v___x_1496_; lean_object* v___x_1497_; 
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_a_1494_);
lean_dec_ref_known(v___x_1493_, 1);
v___x_1495_ = ((size_t)1ULL);
v___x_1496_ = lean_usize_add(v_i_1469_, v___x_1495_);
v___x_1497_ = lean_array_uset(v_bs_x27_1487_, v_i_1469_, v_a_1494_);
v_i_1469_ = v___x_1496_;
v_bs_1470_ = v___x_1497_;
goto _start;
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1506_; 
lean_dec_ref(v_bs_x27_1487_);
lean_dec_ref(v_val_1466_);
lean_dec(v_declName_1465_);
v_a_1499_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1501_ = v___x_1493_;
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1493_);
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
}
v___jp_1507_:
{
v___y_1489_ = v___x_1485_;
goto v___jp_1488_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___boxed(lean_object* v_declName_1508_, lean_object* v_val_1509_, lean_object* v___x_1510_, lean_object* v_sz_1511_, lean_object* v_i_1512_, lean_object* v_bs_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
uint8_t v___x_34307__boxed_1519_; size_t v_sz_boxed_1520_; size_t v_i_boxed_1521_; lean_object* v_res_1522_; 
v___x_34307__boxed_1519_ = lean_unbox(v___x_1510_);
v_sz_boxed_1520_ = lean_unbox_usize(v_sz_1511_);
lean_dec(v_sz_1511_);
v_i_boxed_1521_ = lean_unbox_usize(v_i_1512_);
lean_dec(v_i_1512_);
v_res_1522_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(v_declName_1508_, v_val_1509_, v___x_34307__boxed_1519_, v_sz_boxed_1520_, v_i_boxed_1521_, v_bs_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__4(lean_object* v_val_1523_, lean_object* v___x_1524_, lean_object* v_x_1525_, lean_object* v_mvarId_1526_, lean_object* v_declName_1527_, uint8_t v___x_1528_, lean_object* v_____r_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v_majorPos_1560_; lean_object* v_arity_1561_; lean_object* v_insterestingCtors_1562_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___x_1582_; uint8_t v___x_1583_; 
v_majorPos_1560_ = lean_ctor_get(v_val_1523_, 1);
v_arity_1561_ = lean_ctor_get(v_val_1523_, 2);
v_insterestingCtors_1562_ = lean_ctor_get(v_val_1523_, 3);
v___x_1582_ = lean_array_get_size(v_x_1525_);
v___x_1583_ = lean_nat_dec_lt(v___x_1582_, v_arity_1561_);
if (v___x_1583_ == 0)
{
v___y_1564_ = v___y_1530_;
v___y_1565_ = v___y_1531_;
v___y_1566_ = v___y_1532_;
v___y_1567_ = v___y_1533_;
goto v___jp_1563_;
}
else
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
lean_dec(v_declName_1527_);
lean_dec(v_mvarId_1526_);
lean_dec_ref(v_val_1523_);
v___x_1584_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1);
v___x_1585_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1584_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1585_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1585_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
v___jp_1535_:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; uint8_t v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1542_ = lean_array_get_borrowed(v___x_1524_, v_x_1525_, v___y_1537_);
lean_dec(v___y_1537_);
v___x_1543_ = l_Lean_Expr_fvarId_x21(v___x_1542_);
v___x_1544_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__0));
v___x_1545_ = 0;
v___x_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1546_, 0, v___y_1536_);
v___x_1547_ = l_Lean_MVarId_cases(v_mvarId_1526_, v___x_1543_, v___x_1544_, v___x_1545_, v___x_1546_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; size_t v_sz_1549_; size_t v___x_1550_; lean_object* v___x_1551_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1548_);
lean_dec_ref_known(v___x_1547_, 1);
v_sz_1549_ = lean_array_size(v_a_1548_);
v___x_1550_ = ((size_t)0ULL);
v___x_1551_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3(v_declName_1527_, v_val_1523_, v___x_1528_, v_sz_1549_, v___x_1550_, v_a_1548_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
return v___x_1551_;
}
else
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
lean_dec(v_declName_1527_);
lean_dec_ref(v_val_1523_);
v_a_1552_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v___x_1547_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1547_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1552_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
v___jp_1563_:
{
lean_object* v___x_1568_; uint8_t v___x_1569_; 
v___x_1568_ = lean_array_get_borrowed(v___x_1524_, v_x_1525_, v_majorPos_1560_);
v___x_1569_ = l_Lean_Expr_isFVar(v___x_1568_);
if (v___x_1569_ == 0)
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
lean_dec(v_declName_1527_);
lean_dec(v_mvarId_1526_);
lean_dec_ref(v_val_1523_);
v___x_1570_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2);
lean_inc(v___x_1568_);
v___x_1571_ = l_Lean_indentExpr(v___x_1568_);
v___x_1572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1570_);
lean_ctor_set(v___x_1572_, 1, v___x_1571_);
v___x_1573_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1572_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1573_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1573_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
else
{
lean_inc(v_majorPos_1560_);
lean_inc_ref(v_insterestingCtors_1562_);
v___y_1536_ = v_insterestingCtors_1562_;
v___y_1537_ = v_majorPos_1560_;
v___y_1538_ = v___y_1564_;
v___y_1539_ = v___y_1565_;
v___y_1540_ = v___y_1566_;
v___y_1541_ = v___y_1567_;
goto v___jp_1535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__4___boxed(lean_object* v_val_1594_, lean_object* v___x_1595_, lean_object* v_x_1596_, lean_object* v_mvarId_1597_, lean_object* v_declName_1598_, lean_object* v___x_1599_, lean_object* v_____r_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
uint8_t v___x_34394__boxed_1606_; lean_object* v_res_1607_; 
v___x_34394__boxed_1606_ = lean_unbox(v___x_1599_);
v_res_1607_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__4(v_val_1594_, v___x_1595_, v_x_1596_, v_mvarId_1597_, v_declName_1598_, v___x_34394__boxed_1606_, v_____r_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec_ref(v_x_1596_);
lean_dec_ref(v___x_1595_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5(lean_object* v_declName_1608_, lean_object* v_val_1609_, uint8_t v___x_1610_, size_t v_sz_1611_, size_t v_i_1612_, lean_object* v_bs_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
uint8_t v___x_1619_; 
v___x_1619_ = lean_usize_dec_lt(v_i_1612_, v_sz_1611_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; 
lean_dec_ref(v_val_1609_);
lean_dec(v_declName_1608_);
v___x_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1620_, 0, v_bs_1613_);
return v___x_1620_;
}
else
{
lean_object* v_v_1621_; lean_object* v_toInductionSubgoal_1622_; lean_object* v_ctorName_1623_; lean_object* v_mvarId_1624_; lean_object* v_fields_1625_; lean_object* v___f_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v_bs_x27_1629_; uint8_t v___y_1631_; 
v_v_1621_ = lean_array_uget_borrowed(v_bs_1613_, v_i_1612_);
v_toInductionSubgoal_1622_ = lean_ctor_get(v_v_1621_, 0);
v_ctorName_1623_ = lean_ctor_get(v_v_1621_, 1);
lean_inc(v_ctorName_1623_);
v_mvarId_1624_ = lean_ctor_get(v_toInductionSubgoal_1622_, 0);
lean_inc(v_mvarId_1624_);
v_fields_1625_ = lean_ctor_get(v_toInductionSubgoal_1622_, 1);
lean_inc_ref(v_fields_1625_);
v___f_1626_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__0));
v___x_1627_ = l_Lean_instInhabitedExpr;
v___x_1628_ = lean_unsigned_to_nat(0u);
v_bs_x27_1629_ = lean_array_uset(v_bs_1613_, v_i_1612_, v___x_1628_);
if (lean_obj_tag(v_ctorName_1623_) == 0)
{
v___y_1631_ = v___x_1619_;
goto v___jp_1630_;
}
else
{
lean_dec_ref_known(v_ctorName_1623_, 1);
if (v___x_1610_ == 0)
{
v___y_1631_ = v___x_1610_;
goto v___jp_1630_;
}
else
{
v___y_1631_ = v___x_1619_;
goto v___jp_1630_;
}
}
v___jp_1630_:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___y_1634_; lean_object* v___x_1635_; 
v___x_1632_ = lean_box(v___y_1631_);
v___x_1633_ = lean_box(v___x_1610_);
lean_inc_ref(v_val_1609_);
lean_inc(v_declName_1608_);
lean_inc(v_mvarId_1624_);
v___y_1634_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__3___lam__0___boxed), 13, 8);
lean_closure_set(v___y_1634_, 0, v___x_1632_);
lean_closure_set(v___y_1634_, 1, v_mvarId_1624_);
lean_closure_set(v___y_1634_, 2, v___f_1626_);
lean_closure_set(v___y_1634_, 3, v_declName_1608_);
lean_closure_set(v___y_1634_, 4, v_val_1609_);
lean_closure_set(v___y_1634_, 5, v___x_1627_);
lean_closure_set(v___y_1634_, 6, v_fields_1625_);
lean_closure_set(v___y_1634_, 7, v___x_1633_);
v___x_1635_ = l_Lean_MVarId_withContext___at___00Lean_Meta_splitSparseCasesOn_spec__2___redArg(v_mvarId_1624_, v___y_1634_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; size_t v___x_1637_; size_t v___x_1638_; lean_object* v___x_1639_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_a_1636_);
lean_dec_ref_known(v___x_1635_, 1);
v___x_1637_ = ((size_t)1ULL);
v___x_1638_ = lean_usize_add(v_i_1612_, v___x_1637_);
v___x_1639_ = lean_array_uset(v_bs_x27_1629_, v_i_1612_, v_a_1636_);
v_i_1612_ = v___x_1638_;
v_bs_1613_ = v___x_1639_;
goto _start;
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
lean_dec_ref(v_bs_x27_1629_);
lean_dec_ref(v_val_1609_);
lean_dec(v_declName_1608_);
v_a_1641_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1635_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1635_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5___boxed(lean_object* v_declName_1649_, lean_object* v_val_1650_, lean_object* v___x_1651_, lean_object* v_sz_1652_, lean_object* v_i_1653_, lean_object* v_bs_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
uint8_t v___x_34541__boxed_1660_; size_t v_sz_boxed_1661_; size_t v_i_boxed_1662_; lean_object* v_res_1663_; 
v___x_34541__boxed_1660_ = lean_unbox(v___x_1651_);
v_sz_boxed_1661_ = lean_unbox_usize(v_sz_1652_);
lean_dec(v_sz_1652_);
v_i_boxed_1662_ = lean_unbox_usize(v_i_1653_);
lean_dec(v_i_1653_);
v_res_1663_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5(v_declName_1649_, v_val_1650_, v___x_34541__boxed_1660_, v_sz_boxed_1661_, v_i_boxed_1662_, v_bs_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(lean_object* v_val_1664_, lean_object* v___x_1665_, lean_object* v_x_1666_, lean_object* v_mvarId_1667_, uint8_t v___x_1668_, lean_object* v_declName_1669_, lean_object* v_____r_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v_majorPos_1700_; lean_object* v_arity_1701_; lean_object* v_insterestingCtors_1702_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___x_1722_; uint8_t v___x_1723_; 
v_majorPos_1700_ = lean_ctor_get(v_val_1664_, 1);
v_arity_1701_ = lean_ctor_get(v_val_1664_, 2);
v_insterestingCtors_1702_ = lean_ctor_get(v_val_1664_, 3);
v___x_1722_ = lean_array_get_size(v_x_1666_);
v___x_1723_ = lean_nat_dec_lt(v___x_1722_, v_arity_1701_);
if (v___x_1723_ == 0)
{
v___y_1704_ = v___y_1671_;
v___y_1705_ = v___y_1672_;
v___y_1706_ = v___y_1673_;
v___y_1707_ = v___y_1674_;
goto v___jp_1703_;
}
else
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
lean_dec(v_declName_1669_);
lean_dec(v_mvarId_1667_);
lean_dec_ref(v_val_1664_);
v___x_1724_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__1___closed__1);
v___x_1725_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1724_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1728_ = v___x_1725_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1725_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
v___jp_1676_:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1683_ = lean_array_get_borrowed(v___x_1665_, v_x_1666_, v___y_1677_);
lean_dec(v___y_1677_);
v___x_1684_ = l_Lean_Expr_fvarId_x21(v___x_1683_);
v___x_1685_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__0));
v___x_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1686_, 0, v___y_1678_);
v___x_1687_ = l_Lean_MVarId_cases(v_mvarId_1667_, v___x_1684_, v___x_1685_, v___x_1668_, v___x_1686_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; size_t v_sz_1689_; size_t v___x_1690_; lean_object* v___x_1691_; 
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_a_1688_);
lean_dec_ref_known(v___x_1687_, 1);
v_sz_1689_ = lean_array_size(v_a_1688_);
v___x_1690_ = ((size_t)0ULL);
v___x_1691_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_splitSparseCasesOn_spec__5(v_declName_1669_, v_val_1664_, v___x_1668_, v_sz_1689_, v___x_1690_, v_a_1688_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
return v___x_1691_;
}
else
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1699_; 
lean_dec(v_declName_1669_);
lean_dec_ref(v_val_1664_);
v_a_1692_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1694_ = v___x_1687_;
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1687_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1697_; 
if (v_isShared_1695_ == 0)
{
v___x_1697_ = v___x_1694_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_a_1692_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
}
v___jp_1703_:
{
lean_object* v___x_1708_; uint8_t v___x_1709_; 
v___x_1708_ = lean_array_get_borrowed(v___x_1665_, v_x_1666_, v_majorPos_1700_);
v___x_1709_ = l_Lean_Expr_isFVar(v___x_1708_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
lean_dec(v_declName_1669_);
lean_dec(v_mvarId_1667_);
lean_dec_ref(v_val_1664_);
v___x_1710_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___closed__2);
lean_inc(v___x_1708_);
v___x_1711_ = l_Lean_indentExpr(v___x_1708_);
v___x_1712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1710_);
lean_ctor_set(v___x_1712_, 1, v___x_1711_);
v___x_1713_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_1712_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1713_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1713_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
else
{
lean_inc_ref(v_insterestingCtors_1702_);
lean_inc(v_majorPos_1700_);
v___y_1677_ = v_majorPos_1700_;
v___y_1678_ = v_insterestingCtors_1702_;
v___y_1679_ = v___y_1704_;
v___y_1680_ = v___y_1705_;
v___y_1681_ = v___y_1706_;
v___y_1682_ = v___y_1707_;
goto v___jp_1676_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___boxed(lean_object* v_val_1734_, lean_object* v___x_1735_, lean_object* v_x_1736_, lean_object* v_mvarId_1737_, lean_object* v___x_1738_, lean_object* v_declName_1739_, lean_object* v_____r_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
uint8_t v___x_34622__boxed_1746_; lean_object* v_res_1747_; 
v___x_34622__boxed_1746_ = lean_unbox(v___x_1738_);
v_res_1747_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(v_val_1734_, v___x_1735_, v_x_1736_, v_mvarId_1737_, v___x_34622__boxed_1746_, v_declName_1739_, v_____r_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec_ref(v_x_1736_);
lean_dec_ref(v___x_1735_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(lean_object* v___x_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v_options_1754_; uint8_t v_hasTrace_1755_; 
v_options_1754_ = lean_ctor_get(v___y_1751_, 2);
v_hasTrace_1755_ = lean_ctor_get_uint8(v_options_1754_, sizeof(void*)*1);
if (v_hasTrace_1755_ == 0)
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
lean_dec(v___x_1748_);
v___x_1756_ = lean_box(v_hasTrace_1755_);
v___x_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
return v___x_1757_;
}
else
{
lean_object* v_inheritedTraceOptions_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; uint8_t v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v_inheritedTraceOptions_1758_ = lean_ctor_get(v___y_1751_, 13);
v___x_1759_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__9));
v___x_1760_ = l_Lean_Name_append(v___x_1759_, v___x_1748_);
v___x_1761_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1758_, v_options_1754_, v___x_1760_);
lean_dec(v___x_1760_);
v___x_1762_ = lean_box(v___x_1761_);
v___x_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
return v___x_1763_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0___boxed(lean_object* v___x_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v___x_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
return v_res_1770_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1(void){
_start:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1772_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__0));
v___x_1773_ = l_Lean_stringToMessageData(v___x_1772_);
return v___x_1773_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3(void){
_start:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1775_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__2));
v___x_1776_ = l_Lean_stringToMessageData(v___x_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6(lean_object* v_mvarId_1777_, lean_object* v_x_1778_, lean_object* v_x_1779_, lean_object* v_x_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
if (lean_obj_tag(v_x_1778_) == 5)
{
lean_object* v_fn_1786_; lean_object* v_arg_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v_fn_1786_ = lean_ctor_get(v_x_1778_, 0);
lean_inc_ref(v_fn_1786_);
v_arg_1787_ = lean_ctor_get(v_x_1778_, 1);
lean_inc_ref(v_arg_1787_);
lean_dec_ref_known(v_x_1778_, 2);
v___x_1788_ = lean_array_set(v_x_1779_, v_x_1780_, v_arg_1787_);
v___x_1789_ = lean_unsigned_to_nat(1u);
v___x_1790_ = lean_nat_sub(v_x_1780_, v___x_1789_);
lean_dec(v_x_1780_);
v_x_1778_ = v_fn_1786_;
v_x_1779_ = v___x_1788_;
v_x_1780_ = v___x_1790_;
goto _start;
}
else
{
lean_dec(v_x_1780_);
if (lean_obj_tag(v_x_1778_) == 4)
{
lean_object* v_declName_1792_; lean_object* v___x_1793_; 
v_declName_1792_ = lean_ctor_get(v_x_1778_, 0);
lean_inc_n(v_declName_1792_, 2);
lean_dec_ref_known(v_x_1778_, 2);
v___x_1793_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_declName_1792_, v___y_1784_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_a_1794_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_a_1794_);
lean_dec_ref_known(v___x_1793_, 1);
if (lean_obj_tag(v_a_1794_) == 1)
{
lean_object* v_options_1795_; lean_object* v_val_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_2111_; 
v_options_1795_ = lean_ctor_get(v___y_1783_, 2);
v_val_1796_ = lean_ctor_get(v_a_1794_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v_a_1794_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_1798_ = v_a_1794_;
v_isShared_1799_ = v_isSharedCheck_2111_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_val_1796_);
lean_dec(v_a_1794_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_2111_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v_inheritedTraceOptions_1800_; uint8_t v_hasTrace_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___y_1805_; lean_object* v___y_1806_; uint8_t v___y_1807_; lean_object* v___y_1840_; lean_object* v_a_1841_; lean_object* v___y_1845_; lean_object* v___y_1848_; lean_object* v___y_1852_; lean_object* v___y_1853_; uint8_t v___y_1854_; lean_object* v___y_1887_; lean_object* v_a_1888_; lean_object* v___y_1892_; uint8_t v___x_1894_; 
v_inheritedTraceOptions_1800_ = lean_ctor_get(v___y_1783_, 13);
v_hasTrace_1801_ = lean_ctor_get_uint8(v_options_1795_, sizeof(void*)*1);
v___x_1802_ = l_Lean_instInhabitedExpr;
v___x_1803_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__5));
v___x_1894_ = lean_bool_not(v_hasTrace_1801_);
if (v___x_1894_ == 0)
{
lean_object* v___f_1895_; uint8_t v___x_1896_; lean_object* v___x_1897_; uint8_t v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v_a_1902_; uint8_t v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v_a_1918_; uint8_t v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; uint8_t v___y_1927_; uint8_t v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v_a_1941_; uint8_t v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; uint8_t v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; uint8_t v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v_a_1969_; uint8_t v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v_a_1982_; uint8_t v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; uint8_t v___y_1989_; uint8_t v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v_a_2003_; uint8_t v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; uint8_t v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; uint8_t v___y_2028_; uint8_t v_a_2067_; 
v___f_1895_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__1));
v___x_1896_ = 1;
v___x_1897_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__6));
if (v_hasTrace_1801_ == 0)
{
v_a_2067_ = v_hasTrace_1801_;
goto v___jp_2066_;
}
else
{
lean_object* v___x_2088_; uint8_t v___x_2089_; 
v___x_2088_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10);
v___x_2089_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1800_, v_options_1795_, v___x_2088_);
if (v___x_2089_ == 0)
{
v_a_2067_ = v___x_2089_;
goto v___jp_2066_;
}
else
{
v___y_2028_ = v___x_2089_;
goto v___jp_2027_;
}
}
v___jp_1898_:
{
lean_object* v___x_1903_; double v___x_1904_; double v___x_1905_; double v___x_1906_; double v___x_1907_; double v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1903_ = lean_io_mono_nanos_now();
v___x_1904_ = lean_float_of_nat(v___y_1901_);
v___x_1905_ = lean_float_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__7);
v___x_1906_ = lean_float_div(v___x_1904_, v___x_1905_);
v___x_1907_ = lean_float_of_nat(v___x_1903_);
v___x_1908_ = lean_float_div(v___x_1907_, v___x_1905_);
v___x_1909_ = lean_box_float(v___x_1906_);
v___x_1910_ = lean_box_float(v___x_1908_);
v___x_1911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1909_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1912_, 0, v_a_1902_);
lean_ctor_set(v___x_1912_, 1, v___x_1911_);
v___x_1913_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_1803_, v___x_1896_, v___x_1897_, v_options_1795_, v___y_1899_, v___y_1900_, v___f_1895_, v___x_1912_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
return v___x_1913_;
}
v___jp_1914_:
{
lean_object* v___x_1920_; 
if (v_isShared_1799_ == 0)
{
lean_ctor_set_tag(v___x_1798_, 0);
lean_ctor_set(v___x_1798_, 0, v_a_1918_);
v___x_1920_ = v___x_1798_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1918_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
v___y_1899_ = v___y_1915_;
v___y_1900_ = v___y_1916_;
v___y_1901_ = v___y_1917_;
v_a_1902_ = v___x_1920_;
goto v___jp_1898_;
}
}
v___jp_1922_:
{
if (v___y_1927_ == 0)
{
lean_object* v___x_1928_; lean_object* v_a_1929_; uint8_t v___x_1930_; 
v___x_1928_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v___x_1803_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_a_1929_);
lean_dec_ref(v___x_1928_);
v___x_1930_ = lean_unbox(v_a_1929_);
lean_dec(v_a_1929_);
if (v___x_1930_ == 0)
{
v___y_1915_ = v___y_1923_;
v___y_1916_ = v___y_1924_;
v___y_1917_ = v___y_1926_;
v_a_1918_ = v___y_1925_;
goto v___jp_1914_;
}
else
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1931_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1);
lean_inc_ref(v___y_1925_);
v___x_1932_ = l_Lean_Exception_toMessageData(v___y_1925_);
v___x_1933_ = l_Lean_indentD(v___x_1932_);
v___x_1934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1931_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
v___x_1935_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1803_, v___x_1934_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_dec_ref_known(v___x_1935_, 1);
v___y_1915_ = v___y_1923_;
v___y_1916_ = v___y_1924_;
v___y_1917_ = v___y_1926_;
v_a_1918_ = v___y_1925_;
goto v___jp_1914_;
}
else
{
lean_object* v_a_1936_; 
lean_dec_ref(v___y_1925_);
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
lean_dec_ref_known(v___x_1935_, 1);
v___y_1915_ = v___y_1923_;
v___y_1916_ = v___y_1924_;
v___y_1917_ = v___y_1926_;
v_a_1918_ = v_a_1936_;
goto v___jp_1914_;
}
}
}
else
{
v___y_1915_ = v___y_1923_;
v___y_1916_ = v___y_1924_;
v___y_1917_ = v___y_1926_;
v_a_1918_ = v___y_1925_;
goto v___jp_1914_;
}
}
v___jp_1937_:
{
uint8_t v___x_1942_; 
v___x_1942_ = l_Lean_Exception_isInterrupt(v_a_1941_);
if (v___x_1942_ == 0)
{
uint8_t v___x_1943_; 
lean_inc_ref(v_a_1941_);
v___x_1943_ = l_Lean_Exception_isRuntime(v_a_1941_);
v___y_1923_ = v___y_1938_;
v___y_1924_ = v___y_1939_;
v___y_1925_ = v_a_1941_;
v___y_1926_ = v___y_1940_;
v___y_1927_ = v___x_1943_;
goto v___jp_1922_;
}
else
{
v___y_1923_ = v___y_1938_;
v___y_1924_ = v___y_1939_;
v___y_1925_ = v_a_1941_;
v___y_1926_ = v___y_1940_;
v___y_1927_ = v___x_1942_;
goto v___jp_1922_;
}
}
v___jp_1944_:
{
if (lean_obj_tag(v___y_1948_) == 0)
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
lean_del_object(v___x_1798_);
v_a_1949_ = lean_ctor_get(v___y_1948_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___y_1948_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___y_1948_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___y_1948_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
lean_ctor_set_tag(v___x_1951_, 1);
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
v___y_1899_ = v___y_1945_;
v___y_1900_ = v___y_1946_;
v___y_1901_ = v___y_1947_;
v_a_1902_ = v___x_1954_;
goto v___jp_1898_;
}
}
}
else
{
lean_object* v_a_1957_; 
v_a_1957_ = lean_ctor_get(v___y_1948_, 0);
lean_inc(v_a_1957_);
lean_dec_ref_known(v___y_1948_, 1);
v___y_1938_ = v___y_1945_;
v___y_1939_ = v___y_1946_;
v___y_1940_ = v___y_1947_;
v_a_1941_ = v_a_1957_;
goto v___jp_1937_;
}
}
v___jp_1958_:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1963_ = lean_box(0);
lean_inc(v___y_1784_);
lean_inc_ref(v___y_1783_);
lean_inc(v___y_1782_);
lean_inc_ref(v___y_1781_);
v___x_1964_ = lean_apply_6(v___y_1962_, v___x_1963_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, lean_box(0));
v___y_1945_ = v___y_1959_;
v___y_1946_ = v___y_1960_;
v___y_1947_ = v___y_1961_;
v___y_1948_ = v___x_1964_;
goto v___jp_1944_;
}
v___jp_1965_:
{
lean_object* v___x_1970_; double v___x_1971_; double v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1970_ = lean_io_get_num_heartbeats();
v___x_1971_ = lean_float_of_nat(v___y_1968_);
v___x_1972_ = lean_float_of_nat(v___x_1970_);
v___x_1973_ = lean_box_float(v___x_1971_);
v___x_1974_ = lean_box_float(v___x_1972_);
v___x_1975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1973_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
v___x_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1976_, 0, v_a_1969_);
lean_ctor_set(v___x_1976_, 1, v___x_1975_);
v___x_1977_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_reduceSparseCasesOn_spec__6(v___x_1803_, v___x_1896_, v___x_1897_, v_options_1795_, v___y_1966_, v___y_1967_, v___f_1895_, v___x_1976_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
return v___x_1977_;
}
v___jp_1978_:
{
lean_object* v___x_1983_; 
v___x_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1983_, 0, v_a_1982_);
v___y_1966_ = v___y_1979_;
v___y_1967_ = v___y_1980_;
v___y_1968_ = v___y_1981_;
v_a_1969_ = v___x_1983_;
goto v___jp_1965_;
}
v___jp_1984_:
{
if (v___y_1989_ == 0)
{
lean_object* v___x_1990_; lean_object* v_a_1991_; uint8_t v___x_1992_; 
v___x_1990_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v___x_1803_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_1991_);
lean_dec_ref(v___x_1990_);
v___x_1992_ = lean_unbox(v_a_1991_);
lean_dec(v_a_1991_);
if (v___x_1992_ == 0)
{
v___y_1979_ = v___y_1985_;
v___y_1980_ = v___y_1986_;
v___y_1981_ = v___y_1987_;
v_a_1982_ = v___y_1988_;
goto v___jp_1978_;
}
else
{
lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1993_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1);
lean_inc_ref(v___y_1988_);
v___x_1994_ = l_Lean_Exception_toMessageData(v___y_1988_);
v___x_1995_ = l_Lean_indentD(v___x_1994_);
v___x_1996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1993_);
lean_ctor_set(v___x_1996_, 1, v___x_1995_);
v___x_1997_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1803_, v___x_1996_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_dec_ref_known(v___x_1997_, 1);
v___y_1979_ = v___y_1985_;
v___y_1980_ = v___y_1986_;
v___y_1981_ = v___y_1987_;
v_a_1982_ = v___y_1988_;
goto v___jp_1978_;
}
else
{
lean_object* v_a_1998_; 
lean_dec_ref(v___y_1988_);
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_a_1998_);
lean_dec_ref_known(v___x_1997_, 1);
v___y_1979_ = v___y_1985_;
v___y_1980_ = v___y_1986_;
v___y_1981_ = v___y_1987_;
v_a_1982_ = v_a_1998_;
goto v___jp_1978_;
}
}
}
else
{
v___y_1979_ = v___y_1985_;
v___y_1980_ = v___y_1986_;
v___y_1981_ = v___y_1987_;
v_a_1982_ = v___y_1988_;
goto v___jp_1978_;
}
}
v___jp_1999_:
{
uint8_t v___x_2004_; 
v___x_2004_ = l_Lean_Exception_isInterrupt(v_a_2003_);
if (v___x_2004_ == 0)
{
uint8_t v___x_2005_; 
lean_inc_ref(v_a_2003_);
v___x_2005_ = l_Lean_Exception_isRuntime(v_a_2003_);
v___y_1985_ = v___y_2000_;
v___y_1986_ = v___y_2001_;
v___y_1987_ = v___y_2002_;
v___y_1988_ = v_a_2003_;
v___y_1989_ = v___x_2005_;
goto v___jp_1984_;
}
else
{
v___y_1985_ = v___y_2000_;
v___y_1986_ = v___y_2001_;
v___y_1987_ = v___y_2002_;
v___y_1988_ = v_a_2003_;
v___y_1989_ = v___x_2004_;
goto v___jp_1984_;
}
}
v___jp_2006_:
{
if (lean_obj_tag(v___y_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
v_a_2011_ = lean_ctor_get(v___y_2010_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___y_2010_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___y_2010_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___y_2010_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
lean_ctor_set_tag(v___x_2013_, 1);
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
v___y_1966_ = v___y_2007_;
v___y_1967_ = v___y_2008_;
v___y_1968_ = v___y_2009_;
v_a_1969_ = v___x_2016_;
goto v___jp_1965_;
}
}
}
else
{
lean_object* v_a_2019_; 
v_a_2019_ = lean_ctor_get(v___y_2010_, 0);
lean_inc(v_a_2019_);
lean_dec_ref_known(v___y_2010_, 1);
v___y_2000_ = v___y_2007_;
v___y_2001_ = v___y_2008_;
v___y_2002_ = v___y_2009_;
v_a_2003_ = v_a_2019_;
goto v___jp_1999_;
}
}
v___jp_2020_:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = lean_box(0);
lean_inc(v___y_1784_);
lean_inc_ref(v___y_1783_);
lean_inc(v___y_1782_);
lean_inc_ref(v___y_1781_);
v___x_2026_ = lean_apply_6(v___y_2023_, v___x_2025_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, lean_box(0));
v___y_2007_ = v___y_2021_;
v___y_2008_ = v___y_2022_;
v___y_2009_ = v___y_2024_;
v___y_2010_ = v___x_2026_;
goto v___jp_2006_;
}
v___jp_2027_:
{
lean_object* v___x_2029_; lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2065_; 
v___x_2029_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_reduceSparseCasesOn_spec__4___redArg(v___y_1784_);
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2032_ = v___x_2029_;
v_isShared_2033_ = v_isSharedCheck_2065_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2029_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2065_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2034_; uint8_t v___x_2035_; 
v___x_2034_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2035_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_options_1795_, v___x_2034_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___f_2038_; 
v___x_2036_ = lean_io_mono_nanos_now();
v___x_2037_ = lean_box(v___x_2035_);
lean_inc(v_declName_1792_);
lean_inc(v_mvarId_1777_);
lean_inc_ref(v_x_1779_);
lean_inc(v_val_1796_);
v___f_2038_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___boxed), 12, 6);
lean_closure_set(v___f_2038_, 0, v_val_1796_);
lean_closure_set(v___f_2038_, 1, v___x_1802_);
lean_closure_set(v___f_2038_, 2, v_x_1779_);
lean_closure_set(v___f_2038_, 3, v_mvarId_1777_);
lean_closure_set(v___f_2038_, 4, v___x_2037_);
lean_closure_set(v___f_2038_, 5, v_declName_1792_);
if (v_hasTrace_1801_ == 0)
{
lean_del_object(v___x_2032_);
lean_dec(v_val_1796_);
lean_dec(v_declName_1792_);
lean_dec_ref(v_x_1779_);
lean_dec(v_mvarId_1777_);
v___y_1959_ = v___y_2028_;
v___y_1960_ = v_a_2030_;
v___y_1961_ = v___x_2036_;
v___y_1962_ = v___f_2038_;
goto v___jp_1958_;
}
else
{
lean_object* v___x_2039_; uint8_t v___x_2040_; 
v___x_2039_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10);
v___x_2040_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1800_, v_options_1795_, v___x_2039_);
if (v___x_2040_ == 0)
{
lean_del_object(v___x_2032_);
lean_dec(v_val_1796_);
lean_dec(v_declName_1792_);
lean_dec_ref(v_x_1779_);
lean_dec(v_mvarId_1777_);
v___y_1959_ = v___y_2028_;
v___y_1960_ = v_a_2030_;
v___y_1961_ = v___x_2036_;
v___y_1962_ = v___f_2038_;
goto v___jp_1958_;
}
else
{
lean_object* v___x_2041_; lean_object* v___x_2043_; 
lean_dec_ref(v___f_2038_);
v___x_2041_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3);
lean_inc(v_mvarId_1777_);
if (v_isShared_2033_ == 0)
{
lean_ctor_set_tag(v___x_2032_, 1);
lean_ctor_set(v___x_2032_, 0, v_mvarId_1777_);
v___x_2043_ = v___x_2032_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_mvarId_1777_);
v___x_2043_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2041_);
lean_ctor_set(v___x_2044_, 1, v___x_2043_);
v___x_2045_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1803_, v___x_2044_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v___x_2047_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc(v_a_2046_);
lean_dec_ref_known(v___x_2045_, 1);
v___x_2047_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(v_val_1796_, v___x_1802_, v_x_1779_, v_mvarId_1777_, v___x_2035_, v_declName_1792_, v_a_2046_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
lean_dec_ref(v_x_1779_);
v___y_1945_ = v___y_2028_;
v___y_1946_ = v_a_2030_;
v___y_1947_ = v___x_2036_;
v___y_1948_ = v___x_2047_;
goto v___jp_1944_;
}
else
{
lean_object* v_a_2048_; 
lean_dec(v_val_1796_);
lean_dec(v_declName_1792_);
lean_dec_ref(v_x_1779_);
lean_dec(v_mvarId_1777_);
v_a_2048_ = lean_ctor_get(v___x_2045_, 0);
lean_inc(v_a_2048_);
lean_dec_ref_known(v___x_2045_, 1);
v___y_1938_ = v___y_2028_;
v___y_1939_ = v_a_2030_;
v___y_1940_ = v___x_2036_;
v_a_1941_ = v_a_2048_;
goto v___jp_1937_;
}
}
}
}
}
else
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___f_2053_; 
lean_del_object(v___x_1798_);
v___x_2050_ = lean_io_get_num_heartbeats();
v___x_2051_ = lean_box(v___x_1894_);
v___x_2052_ = lean_box(v___x_2035_);
lean_inc(v_declName_1792_);
lean_inc(v_mvarId_1777_);
lean_inc_ref(v_x_1779_);
lean_inc(v_val_1796_);
v___f_2053_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1___boxed), 13, 7);
lean_closure_set(v___f_2053_, 0, v_val_1796_);
lean_closure_set(v___f_2053_, 1, v___x_1802_);
lean_closure_set(v___f_2053_, 2, v_x_1779_);
lean_closure_set(v___f_2053_, 3, v_mvarId_1777_);
lean_closure_set(v___f_2053_, 4, v___x_2051_);
lean_closure_set(v___f_2053_, 5, v_declName_1792_);
lean_closure_set(v___f_2053_, 6, v___x_2052_);
if (v_hasTrace_1801_ == 0)
{
lean_del_object(v___x_2032_);
lean_dec(v_val_1796_);
lean_dec(v_declName_1792_);
lean_dec_ref(v_x_1779_);
lean_dec(v_mvarId_1777_);
v___y_2021_ = v___y_2028_;
v___y_2022_ = v_a_2030_;
v___y_2023_ = v___f_2053_;
v___y_2024_ = v___x_2050_;
goto v___jp_2020_;
}
else
{
lean_object* v___x_2054_; uint8_t v___x_2055_; 
v___x_2054_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10);
v___x_2055_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1800_, v_options_1795_, v___x_2054_);
if (v___x_2055_ == 0)
{
lean_del_object(v___x_2032_);
lean_dec(v_val_1796_);
lean_dec(v_declName_1792_);
lean_dec_ref(v_x_1779_);
lean_dec(v_mvarId_1777_);
v___y_2021_ = v___y_2028_;
v___y_2022_ = v_a_2030_;
v___y_2023_ = v___f_2053_;
v___y_2024_ = v___x_2050_;
goto v___jp_2020_;
}
else
{
lean_object* v___x_2056_; lean_object* v___x_2058_; 
lean_dec_ref(v___f_2053_);
v___x_2056_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3);
lean_inc(v_mvarId_1777_);
if (v_isShared_2033_ == 0)
{
lean_ctor_set_tag(v___x_2032_, 1);
lean_ctor_set(v___x_2032_, 0, v_mvarId_1777_);
v___x_2058_ = v___x_2032_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_mvarId_1777_);
v___x_2058_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2056_);
lean_ctor_set(v___x_2059_, 1, v___x_2058_);
v___x_2060_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1803_, v___x_2059_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2061_; lean_object* v___x_2062_; 
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_a_2061_);
lean_dec_ref_known(v___x_2060_, 1);
v___x_2062_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__1(v_val_1796_, v___x_1802_, v_x_1779_, v_mvarId_1777_, v___x_1894_, v_declName_1792_, v___x_2035_, v_a_2061_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
lean_dec_ref(v_x_1779_);
v___y_2007_ = v___y_2028_;
v___y_2008_ = v_a_2030_;
v___y_2009_ = v___x_2050_;
v___y_2010_ = v___x_2062_;
goto v___jp_2006_;
}
else
{
lean_object* v_a_2063_; 
lean_dec(v_val_1796_);
lean_dec(v_declName_1792_);
lean_dec_ref(v_x_1779_);
lean_dec(v_mvarId_1777_);
v_a_2063_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_a_2063_);
lean_dec_ref_known(v___x_2060_, 1);
v___y_2000_ = v___y_2028_;
v___y_2001_ = v_a_2030_;
v___y_2002_ = v___x_2050_;
v_a_2003_ = v_a_2063_;
goto v___jp_1999_;
}
}
}
}
}
}
}
v___jp_2066_:
{
lean_object* v___x_2068_; uint8_t v___x_2069_; 
v___x_2068_ = l_Lean_trace_profiler;
v___x_2069_ = l_Lean_Option_get___at___00Lean_Meta_reduceSparseCasesOn_spec__5(v_options_1795_, v___x_2068_);
if (v___x_2069_ == 0)
{
lean_object* v___x_2070_; lean_object* v___f_2071_; 
lean_del_object(v___x_1798_);
v___x_2070_ = lean_box(v___x_2069_);
lean_inc(v_declName_1792_);
lean_inc(v_mvarId_1777_);
lean_inc_ref(v_x_1779_);
lean_inc(v_val_1796_);
v___f_2071_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2___boxed), 12, 6);
lean_closure_set(v___f_2071_, 0, v_val_1796_);
lean_closure_set(v___f_2071_, 1, v___x_1802_);
lean_closure_set(v___f_2071_, 2, v_x_1779_);
lean_closure_set(v___f_2071_, 3, v_mvarId_1777_);
lean_closure_set(v___f_2071_, 4, v___x_2070_);
lean_closure_set(v___f_2071_, 5, v_declName_1792_);
if (v_hasTrace_1801_ == 0)
{
lean_dec(v_val_1796_);
lean_dec(v_declName_1792_);
lean_dec_ref(v_x_1779_);
lean_dec(v_mvarId_1777_);
v___y_1848_ = v___f_2071_;
goto v___jp_1847_;
}
else
{
lean_object* v___x_2072_; uint8_t v___x_2073_; 
v___x_2072_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10);
v___x_2073_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1800_, v_options_1795_, v___x_2072_);
if (v___x_2073_ == 0)
{
lean_dec(v_val_1796_);
lean_dec(v_declName_1792_);
lean_dec_ref(v_x_1779_);
lean_dec(v_mvarId_1777_);
v___y_1848_ = v___f_2071_;
goto v___jp_1847_;
}
else
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
lean_dec_ref(v___f_2071_);
v___x_2074_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3);
lean_inc(v_mvarId_1777_);
v___x_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2075_, 0, v_mvarId_1777_);
v___x_2076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2074_);
lean_ctor_set(v___x_2076_, 1, v___x_2075_);
v___x_2077_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1803_, v___x_2076_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; lean_object* v___x_2079_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_a_2078_);
lean_dec_ref_known(v___x_2077_, 1);
v___x_2079_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__2(v_val_1796_, v___x_1802_, v_x_1779_, v_mvarId_1777_, v___x_2069_, v_declName_1792_, v_a_2078_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
lean_dec_ref(v_x_1779_);
v___y_1845_ = v___x_2079_;
goto v___jp_1844_;
}
else
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
lean_dec(v_val_1796_);
lean_dec(v_declName_1792_);
lean_dec_ref(v_x_1779_);
lean_dec(v_mvarId_1777_);
v_a_2080_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2077_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2077_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
lean_inc(v_a_2080_);
if (v_isShared_2083_ == 0)
{
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2080_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
v___y_1840_ = v___x_2085_;
v_a_1841_ = v_a_2080_;
goto v___jp_1839_;
}
}
}
}
}
}
else
{
v___y_2028_ = v_a_2067_;
goto v___jp_2027_;
}
}
}
else
{
if (v_hasTrace_1801_ == 0)
{
lean_del_object(v___x_1798_);
goto v___jp_2090_;
}
else
{
lean_object* v___x_2093_; uint8_t v___x_2094_; 
v___x_2093_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__10);
v___x_2094_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1800_, v_options_1795_, v___x_2093_);
if (v___x_2094_ == 0)
{
lean_del_object(v___x_1798_);
goto v___jp_2090_;
}
else
{
lean_object* v___x_2095_; lean_object* v___x_2097_; 
v___x_2095_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__3);
lean_inc(v_mvarId_1777_);
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 0, v_mvarId_1777_);
v___x_2097_ = v___x_1798_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_mvarId_1777_);
v___x_2097_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2095_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
v___x_2099_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1803_, v___x_2098_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v___x_2101_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2100_);
lean_dec_ref_known(v___x_2099_, 1);
v___x_2101_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__4(v_val_1796_, v___x_1802_, v_x_1779_, v_mvarId_1777_, v_declName_1792_, v___x_1894_, v_a_2100_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
lean_dec_ref(v_x_1779_);
v___y_1892_ = v___x_2101_;
goto v___jp_1891_;
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
lean_dec(v_val_1796_);
lean_dec(v_declName_1792_);
lean_dec_ref(v_x_1779_);
lean_dec(v_mvarId_1777_);
v_a_2102_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v___x_2099_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2099_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
lean_inc(v_a_2102_);
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
v___y_1887_ = v___x_2107_;
v_a_1888_ = v_a_2102_;
goto v___jp_1886_;
}
}
}
}
}
}
v___jp_2090_:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = lean_box(0);
v___x_2092_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__4(v_val_1796_, v___x_1802_, v_x_1779_, v_mvarId_1777_, v_declName_1792_, v___x_1894_, v___x_2091_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
lean_dec_ref(v_x_1779_);
v___y_1892_ = v___x_2092_;
goto v___jp_1891_;
}
}
v___jp_1804_:
{
if (v___y_1807_ == 0)
{
lean_object* v___x_1808_; lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1838_; 
lean_dec_ref(v___y_1805_);
v___x_1808_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v___x_1803_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1811_ = v___x_1808_;
v_isShared_1812_ = v_isSharedCheck_1838_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1808_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1838_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
uint8_t v___x_1813_; 
v___x_1813_ = lean_unbox(v_a_1809_);
lean_dec(v_a_1809_);
if (v___x_1813_ == 0)
{
lean_object* v___x_1815_; 
if (v_isShared_1812_ == 0)
{
lean_ctor_set_tag(v___x_1811_, 1);
lean_ctor_set(v___x_1811_, 0, v___y_1806_);
v___x_1815_ = v___x_1811_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___y_1806_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
else
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
lean_del_object(v___x_1811_);
v___x_1817_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1);
lean_inc_ref(v___y_1806_);
v___x_1818_ = l_Lean_Exception_toMessageData(v___y_1806_);
v___x_1819_ = l_Lean_indentD(v___x_1818_);
v___x_1820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1817_);
lean_ctor_set(v___x_1820_, 1, v___x_1819_);
v___x_1821_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1803_, v___x_1820_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1828_ == 0)
{
lean_object* v_unused_1829_; 
v_unused_1829_ = lean_ctor_get(v___x_1821_, 0);
lean_dec(v_unused_1829_);
v___x_1823_ = v___x_1821_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_dec(v___x_1821_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
lean_ctor_set_tag(v___x_1823_, 1);
lean_ctor_set(v___x_1823_, 0, v___y_1806_);
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___y_1806_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
else
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1837_; 
lean_dec_ref(v___y_1806_);
v_a_1830_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1832_ = v___x_1821_;
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1821_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
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
return v___x_1835_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_1806_);
return v___y_1805_;
}
}
v___jp_1839_:
{
uint8_t v___x_1842_; 
v___x_1842_ = l_Lean_Exception_isInterrupt(v_a_1841_);
if (v___x_1842_ == 0)
{
uint8_t v___x_1843_; 
lean_inc_ref(v_a_1841_);
v___x_1843_ = l_Lean_Exception_isRuntime(v_a_1841_);
v___y_1805_ = v___y_1840_;
v___y_1806_ = v_a_1841_;
v___y_1807_ = v___x_1843_;
goto v___jp_1804_;
}
else
{
v___y_1805_ = v___y_1840_;
v___y_1806_ = v_a_1841_;
v___y_1807_ = v___x_1842_;
goto v___jp_1804_;
}
}
v___jp_1844_:
{
if (lean_obj_tag(v___y_1845_) == 0)
{
return v___y_1845_;
}
else
{
lean_object* v_a_1846_; 
v_a_1846_ = lean_ctor_get(v___y_1845_, 0);
lean_inc(v_a_1846_);
v___y_1840_ = v___y_1845_;
v_a_1841_ = v_a_1846_;
goto v___jp_1839_;
}
}
v___jp_1847_:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1849_ = lean_box(0);
lean_inc(v___y_1784_);
lean_inc_ref(v___y_1783_);
lean_inc(v___y_1782_);
lean_inc_ref(v___y_1781_);
v___x_1850_ = lean_apply_6(v___y_1848_, v___x_1849_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, lean_box(0));
v___y_1845_ = v___x_1850_;
goto v___jp_1844_;
}
v___jp_1851_:
{
if (v___y_1854_ == 0)
{
lean_object* v___x_1855_; lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1885_; 
lean_dec_ref(v___y_1853_);
v___x_1855_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___lam__0(v___x_1803_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
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
v___x_1864_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___closed__1);
lean_inc_ref(v___y_1852_);
v___x_1865_ = l_Lean_Exception_toMessageData(v___y_1852_);
v___x_1866_ = l_Lean_indentD(v___x_1865_);
v___x_1867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1864_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
v___x_1868_ = l_Lean_addTrace___at___00Lean_Meta_splitSparseCasesOn_spec__0(v___x_1803_, v___x_1867_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
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
}
}
else
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
lean_dec(v_a_1794_);
lean_dec(v_declName_1792_);
lean_dec_ref(v_x_1779_);
lean_dec(v_mvarId_1777_);
v___x_2112_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__12);
v___x_2113_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_2112_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
return v___x_2113_;
}
}
else
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
lean_dec(v_declName_1792_);
lean_dec_ref(v_x_1779_);
lean_dec(v_mvarId_1777_);
v_a_2114_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_1793_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_1793_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2114_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
else
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
lean_dec_ref(v_x_1779_);
lean_dec_ref(v_x_1778_);
lean_dec(v_mvarId_1777_);
v___x_2122_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___closed__14);
v___x_2123_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_2122_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
return v___x_2123_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6___boxed(lean_object* v_mvarId_2124_, lean_object* v_x_2125_, lean_object* v_x_2126_, lean_object* v_x_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6(v_mvarId_2124_, v_x_2125_, v_x_2126_, v_x_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitSparseCasesOn(lean_object* v_mvarId_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_){
_start:
{
lean_object* v___x_2140_; 
lean_inc(v_mvarId_2134_);
v___x_2140_ = l_Lean_MVarId_getType(v_mvarId_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; lean_object* v___x_2142_; 
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_a_2141_);
lean_dec_ref_known(v___x_2140_, 1);
v___x_2142_ = l_Lean_Meta_matchEqHEqLHS_x3f(v_a_2141_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2143_);
lean_dec_ref_known(v___x_2142_, 1);
if (lean_obj_tag(v_a_2143_) == 1)
{
lean_object* v_val_2144_; lean_object* v_snd_2145_; lean_object* v_dummy_2146_; lean_object* v_nargs_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v_val_2144_ = lean_ctor_get(v_a_2143_, 0);
lean_inc(v_val_2144_);
lean_dec_ref_known(v_a_2143_, 1);
v_snd_2145_ = lean_ctor_get(v_val_2144_, 1);
lean_inc(v_snd_2145_);
lean_dec(v_val_2144_);
v_dummy_2146_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_reduceSparseCasesOn_spec__7___lam__0___closed__0);
v_nargs_2147_ = l_Lean_Expr_getAppNumArgs(v_snd_2145_);
lean_inc(v_nargs_2147_);
v___x_2148_ = lean_mk_array(v_nargs_2147_, v_dummy_2146_);
v___x_2149_ = lean_unsigned_to_nat(1u);
v___x_2150_ = lean_nat_sub(v_nargs_2147_, v___x_2149_);
lean_dec(v_nargs_2147_);
v___x_2151_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_splitSparseCasesOn_spec__6(v_mvarId_2134_, v_snd_2145_, v___x_2148_, v___x_2150_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_);
return v___x_2151_;
}
else
{
lean_object* v___x_2152_; lean_object* v___x_2153_; 
lean_dec(v_a_2143_);
lean_dec(v_mvarId_2134_);
v___x_2152_ = lean_obj_once(&l_Lean_Meta_reduceSparseCasesOn___closed__1, &l_Lean_Meta_reduceSparseCasesOn___closed__1_once, _init_l_Lean_Meta_reduceSparseCasesOn___closed__1);
v___x_2153_ = l_Lean_throwError___at___00Lean_Meta_reduceSparseCasesOn_spec__3___redArg(v___x_2152_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_);
return v___x_2153_;
}
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_dec(v_mvarId_2134_);
v_a_2154_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2142_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2142_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_dec(v_mvarId_2134_);
v_a_2162_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2140_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2140_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitSparseCasesOn___boxed(lean_object* v_mvarId_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l_Lean_Meta_splitSparseCasesOn(v_mvarId_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_);
lean_dec(v_a_2174_);
lean_dec_ref(v_a_2173_);
lean_dec(v_a_2172_);
lean_dec_ref(v_a_2171_);
return v_res_2176_;
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
