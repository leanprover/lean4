// Lean compiler output
// Module: Lean.Meta.SizeOf
// Imports: public import Lean.AddDecl public import Lean.Meta.AppBuilder public import Lean.DefEqAttrib import Lean.Meta.WHNF
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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRecName(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
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
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfI(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_natAdd_x3f(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_RecursorVal_getFirstIndexIdx(lean_object*);
lean_object* l_Lean_RecursorVal_getMajorIdx(lean_object*);
lean_object* l_List_tail_x21___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withInstImplicitAsImplicit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNumeral(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
uint8_t l_Lean_Expr_isArrow(lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_inferDefEqAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_InductiveVal_isNested(lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_RecursorVal_getFirstMinorIdx(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_registerInstance(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_getAttributeImpl(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_isPrivateName___boxed(lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__0___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "SizeOf"};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 190, 244, 45, 165, 196, 61, 198)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "inst"};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(170, 188, 240, 205, 110, 63, 170, 91)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_isInductiveHypothesis_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_isInductiveHypothesis_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_isInductiveHypothesis_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_isInductiveHypothesis_x3f_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_isInductiveHypothesis_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_isInductiveHypothesis_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_isInductiveHypothesis_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_isInductiveHypothesis_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_isInductiveHypothesis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_isInductiveHypothesis___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_isRecField_x3f_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_isRecField_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_isRecField_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_isRecField_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_isRecField_x3f___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_isRecField_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_isRecField_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___lam__0___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "sizeOf"};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(157, 123, 61, 199, 19, 54, 20, 234)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "motive: "};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_ignoreFieldType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Unit"};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_ignoreFieldType___closed__0 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_ignoreFieldType___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_ignoreFieldType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_ignoreFieldType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_ignoreFieldType___closed__1 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_ignoreFieldType___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_ignoreFieldType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_ignoreFieldType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_ignoreField(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_ignoreField___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfRecFieldFormIH___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "unit"};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfRecFieldFormIH___closed__0 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfRecFieldFormIH___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfRecFieldFormIH___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_ignoreFieldType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfRecFieldFormIH___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfRecFieldFormIH___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfRecFieldFormIH___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 186, 243, 194, 96, 12, 218, 7)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfRecFieldFormIH___closed__1 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfRecFieldFormIH___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfRecFieldFormIH___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfRecFieldFormIH___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfRecFieldFormIH(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfRecFieldFormIH___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop_spec__0___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 190, 244, 45, 165, 196, 61, 198)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop_spec__0___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(151, 205, 72, 249, 57, 72, 20, 171)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "minor: "};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop___redArg___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_spec__0___redArg___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Lean.Meta.SizeOf"};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "_private.Lean.Meta.SizeOf.0.Lean.Meta.mkSizeOfMinors"};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "assertion violation: minorFVars.size == minorFVars'.size\n  "};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___closed__2;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFn___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFn___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkSizeOfFn___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "val: "};
static const lean_object* l_Lean_Meta_mkSizeOfFn___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_mkSizeOfFn___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_mkSizeOfFn___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSizeOfFn___lam__1___closed__1;
static const lean_string_object l_Lean_Meta_mkSizeOfFn___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "type: "};
static const lean_object* l_Lean_Meta_mkSizeOfFn___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_mkSizeOfFn___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Meta_mkSizeOfFn___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSizeOfFn___lam__1___closed__3;
static const lean_string_object l_Lean_Meta_mkSizeOfFn___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "declName: "};
static const lean_object* l_Lean_Meta_mkSizeOfFn___lam__1___closed__4 = (const lean_object*)&l_Lean_Meta_mkSizeOfFn___lam__1___closed__4_value;
static lean_once_cell_t l_Lean_Meta_mkSizeOfFn___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSizeOfFn___lam__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFn___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFn___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFn___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFn___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFn___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFn___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_mkSizeOfFn_spec__1(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_mkSizeOfFn___lam__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSizeOfFn___lam__4___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFn___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFn___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFn___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFn___lam__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFn___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFn___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__1;
static const lean_string_object l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "` is not a recursor"};
static const lean_object* l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__2 = (const lean_object*)&l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__3;
static const lean_string_object l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__4 = (const lean_object*)&l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__4_value;
static const lean_string_object l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Lean.isRec\?"};
static const lean_object* l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__5 = (const lean_object*)&l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__5_value;
static const lean_string_object l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__6 = (const lean_object*)&l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkSizeOfFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "recName: "};
static const lean_object* l_Lean_Meta_mkSizeOfFn___closed__0 = (const lean_object*)&l_Lean_Meta_mkSizeOfFn___closed__0_value;
static lean_once_cell_t l_Lean_Meta_mkSizeOfFn___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSizeOfFn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkSizeOfFns_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkSizeOfFns_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfFns_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfFns_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSizeOfFns_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is not an inductive type"};
static const lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSizeOfFns_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSizeOfFns_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSizeOfFns_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSizeOfFns_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSizeOfFns_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSizeOfFns_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_mkSizeOfFns___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_mkSizeOfFns___closed__0 = (const lean_object*)&l_Lean_Meta_mkSizeOfFns___closed__0_value;
static const lean_string_object l_Lean_Meta_mkSizeOfFns___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_sizeOf"};
static const lean_object* l_Lean_Meta_mkSizeOfFns___closed__1 = (const lean_object*)&l_Lean_Meta_mkSizeOfFns___closed__1_value;
static const lean_ctor_object l_Lean_Meta_mkSizeOfFns___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkSizeOfFns___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 95, 129, 124, 156, 242, 61, 104)}};
static const lean_object* l_Lean_Meta_mkSizeOfFns___closed__2 = (const lean_object*)&l_Lean_Meta_mkSizeOfFns___closed__2_value;
static const lean_ctor_object l_Lean_Meta_mkSizeOfFns___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_mkSizeOfFns___closed__3 = (const lean_object*)&l_Lean_Meta_mkSizeOfFns___closed__3_value;
static const lean_ctor_object l_Lean_Meta_mkSizeOfFns___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_mkSizeOfFns___closed__0_value),((lean_object*)&l_Lean_Meta_mkSizeOfFns___closed__3_value)}};
static const lean_object* l_Lean_Meta_mkSizeOfFns___closed__4 = (const lean_object*)&l_Lean_Meta_mkSizeOfFns___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFns___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfFns_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfFns_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkSizeOfFns_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkSizeOfFns_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkSizeOfSpecLemmaName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "sizeOf_spec"};
static const lean_object* l_Lean_Meta_mkSizeOfSpecLemmaName___closed__0 = (const lean_object*)&l_Lean_Meta_mkSizeOfSpecLemmaName___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkSizeOfSpecLemmaName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkSizeOfSpecLemmaName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(26, 156, 136, 91, 46, 126, 16, 102)}};
static const lean_object* l_Lean_Meta_mkSizeOfSpecLemmaName___closed__1 = (const lean_object*)&l_Lean_Meta_mkSizeOfSpecLemmaName___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfSpecLemmaName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfSpecLemmaInstance___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfSpecLemmaInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "failed to apply 'sizeOf' spec, constructor expected"};
static const lean_object* l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__0 = (const lean_object*)&l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__0_value;
static lean_once_cell_t l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__1;
static const lean_closure_object l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_mkSizeOfSpecLemmaInstance___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__2 = (const lean_object*)&l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__2_value;
static lean_once_cell_t l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfSpecLemmaInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfSpecLemmaInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SizeOfSpecNested_throwUnexpected_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SizeOfSpecNested_throwUnexpected_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_SizeOfSpecNested_throwUnexpected___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "failed to generate sizeOf theorem for "};
static const lean_object* l_Lean_Meta_SizeOfSpecNested_throwUnexpected___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_SizeOfSpecNested_throwUnexpected___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_SizeOfSpecNested_throwUnexpected___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SizeOfSpecNested_throwUnexpected___redArg___closed__1;
static const lean_string_object l_Lean_Meta_SizeOfSpecNested_throwUnexpected___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = " (use `set_option genSizeOfSpec false` to disable theorem generation), "};
static const lean_object* l_Lean_Meta_SizeOfSpecNested_throwUnexpected___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_SizeOfSpecNested_throwUnexpected___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_SizeOfSpecNested_throwUnexpected___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SizeOfSpecNested_throwUnexpected___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_SizeOfSpecNested_throwUnexpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SizeOfSpecNested_throwUnexpected___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SizeOfSpecNested_throwUnexpected(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SizeOfSpecNested_throwUnexpected___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SizeOfSpecNested_throwUnexpected_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SizeOfSpecNested_throwUnexpected_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_SizeOfSpecNested_throwFailed___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = ", (use `set_option genSizeOfSpec false` to disable theorem generation)"};
static const lean_object* l_Lean_Meta_SizeOfSpecNested_throwFailed___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_SizeOfSpecNested_throwFailed___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_SizeOfSpecNested_throwFailed___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SizeOfSpecNested_throwFailed___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SizeOfSpecNested_throwFailed___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SizeOfSpecNested_throwFailed___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SizeOfSpecNested_throwFailed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SizeOfSpecNested_throwFailed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_recToSizeOf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "expected recursor application "};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_recToSizeOf___closed__0 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_recToSizeOf___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_recToSizeOf___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_recToSizeOf___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_recToSizeOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_recToSizeOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_mkSizeOf_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_mkSizeOf_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_mkSizeOf_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_mkSizeOf_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_mkSizeOf_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_mkSizeOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_mkSizeOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_mkSizeOf_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_mkSizeOf_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__10_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__10_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__13___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__11___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__11___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__7___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__11(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__6_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__6_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__6_spec__6___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__6_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___lam__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof___lam__1___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof___lam__1___boxed__const__1 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof___lam__1___boxed__const__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__12___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__12___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__12___lam__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__12___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__12___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__12___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__12___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "expected 'Nat.add' application, lhs is "};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__0 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__1;
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "\nrhs is"};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__2 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__3;
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "_eq"};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___closed__0 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___lam__1___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "aux"};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___closed__1 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(157, 123, 61, 199, 19, 54, 20, 234)}};
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___closed__1_value),LEAN_SCALAR_PTR_LITERAL(132, 105, 157, 86, 24, 108, 63, 49)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___closed__2 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___closed__2_value;
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " =\?= "};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__3 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "step"};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__1 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__1_value;
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "minor"};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__0 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(157, 123, 61, 199, 19, 54, 20, 234)}};
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__0_value),LEAN_SCALAR_PTR_LITERAL(222, 92, 77, 13, 196, 27, 121, 90)}};
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__1_value),LEAN_SCALAR_PTR_LITERAL(222, 19, 48, 48, 239, 244, 202, 92)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__2 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__4 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__4_value),LEAN_SCALAR_PTR_LITERAL(210, 189, 86, 121, 130, 22, 242, 236)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__5 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__6;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(157, 123, 61, 199, 19, 54, 20, 234)}};
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__0_value),LEAN_SCALAR_PTR_LITERAL(222, 92, 77, 13, 196, 27, 121, 90)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__7 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__12___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__12___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__12(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof___lam__0(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "thmValue: "};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__7(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__6_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__6_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_main_step(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_main_step___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_main_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "loop"};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_main_loop___closed__0 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_main_loop___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_main_loop___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_main_loop___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_main_loop___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(157, 123, 61, 199, 19, 54, 20, 234)}};
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_main_loop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_main_loop___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_main_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(173, 185, 67, 169, 161, 115, 178, 199)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_main_loop___closed__1 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_main_loop___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_main_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_main_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SizeOfSpecNested_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SizeOfSpecNested_main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "type mismatch"};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__1;
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "sizeOf spec theorem value: "};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__3;
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "sizeOf spec theorem type: "};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__5;
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "sizeOf spec theorem name: "};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__7;
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "_sizeOf_inst"};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(90, 161, 26, 192, 108, 87, 142, 145)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__9_value;
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ctor: "};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__10 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__11;
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = ", target: "};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__12 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__12_value;
static lean_once_cell_t l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__13;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__0___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__0___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 61, 75, 186, 44, 210, 52, 194)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__1_value;
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__3 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__3_value;
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__4 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__4_value;
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__5 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__5_value;
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__6 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__6_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(11, 96, 164, 147, 27, 132, 207, 84)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__7 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__7_value;
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__8 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__9 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__9_value;
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindMod"};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__10 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__6_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__10_value),LEAN_SCALAR_PTR_LITERAL(166, 252, 83, 80, 136, 168, 19, 119)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__11 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__11_value;
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "grindEq"};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__12 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__6_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__12_value),LEAN_SCALAR_PTR_LITERAL(179, 34, 219, 24, 240, 38, 65, 204)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__13 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__13_value;
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "="};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__14 = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__15;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorems_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorems_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorems_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorems_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorems_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "genSizeOf"};
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(219, 41, 231, 171, 40, 215, 128, 53)}};
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "generate `SizeOf` instance for inductive types and structures"};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(142, 3, 54, 82, 25, 122, 33, 63)}};
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_genSizeOf;
static const lean_string_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_SizeOf_3847602515____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "genSizeOfSpec"};
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_SizeOf_3847602515____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_SizeOf_3847602515____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_SizeOf_3847602515____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_SizeOf_3847602515____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(92, 60, 10, 78, 174, 36, 49, 227)}};
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_SizeOf_3847602515____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_SizeOf_3847602515____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_SizeOf_3847602515____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "generate `SizeOf` specification theorems for automatically generated instances"};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_SizeOf_3847602515____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_SizeOf_3847602515____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_SizeOf_3847602515____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_SizeOf_3847602515____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_SizeOf_3847602515____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_SizeOf_3847602515____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_SizeOf_3847602515____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_SizeOf_3847602515____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_SizeOf_3847602515____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_SizeOf_3847602515____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_SizeOf_3847602515____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_SizeOf_3847602515____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(185, 30, 68, 23, 199, 116, 0, 249)}};
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_SizeOf_3847602515____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_SizeOf_3847602515____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_SizeOf_3847602515____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_SizeOf_3847602515____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_genSizeOfSpec;
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_mkSizeOfInstances_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_mkSizeOfInstances_spec__1___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_mkSizeOfInstances_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_mkSizeOfInstances_spec__4___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_mkSizeOfInstances_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_mkSizeOfInstances_spec__4___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_mkSizeOfInstances_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_mkSizeOfInstances_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_mkSizeOfInstances_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_mkSizeOfInstances_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfInstances___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfInstances___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfInstances___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSizeOfInstances_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSizeOfInstances_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__1___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__1___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = ">> "};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__1___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__1___closed__1_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__1___closed__2;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__1___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__1___closed__3_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__1___closed__4;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__1___boxed(lean_object**);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "m"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__2___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(165, 239, 73, 172, 230, 126, 139, 134)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__2___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfInstances___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfInstances___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__6_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__5___boxed(lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5___closed__1;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5___closed__2 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5___closed__2_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5___closed__3;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_mkSizeOfInstances___lam__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_mkSizeOfInstances___lam__3___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfInstances___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfInstances___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkSizeOfInstances_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkSizeOfInstances_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_mkSizeOfInstances___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_isPrivateName___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_mkSizeOfInstances___lam__4___closed__0 = (const lean_object*)&l_Lean_Meta_mkSizeOfInstances___lam__4___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfInstances___lam__4(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfInstances___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkSizeOfInstances___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "failed to generate `SizeOf` instance for `"};
static const lean_object* l_Lean_Meta_mkSizeOfInstances___closed__0 = (const lean_object*)&l_Lean_Meta_mkSizeOfInstances___closed__0_value;
static lean_once_cell_t l_Lean_Meta_mkSizeOfInstances___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSizeOfInstances___closed__1;
static const lean_string_object l_Lean_Meta_mkSizeOfInstances___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`:"};
static const lean_object* l_Lean_Meta_mkSizeOfInstances___closed__2 = (const lean_object*)&l_Lean_Meta_mkSizeOfInstances___closed__2_value;
static lean_once_cell_t l_Lean_Meta_mkSizeOfInstances___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSizeOfInstances___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfInstances___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkSizeOfInstances_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkSizeOfInstances_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSizeOfInstances_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSizeOfInstances_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 71, 184, 17, 85, 89, 154, 165)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(177, 31, 187, 153, 217, 60, 89, 246)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(116, 46, 169, 158, 189, 224, 40, 136)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(168, 32, 72, 114, 221, 190, 164, 184)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(69, 143, 37, 4, 35, 187, 44, 37)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(56, 137, 6, 66, 249, 114, 250, 138)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(49, 76, 1, 171, 92, 81, 80, 149)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(209, 31, 127, 209, 92, 172, 230, 128)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 233, 92, 237, 107, 220, 9, 22)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value),((lean_object*)(((size_t)(726572898) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(181, 120, 32, 188, 173, 212, 161, 114)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(38, 148, 73, 236, 17, 172, 177, 89)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 61, 171, 157, 156, 200, 15, 24)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(67, 117, 193, 80, 251, 192, 189, 227)}};
static const lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__0___redArg___lam__0(lean_object* v_k_1_, lean_object* v_b_2_, lean_object* v_c_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
_start:
{
lean_object* v___x_9_; 
lean_inc(v___y_7_);
lean_inc_ref(v___y_6_);
lean_inc(v___y_5_);
lean_inc_ref(v___y_4_);
v___x_9_ = lean_apply_7(v_k_1_, v_b_2_, v_c_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, lean_box(0));
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__0___redArg___lam__0___boxed(lean_object* v_k_10_, lean_object* v_b_11_, lean_object* v_c_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__0___redArg___lam__0(v_k_10_, v_b_11_, v_c_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__0___redArg(lean_object* v_type_19_, lean_object* v_k_20_, uint8_t v_cleanupAnnotations_21_, uint8_t v_whnfType_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_){
_start:
{
lean_object* v___f_28_; lean_object* v___x_29_; 
v___f_28_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_28_, 0, v_k_20_);
v___x_29_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_19_, v___f_28_, v_cleanupAnnotations_21_, v_whnfType_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
if (lean_obj_tag(v___x_29_) == 0)
{
lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_37_; 
v_a_30_ = lean_ctor_get(v___x_29_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_37_ == 0)
{
v___x_32_ = v___x_29_;
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_dec(v___x_29_);
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
v_reuseFailAlloc_36_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_45_; 
v_a_38_ = lean_ctor_get(v___x_29_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_45_ == 0)
{
v___x_40_ = v___x_29_;
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_a_38_);
lean_dec(v___x_29_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_43_; 
if (v_isShared_41_ == 0)
{
v___x_43_ = v___x_40_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_a_38_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__0___redArg___boxed(lean_object* v_type_46_, lean_object* v_k_47_, lean_object* v_cleanupAnnotations_48_, lean_object* v_whnfType_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_55_; uint8_t v_whnfType_boxed_56_; lean_object* v_res_57_; 
v_cleanupAnnotations_boxed_55_ = lean_unbox(v_cleanupAnnotations_48_);
v_whnfType_boxed_56_ = lean_unbox(v_whnfType_49_);
v_res_57_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__0___redArg(v_type_46_, v_k_47_, v_cleanupAnnotations_boxed_55_, v_whnfType_boxed_56_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__0(lean_object* v_00_u03b1_58_, lean_object* v_type_59_, lean_object* v_k_60_, uint8_t v_cleanupAnnotations_61_, uint8_t v_whnfType_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__0___redArg(v_type_59_, v_k_60_, v_cleanupAnnotations_61_, v_whnfType_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__0___boxed(lean_object* v_00_u03b1_69_, lean_object* v_type_70_, lean_object* v_k_71_, lean_object* v_cleanupAnnotations_72_, lean_object* v_whnfType_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_79_; uint8_t v_whnfType_boxed_80_; lean_object* v_res_81_; 
v_cleanupAnnotations_boxed_79_ = lean_unbox(v_cleanupAnnotations_72_);
v_whnfType_boxed_80_ = lean_unbox(v_whnfType_73_);
v_res_81_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__0(v_00_u03b1_69_, v_type_70_, v_k_71_, v_cleanupAnnotations_boxed_79_, v_whnfType_boxed_80_, v___y_74_, v___y_75_, v___y_76_, v___y_77_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__1___redArg___lam__0(lean_object* v_k_82_, lean_object* v_b_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v___x_89_; 
lean_inc(v___y_87_);
lean_inc_ref(v___y_86_);
lean_inc(v___y_85_);
lean_inc_ref(v___y_84_);
v___x_89_ = lean_apply_6(v_k_82_, v_b_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, lean_box(0));
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__1___redArg___lam__0___boxed(lean_object* v_k_90_, lean_object* v_b_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__1___redArg___lam__0(v_k_90_, v_b_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__1___redArg(lean_object* v_name_98_, uint8_t v_bi_99_, lean_object* v_type_100_, lean_object* v_k_101_, uint8_t v_kind_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v___f_108_; lean_object* v___x_109_; 
v___f_108_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__1___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_108_, 0, v_k_101_);
v___x_109_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_98_, v_bi_99_, v_type_100_, v___f_108_, v_kind_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_117_; 
v_a_110_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_117_ == 0)
{
v___x_112_ = v___x_109_;
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_109_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_115_; 
if (v_isShared_113_ == 0)
{
v___x_115_ = v___x_112_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_a_110_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
else
{
lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_125_; 
v_a_118_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_125_ == 0)
{
v___x_120_ = v___x_109_;
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___x_109_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_123_; 
if (v_isShared_121_ == 0)
{
v___x_123_ = v___x_120_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_a_118_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__1___redArg___boxed(lean_object* v_name_126_, lean_object* v_bi_127_, lean_object* v_type_128_, lean_object* v_k_129_, lean_object* v_kind_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
uint8_t v_bi_boxed_136_; uint8_t v_kind_boxed_137_; lean_object* v_res_138_; 
v_bi_boxed_136_ = lean_unbox(v_bi_127_);
v_kind_boxed_137_ = lean_unbox(v_kind_130_);
v_res_138_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__1___redArg(v_name_126_, v_bi_boxed_136_, v_type_128_, v_k_129_, v_kind_boxed_137_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__1(lean_object* v_00_u03b1_139_, lean_object* v_name_140_, uint8_t v_bi_141_, lean_object* v_type_142_, lean_object* v_k_143_, uint8_t v_kind_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__1___redArg(v_name_140_, v_bi_141_, v_type_142_, v_k_143_, v_kind_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__1___boxed(lean_object* v_00_u03b1_151_, lean_object* v_name_152_, lean_object* v_bi_153_, lean_object* v_type_154_, lean_object* v_k_155_, lean_object* v_kind_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
uint8_t v_bi_boxed_162_; uint8_t v_kind_boxed_163_; lean_object* v_res_164_; 
v_bi_boxed_162_ = lean_unbox(v_bi_153_);
v_kind_boxed_163_ = lean_unbox(v_kind_156_);
v_res_164_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__1(v_00_u03b1_151_, v_name_152_, v_bi_boxed_162_, v_type_154_, v_k_155_, v_kind_boxed_163_, v___y_157_, v___y_158_, v___y_159_, v___y_160_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___lam__0(lean_object* v_param_168_, uint8_t v___x_169_, lean_object* v_xs_170_, lean_object* v_x_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v___y_178_; uint8_t v___y_179_; lean_object* v_a_184_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_187_ = l_Lean_mkAppN(v_param_168_, v_xs_170_);
v___x_188_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___lam__0___closed__1));
v___x_189_ = lean_unsigned_to_nat(1u);
v___x_190_ = lean_mk_empty_array_with_capacity(v___x_189_);
v___x_191_ = lean_array_push(v___x_190_, v___x_187_);
v___x_192_ = l_Lean_Meta_mkAppM(v___x_188_, v___x_191_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_212_; 
v_a_193_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_212_ == 0)
{
v___x_195_ = v___x_192_;
v_isShared_196_ = v_isSharedCheck_212_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_192_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_212_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
uint8_t v___x_197_; uint8_t v___x_198_; lean_object* v___x_199_; 
v___x_197_ = 0;
v___x_198_ = 1;
v___x_199_ = l_Lean_Meta_mkForallFVars(v_xs_170_, v_a_193_, v___x_197_, v___x_169_, v___x_169_, v___x_198_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_210_; 
v_a_200_ = lean_ctor_get(v___x_199_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_210_ == 0)
{
v___x_202_ = v___x_199_;
v_isShared_203_ = v_isSharedCheck_210_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_199_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_210_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_196_ == 0)
{
lean_ctor_set_tag(v___x_195_, 1);
lean_ctor_set(v___x_195_, 0, v_a_200_);
v___x_205_ = v___x_195_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_a_200_);
v___x_205_ = v_reuseFailAlloc_209_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v___x_207_; 
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 0, v___x_205_);
v___x_207_ = v___x_202_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_205_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
else
{
lean_object* v_a_211_; 
lean_del_object(v___x_195_);
v_a_211_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_a_211_);
lean_dec_ref(v___x_199_);
v_a_184_ = v_a_211_;
goto v___jp_183_;
}
}
}
else
{
lean_object* v_a_213_; 
v_a_213_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_a_213_);
lean_dec_ref(v___x_192_);
v_a_184_ = v_a_213_;
goto v___jp_183_;
}
v___jp_177_:
{
if (v___y_179_ == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; 
lean_dec_ref(v___y_178_);
v___x_180_ = lean_box(0);
v___x_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
return v___x_181_;
}
else
{
lean_object* v___x_182_; 
v___x_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_182_, 0, v___y_178_);
return v___x_182_;
}
}
v___jp_183_:
{
uint8_t v___x_185_; 
v___x_185_ = l_Lean_Exception_isInterrupt(v_a_184_);
if (v___x_185_ == 0)
{
uint8_t v___x_186_; 
lean_inc_ref(v_a_184_);
v___x_186_ = l_Lean_Exception_isRuntime(v_a_184_);
v___y_178_ = v_a_184_;
v___y_179_ = v___x_186_;
goto v___jp_177_;
}
else
{
v___y_178_ = v_a_184_;
v___y_179_ = v___x_185_;
goto v___jp_177_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___lam__0___boxed(lean_object* v_param_214_, lean_object* v___x_215_, lean_object* v_xs_216_, lean_object* v_x_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
uint8_t v___x_2412__boxed_223_; lean_object* v_res_224_; 
v___x_2412__boxed_223_ = lean_unbox(v___x_215_);
v_res_224_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___lam__0(v_param_214_, v___x_2412__boxed_223_, v_xs_216_, v_x_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
lean_dec_ref(v_x_217_);
lean_dec_ref(v_xs_216_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___lam__1___boxed(lean_object* v_i_228_, lean_object* v_insts_229_, lean_object* v_params_230_, lean_object* v_k_231_, lean_object* v_inst_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___lam__1(v_i_228_, v_insts_229_, v_params_230_, v_k_231_, v_inst_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v_i_228_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg(lean_object* v_params_239_, lean_object* v_k_240_, lean_object* v_i_241_, lean_object* v_insts_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_){
_start:
{
lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_248_ = lean_array_get_size(v_params_239_);
v___x_249_ = lean_nat_dec_lt(v_i_241_, v___x_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; 
lean_dec(v_i_241_);
lean_dec_ref(v_params_239_);
lean_inc(v_a_246_);
lean_inc_ref(v_a_245_);
lean_inc(v_a_244_);
lean_inc_ref(v_a_243_);
v___x_250_ = lean_apply_6(v_k_240_, v_insts_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, lean_box(0));
return v___x_250_;
}
else
{
lean_object* v_param_251_; lean_object* v___x_252_; 
v_param_251_ = lean_array_fget_borrowed(v_params_239_, v_i_241_);
lean_inc(v_a_246_);
lean_inc_ref(v_a_245_);
lean_inc(v_a_244_);
lean_inc_ref(v_a_243_);
lean_inc(v_param_251_);
v___x_252_ = lean_infer_type(v_param_251_, v_a_243_, v_a_244_, v_a_245_, v_a_246_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v___x_254_; lean_object* v___f_255_; uint8_t v___x_256_; lean_object* v___x_257_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_a_253_);
lean_dec_ref(v___x_252_);
v___x_254_ = lean_box(v___x_249_);
lean_inc(v_param_251_);
v___f_255_ = lean_alloc_closure((void*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_255_, 0, v_param_251_);
lean_closure_set(v___f_255_, 1, v___x_254_);
v___x_256_ = 0;
v___x_257_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__0___redArg(v_a_253_, v___f_255_, v___x_256_, v___x_256_, v_a_243_, v_a_244_, v_a_245_, v_a_246_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v_a_258_; 
v_a_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc(v_a_258_);
lean_dec_ref(v___x_257_);
if (lean_obj_tag(v_a_258_) == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_unsigned_to_nat(1u);
v___x_260_ = lean_nat_add(v_i_241_, v___x_259_);
lean_dec(v_i_241_);
v_i_241_ = v___x_260_;
goto _start;
}
else
{
lean_object* v_val_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v_val_262_ = lean_ctor_get(v_a_258_, 0);
lean_inc(v_val_262_);
lean_dec_ref(v_a_258_);
v___x_263_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___closed__1));
v___x_264_ = l_Lean_Core_mkFreshUserName(v___x_263_, v_a_245_, v_a_246_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v_a_265_; lean_object* v___f_266_; uint8_t v___x_267_; uint8_t v___x_268_; lean_object* v___x_269_; 
v_a_265_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_a_265_);
lean_dec_ref(v___x_264_);
v___f_266_ = lean_alloc_closure((void*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_266_, 0, v_i_241_);
lean_closure_set(v___f_266_, 1, v_insts_242_);
lean_closure_set(v___f_266_, 2, v_params_239_);
lean_closure_set(v___f_266_, 3, v_k_240_);
v___x_267_ = 3;
v___x_268_ = 0;
v___x_269_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__1___redArg(v_a_265_, v___x_267_, v_val_262_, v___f_266_, v___x_268_, v_a_243_, v_a_244_, v_a_245_, v_a_246_);
return v___x_269_;
}
else
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
lean_dec(v_val_262_);
lean_dec_ref(v_insts_242_);
lean_dec(v_i_241_);
lean_dec_ref(v_k_240_);
lean_dec_ref(v_params_239_);
v_a_270_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v___x_264_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_264_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_a_270_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
}
else
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
lean_dec_ref(v_insts_242_);
lean_dec(v_i_241_);
lean_dec_ref(v_k_240_);
lean_dec_ref(v_params_239_);
v_a_278_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v___x_257_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_257_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_278_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
else
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
lean_dec_ref(v_insts_242_);
lean_dec(v_i_241_);
lean_dec_ref(v_k_240_);
lean_dec_ref(v_params_239_);
v_a_286_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_252_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_252_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___lam__1(lean_object* v_i_294_, lean_object* v_insts_295_, lean_object* v_params_296_, lean_object* v_k_297_, lean_object* v_inst_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_304_ = lean_unsigned_to_nat(1u);
v___x_305_ = lean_nat_add(v_i_294_, v___x_304_);
v___x_306_ = lean_array_push(v_insts_295_, v_inst_298_);
v___x_307_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg(v_params_296_, v_k_297_, v___x_305_, v___x_306_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___boxed(lean_object* v_params_308_, lean_object* v_k_309_, lean_object* v_i_310_, lean_object* v_insts_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg(v_params_308_, v_k_309_, v_i_310_, v_insts_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_);
lean_dec(v_a_315_);
lean_dec_ref(v_a_314_);
lean_dec(v_a_313_);
lean_dec_ref(v_a_312_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop(lean_object* v_00_u03b1_318_, lean_object* v_params_319_, lean_object* v_k_320_, lean_object* v_i_321_, lean_object* v_insts_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg(v_params_319_, v_k_320_, v_i_321_, v_insts_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___boxed(lean_object* v_00_u03b1_329_, lean_object* v_params_330_, lean_object* v_k_331_, lean_object* v_i_332_, lean_object* v_insts_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop(v_00_u03b1_329_, v_params_330_, v_k_331_, v_i_332_, v_insts_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances___redArg(lean_object* v_params_342_, lean_object* v_k_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_349_ = lean_unsigned_to_nat(0u);
v___x_350_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances___redArg___closed__0));
v___x_351_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg(v_params_342_, v_k_343_, v___x_349_, v___x_350_, v_a_344_, v_a_345_, v_a_346_, v_a_347_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances___redArg___boxed(lean_object* v_params_352_, lean_object* v_k_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances___redArg(v_params_352_, v_k_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_);
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
lean_dec(v_a_355_);
lean_dec_ref(v_a_354_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances(lean_object* v_00_u03b1_360_, lean_object* v_params_361_, lean_object* v_k_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances___redArg(v_params_361_, v_k_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances___boxed(lean_object* v_00_u03b1_369_, lean_object* v_params_370_, lean_object* v_k_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances(v_00_u03b1_369_, v_params_370_, v_k_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
return v_res_377_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_isInductiveHypothesis_x3f_spec__0_spec__0(lean_object* v_a_378_, lean_object* v_as_379_, size_t v_i_380_, size_t v_stop_381_){
_start:
{
uint8_t v___x_382_; 
v___x_382_ = lean_usize_dec_eq(v_i_380_, v_stop_381_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_383_ = lean_array_uget_borrowed(v_as_379_, v_i_380_);
v___x_384_ = lean_expr_eqv(v_a_378_, v___x_383_);
if (v___x_384_ == 0)
{
size_t v___x_385_; size_t v___x_386_; 
v___x_385_ = ((size_t)1ULL);
v___x_386_ = lean_usize_add(v_i_380_, v___x_385_);
v_i_380_ = v___x_386_;
goto _start;
}
else
{
return v___x_384_;
}
}
else
{
uint8_t v___x_388_; 
v___x_388_ = 0;
return v___x_388_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_isInductiveHypothesis_x3f_spec__0_spec__0___boxed(lean_object* v_a_389_, lean_object* v_as_390_, lean_object* v_i_391_, lean_object* v_stop_392_){
_start:
{
size_t v_i_boxed_393_; size_t v_stop_boxed_394_; uint8_t v_res_395_; lean_object* v_r_396_; 
v_i_boxed_393_ = lean_unbox_usize(v_i_391_);
lean_dec(v_i_391_);
v_stop_boxed_394_ = lean_unbox_usize(v_stop_392_);
lean_dec(v_stop_392_);
v_res_395_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_isInductiveHypothesis_x3f_spec__0_spec__0(v_a_389_, v_as_390_, v_i_boxed_393_, v_stop_boxed_394_);
lean_dec_ref(v_as_390_);
lean_dec_ref(v_a_389_);
v_r_396_ = lean_box(v_res_395_);
return v_r_396_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_isInductiveHypothesis_x3f_spec__0(lean_object* v_as_397_, lean_object* v_a_398_){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_399_ = lean_unsigned_to_nat(0u);
v___x_400_ = lean_array_get_size(v_as_397_);
v___x_401_ = lean_nat_dec_lt(v___x_399_, v___x_400_);
if (v___x_401_ == 0)
{
return v___x_401_;
}
else
{
if (v___x_401_ == 0)
{
return v___x_401_;
}
else
{
size_t v___x_402_; size_t v___x_403_; uint8_t v___x_404_; 
v___x_402_ = ((size_t)0ULL);
v___x_403_ = lean_usize_of_nat(v___x_400_);
v___x_404_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_isInductiveHypothesis_x3f_spec__0_spec__0(v_a_398_, v_as_397_, v___x_402_, v___x_403_);
return v___x_404_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_isInductiveHypothesis_x3f_spec__0___boxed(lean_object* v_as_405_, lean_object* v_a_406_){
_start:
{
uint8_t v_res_407_; lean_object* v_r_408_; 
v_res_407_ = l_Array_contains___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_isInductiveHypothesis_x3f_spec__0(v_as_405_, v_a_406_);
lean_dec_ref(v_a_406_);
lean_dec_ref(v_as_405_);
v_r_408_ = lean_box(v_res_407_);
return v_r_408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_isInductiveHypothesis_x3f___lam__0(lean_object* v_motiveFVars_409_, lean_object* v_x_410_, lean_object* v_type_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
uint8_t v___y_418_; uint8_t v___x_424_; 
v___x_424_ = l_Lean_Expr_isApp(v_type_411_);
if (v___x_424_ == 0)
{
v___y_418_ = v___x_424_;
goto v___jp_417_;
}
else
{
lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_425_ = l_Lean_Expr_getAppFn(v_type_411_);
v___x_426_ = l_Array_contains___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_isInductiveHypothesis_x3f_spec__0(v_motiveFVars_409_, v___x_425_);
lean_dec_ref(v___x_425_);
v___y_418_ = v___x_426_;
goto v___jp_417_;
}
v___jp_417_:
{
if (v___y_418_ == 0)
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_box(0);
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
return v___x_420_;
}
else
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_421_ = l_Lean_Expr_appArg_x21(v_type_411_);
v___x_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
return v___x_423_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_isInductiveHypothesis_x3f___lam__0___boxed(lean_object* v_motiveFVars_427_, lean_object* v_x_428_, lean_object* v_type_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_isInductiveHypothesis_x3f___lam__0(v_motiveFVars_427_, v_x_428_, v_type_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec_ref(v_type_429_);
lean_dec_ref(v_x_428_);
lean_dec_ref(v_motiveFVars_427_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_isInductiveHypothesis_x3f(lean_object* v_motiveFVars_436_, lean_object* v_fvar_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
lean_object* v___x_443_; 
lean_inc(v_a_441_);
lean_inc_ref(v_a_440_);
lean_inc(v_a_439_);
lean_inc_ref(v_a_438_);
v___x_443_ = lean_infer_type(v_fvar_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v___f_445_; uint8_t v___x_446_; lean_object* v___x_447_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_a_444_);
lean_dec_ref(v___x_443_);
v___f_445_ = lean_alloc_closure((void*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_isInductiveHypothesis_x3f___lam__0___boxed), 8, 1);
lean_closure_set(v___f_445_, 0, v_motiveFVars_436_);
v___x_446_ = 0;
v___x_447_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__0___redArg(v_a_444_, v___f_445_, v___x_446_, v___x_446_, v_a_438_, v_a_439_, v_a_440_, v_a_441_);
return v___x_447_;
}
else
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
lean_dec_ref(v_motiveFVars_436_);
v_a_448_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v___x_443_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_443_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_isInductiveHypothesis_x3f___boxed(lean_object* v_motiveFVars_456_, lean_object* v_fvar_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_isInductiveHypothesis_x3f(v_motiveFVars_456_, v_fvar_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_);
lean_dec(v_a_461_);
lean_dec_ref(v_a_460_);
lean_dec(v_a_459_);
lean_dec_ref(v_a_458_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_isInductiveHypothesis(lean_object* v_motiveFVars_464_, lean_object* v_fvar_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_isInductiveHypothesis_x3f(v_motiveFVars_464_, v_fvar_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_486_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_486_ == 0)
{
v___x_474_ = v___x_471_;
v_isShared_475_ = v_isSharedCheck_486_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_471_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_486_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
if (lean_obj_tag(v_a_472_) == 0)
{
uint8_t v___x_476_; lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_476_ = 0;
v___x_477_ = lean_box(v___x_476_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v___x_477_);
v___x_479_ = v___x_474_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_477_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
else
{
uint8_t v___x_481_; lean_object* v___x_482_; lean_object* v___x_484_; 
lean_dec_ref(v_a_472_);
v___x_481_ = 1;
v___x_482_ = lean_box(v___x_481_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v___x_482_);
v___x_484_ = v___x_474_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___x_482_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
else
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_494_; 
v_a_487_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_494_ == 0)
{
v___x_489_ = v___x_471_;
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_471_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_487_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_isInductiveHypothesis___boxed(lean_object* v_motiveFVars_495_, lean_object* v_fvar_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_isInductiveHypothesis(v_motiveFVars_495_, v_fvar_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
lean_dec(v_a_498_);
lean_dec_ref(v_a_497_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_isRecField_x3f_spec__0(lean_object* v_motiveFVars_503_, lean_object* v_fvar_504_, lean_object* v_as_505_, size_t v_sz_506_, size_t v_i_507_, lean_object* v_b_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
uint8_t v___x_514_; 
v___x_514_ = lean_usize_dec_lt(v_i_507_, v_sz_506_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; 
lean_dec_ref(v_motiveFVars_503_);
v___x_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_515_, 0, v_b_508_);
return v___x_515_;
}
else
{
lean_object* v_a_516_; lean_object* v___x_517_; 
v_a_516_ = lean_array_uget_borrowed(v_as_505_, v_i_507_);
lean_inc(v_a_516_);
lean_inc_ref(v_motiveFVars_503_);
v___x_517_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_isInductiveHypothesis_x3f(v_motiveFVars_503_, v_a_516_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_553_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_553_ == 0)
{
v___x_520_ = v___x_517_;
v_isShared_521_ = v_isSharedCheck_553_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_517_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_553_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v_snd_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_551_; 
v_snd_522_ = lean_ctor_get(v_b_508_, 1);
v_isSharedCheck_551_ = !lean_is_exclusive(v_b_508_);
if (v_isSharedCheck_551_ == 0)
{
lean_object* v_unused_552_; 
v_unused_552_ = lean_ctor_get(v_b_508_, 0);
lean_dec(v_unused_552_);
v___x_524_ = v_b_508_;
v_isShared_525_ = v_isSharedCheck_551_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_snd_522_);
lean_dec(v_b_508_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_551_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; 
v___x_526_ = lean_box(0);
if (lean_obj_tag(v_a_518_) == 1)
{
lean_object* v_val_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_550_; 
v_val_536_ = lean_ctor_get(v_a_518_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v_a_518_);
if (v_isSharedCheck_550_ == 0)
{
v___x_538_ = v_a_518_;
v_isShared_539_ = v_isSharedCheck_550_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_val_536_);
lean_dec(v_a_518_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_550_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_540_ = l_Lean_Expr_getAppFn(v_val_536_);
lean_dec(v_val_536_);
v___x_541_ = lean_expr_eqv(v_fvar_504_, v___x_540_);
lean_dec_ref(v___x_540_);
if (v___x_541_ == 0)
{
lean_del_object(v___x_538_);
lean_del_object(v___x_520_);
goto v___jp_527_;
}
else
{
lean_object* v___x_543_; 
lean_del_object(v___x_524_);
lean_dec_ref(v_motiveFVars_503_);
lean_inc(v_snd_522_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 0, v_snd_522_);
v___x_543_ = v___x_538_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_snd_522_);
v___x_543_ = v_reuseFailAlloc_549_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_547_; 
v___x_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
v___x_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
lean_ctor_set(v___x_545_, 1, v_snd_522_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_545_);
v___x_547_ = v___x_520_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_545_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
else
{
lean_del_object(v___x_520_);
lean_dec(v_a_518_);
goto v___jp_527_;
}
v___jp_527_:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_528_ = lean_unsigned_to_nat(1u);
v___x_529_ = lean_nat_add(v_snd_522_, v___x_528_);
lean_dec(v_snd_522_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 1, v___x_529_);
lean_ctor_set(v___x_524_, 0, v___x_526_);
v___x_531_ = v___x_524_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v___x_529_);
v___x_531_ = v_reuseFailAlloc_535_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
size_t v___x_532_; size_t v___x_533_; 
v___x_532_ = ((size_t)1ULL);
v___x_533_ = lean_usize_add(v_i_507_, v___x_532_);
v_i_507_ = v___x_533_;
v_b_508_ = v___x_531_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
lean_dec_ref(v_b_508_);
lean_dec_ref(v_motiveFVars_503_);
v_a_554_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_517_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_517_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_554_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_isRecField_x3f_spec__0___boxed(lean_object* v_motiveFVars_562_, lean_object* v_fvar_563_, lean_object* v_as_564_, lean_object* v_sz_565_, lean_object* v_i_566_, lean_object* v_b_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
size_t v_sz_boxed_573_; size_t v_i_boxed_574_; lean_object* v_res_575_; 
v_sz_boxed_573_ = lean_unbox_usize(v_sz_565_);
lean_dec(v_sz_565_);
v_i_boxed_574_ = lean_unbox_usize(v_i_566_);
lean_dec(v_i_566_);
v_res_575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_isRecField_x3f_spec__0(v_motiveFVars_562_, v_fvar_563_, v_as_564_, v_sz_boxed_573_, v_i_boxed_574_, v_b_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec_ref(v_as_564_);
lean_dec_ref(v_fvar_563_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_isRecField_x3f(lean_object* v_motiveFVars_579_, lean_object* v_minorFVars_580_, lean_object* v_fvar_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; size_t v_sz_589_; size_t v___x_590_; lean_object* v___x_591_; 
v___x_587_ = lean_box(0);
v___x_588_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_isRecField_x3f___closed__0));
v_sz_589_ = lean_array_size(v_minorFVars_580_);
v___x_590_ = ((size_t)0ULL);
v___x_591_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_isRecField_x3f_spec__0(v_motiveFVars_579_, v_fvar_581_, v_minorFVars_580_, v_sz_589_, v___x_590_, v___x_588_, v_a_582_, v_a_583_, v_a_584_, v_a_585_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_604_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_604_ == 0)
{
v___x_594_ = v___x_591_;
v_isShared_595_ = v_isSharedCheck_604_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_591_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_604_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v_fst_596_; 
v_fst_596_ = lean_ctor_get(v_a_592_, 0);
lean_inc(v_fst_596_);
lean_dec(v_a_592_);
if (lean_obj_tag(v_fst_596_) == 0)
{
lean_object* v___x_598_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_587_);
v___x_598_ = v___x_594_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_587_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
else
{
lean_object* v_val_600_; lean_object* v___x_602_; 
v_val_600_ = lean_ctor_get(v_fst_596_, 0);
lean_inc(v_val_600_);
lean_dec_ref(v_fst_596_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v_val_600_);
v___x_602_ = v___x_594_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_val_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
else
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_612_; 
v_a_605_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_612_ == 0)
{
v___x_607_ = v___x_591_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_591_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_605_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_isRecField_x3f___boxed(lean_object* v_motiveFVars_613_, lean_object* v_minorFVars_614_, lean_object* v_fvar_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_isRecField_x3f(v_motiveFVars_613_, v_minorFVars_614_, v_fvar_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
lean_dec_ref(v_fvar_615_);
lean_dec_ref(v_minorFVars_614_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__0___redArg(lean_object* v_cls_625_, lean_object* v___y_626_){
_start:
{
lean_object* v_options_628_; uint8_t v_hasTrace_629_; 
v_options_628_ = lean_ctor_get(v___y_626_, 2);
v_hasTrace_629_ = lean_ctor_get_uint8(v_options_628_, sizeof(void*)*1);
if (v_hasTrace_629_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; 
lean_dec(v_cls_625_);
v___x_630_ = lean_box(v_hasTrace_629_);
v___x_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
return v___x_631_;
}
else
{
lean_object* v_inheritedTraceOptions_632_; lean_object* v___x_633_; lean_object* v___x_634_; uint8_t v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v_inheritedTraceOptions_632_ = lean_ctor_get(v___y_626_, 13);
v___x_633_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__0___redArg___closed__1));
v___x_634_ = l_Lean_Name_append(v___x_633_, v_cls_625_);
v___x_635_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_632_, v_options_628_, v___x_634_);
lean_dec(v___x_634_);
v___x_636_ = lean_box(v___x_635_);
v___x_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
return v___x_637_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__0___redArg___boxed(lean_object* v_cls_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__0___redArg(v_cls_638_, v___y_639_);
lean_dec_ref(v___y_639_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__0(lean_object* v_cls_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__0___redArg(v_cls_642_, v___y_645_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__0___boxed(lean_object* v_cls_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__0(v_cls_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
return v_res_655_;
}
}
static lean_object* _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_659_ = lean_box(0);
v___x_660_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___lam__0___closed__1));
v___x_661_ = l_Lean_mkConst(v___x_660_, v___x_659_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___lam__0(uint8_t v___x_662_, lean_object* v_xs_663_, lean_object* v_x_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v___x_670_; uint8_t v___x_671_; uint8_t v___x_672_; lean_object* v___x_673_; 
v___x_670_ = lean_obj_once(&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___lam__0___closed__2, &l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___lam__0___closed__2_once, _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___lam__0___closed__2);
v___x_671_ = 0;
v___x_672_ = 1;
v___x_673_ = l_Lean_Meta_mkLambdaFVars(v_xs_663_, v___x_670_, v___x_671_, v___x_662_, v___x_671_, v___x_662_, v___x_672_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___lam__0___boxed(lean_object* v___x_674_, lean_object* v_xs_675_, lean_object* v_x_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
uint8_t v___x_2419__boxed_682_; lean_object* v_res_683_; 
v___x_2419__boxed_682_ = lean_unbox(v___x_674_);
v_res_683_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___lam__0(v___x_2419__boxed_682_, v_xs_675_, v_x_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec_ref(v_x_676_);
lean_dec_ref(v_xs_675_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1_spec__1(lean_object* v_msgData_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v___x_690_; lean_object* v_env_691_; lean_object* v___x_692_; lean_object* v_mctx_693_; lean_object* v_lctx_694_; lean_object* v_options_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_690_ = lean_st_ref_get(v___y_688_);
v_env_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc_ref(v_env_691_);
lean_dec(v___x_690_);
v___x_692_ = lean_st_ref_get(v___y_686_);
v_mctx_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc_ref(v_mctx_693_);
lean_dec(v___x_692_);
v_lctx_694_ = lean_ctor_get(v___y_685_, 2);
v_options_695_ = lean_ctor_get(v___y_687_, 2);
lean_inc_ref(v_options_695_);
lean_inc_ref(v_lctx_694_);
v___x_696_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_696_, 0, v_env_691_);
lean_ctor_set(v___x_696_, 1, v_mctx_693_);
lean_ctor_set(v___x_696_, 2, v_lctx_694_);
lean_ctor_set(v___x_696_, 3, v_options_695_);
v___x_697_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
lean_ctor_set(v___x_697_, 1, v_msgData_684_);
v___x_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1_spec__1___boxed(lean_object* v_msgData_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1_spec__1(v_msgData_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
return v_res_705_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1___closed__0(void){
_start:
{
lean_object* v___x_706_; double v___x_707_; 
v___x_706_ = lean_unsigned_to_nat(0u);
v___x_707_ = lean_float_of_nat(v___x_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1(lean_object* v_cls_711_, lean_object* v_msg_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v_ref_718_; lean_object* v___x_719_; lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_764_; 
v_ref_718_ = lean_ctor_get(v___y_715_, 5);
v___x_719_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1_spec__1(v_msg_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
v_a_720_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_764_ == 0)
{
v___x_722_ = v___x_719_;
v_isShared_723_ = v_isSharedCheck_764_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_719_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_764_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_724_; lean_object* v_traceState_725_; lean_object* v_env_726_; lean_object* v_nextMacroScope_727_; lean_object* v_ngen_728_; lean_object* v_auxDeclNGen_729_; lean_object* v_cache_730_; lean_object* v_messages_731_; lean_object* v_infoState_732_; lean_object* v_snapshotTasks_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_763_; 
v___x_724_ = lean_st_ref_take(v___y_716_);
v_traceState_725_ = lean_ctor_get(v___x_724_, 4);
v_env_726_ = lean_ctor_get(v___x_724_, 0);
v_nextMacroScope_727_ = lean_ctor_get(v___x_724_, 1);
v_ngen_728_ = lean_ctor_get(v___x_724_, 2);
v_auxDeclNGen_729_ = lean_ctor_get(v___x_724_, 3);
v_cache_730_ = lean_ctor_get(v___x_724_, 5);
v_messages_731_ = lean_ctor_get(v___x_724_, 6);
v_infoState_732_ = lean_ctor_get(v___x_724_, 7);
v_snapshotTasks_733_ = lean_ctor_get(v___x_724_, 8);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_763_ == 0)
{
v___x_735_ = v___x_724_;
v_isShared_736_ = v_isSharedCheck_763_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_snapshotTasks_733_);
lean_inc(v_infoState_732_);
lean_inc(v_messages_731_);
lean_inc(v_cache_730_);
lean_inc(v_traceState_725_);
lean_inc(v_auxDeclNGen_729_);
lean_inc(v_ngen_728_);
lean_inc(v_nextMacroScope_727_);
lean_inc(v_env_726_);
lean_dec(v___x_724_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_763_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
uint64_t v_tid_737_; lean_object* v_traces_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_762_; 
v_tid_737_ = lean_ctor_get_uint64(v_traceState_725_, sizeof(void*)*1);
v_traces_738_ = lean_ctor_get(v_traceState_725_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v_traceState_725_);
if (v_isSharedCheck_762_ == 0)
{
v___x_740_ = v_traceState_725_;
v_isShared_741_ = v_isSharedCheck_762_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_traces_738_);
lean_dec(v_traceState_725_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_762_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_742_; double v___x_743_; uint8_t v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_742_ = lean_box(0);
v___x_743_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1___closed__0);
v___x_744_ = 0;
v___x_745_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1___closed__1));
v___x_746_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_746_, 0, v_cls_711_);
lean_ctor_set(v___x_746_, 1, v___x_742_);
lean_ctor_set(v___x_746_, 2, v___x_745_);
lean_ctor_set_float(v___x_746_, sizeof(void*)*3, v___x_743_);
lean_ctor_set_float(v___x_746_, sizeof(void*)*3 + 8, v___x_743_);
lean_ctor_set_uint8(v___x_746_, sizeof(void*)*3 + 16, v___x_744_);
v___x_747_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1___closed__2));
v___x_748_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_748_, 0, v___x_746_);
lean_ctor_set(v___x_748_, 1, v_a_720_);
lean_ctor_set(v___x_748_, 2, v___x_747_);
lean_inc(v_ref_718_);
v___x_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_749_, 0, v_ref_718_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = l_Lean_PersistentArray_push___redArg(v_traces_738_, v___x_749_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_750_);
v___x_752_ = v___x_740_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_750_);
lean_ctor_set_uint64(v_reuseFailAlloc_761_, sizeof(void*)*1, v_tid_737_);
v___x_752_ = v_reuseFailAlloc_761_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_754_; 
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 4, v___x_752_);
v___x_754_ = v___x_735_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_env_726_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_nextMacroScope_727_);
lean_ctor_set(v_reuseFailAlloc_760_, 2, v_ngen_728_);
lean_ctor_set(v_reuseFailAlloc_760_, 3, v_auxDeclNGen_729_);
lean_ctor_set(v_reuseFailAlloc_760_, 4, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_760_, 5, v_cache_730_);
lean_ctor_set(v_reuseFailAlloc_760_, 6, v_messages_731_);
lean_ctor_set(v_reuseFailAlloc_760_, 7, v_infoState_732_);
lean_ctor_set(v_reuseFailAlloc_760_, 8, v_snapshotTasks_733_);
v___x_754_ = v_reuseFailAlloc_760_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_758_; 
v___x_755_ = lean_st_ref_set(v___y_716_, v___x_754_);
v___x_756_ = lean_box(0);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v___x_756_);
v___x_758_ = v___x_722_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_756_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1___boxed(lean_object* v_cls_765_, lean_object* v_msg_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1(v_cls_765_, v_msg_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
return v_res_772_;
}
}
static lean_object* _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__4(void){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__3));
v___x_780_ = l_Lean_stringToMessageData(v___x_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg(lean_object* v_motiveFVars_781_, lean_object* v_k_782_, lean_object* v_i_783_, lean_object* v_motives_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_){
_start:
{
lean_object* v___x_790_; uint8_t v___x_791_; 
v___x_790_ = lean_array_get_size(v_motiveFVars_781_);
v___x_791_ = lean_nat_dec_lt(v_i_783_, v___x_790_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; 
lean_dec(v_i_783_);
lean_inc(v_a_788_);
lean_inc_ref(v_a_787_);
lean_inc(v_a_786_);
lean_inc_ref(v_a_785_);
v___x_792_ = lean_apply_6(v_k_782_, v_motives_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, lean_box(0));
return v___x_792_;
}
else
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = lean_array_fget_borrowed(v_motiveFVars_781_, v_i_783_);
lean_inc(v_a_788_);
lean_inc_ref(v_a_787_);
lean_inc(v_a_786_);
lean_inc_ref(v_a_785_);
lean_inc(v___x_793_);
v___x_794_ = lean_infer_type(v___x_793_, v_a_785_, v_a_786_, v_a_787_, v_a_788_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; lean_object* v___x_796_; lean_object* v___f_797_; uint8_t v___x_798_; lean_object* v___x_799_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_a_795_);
lean_dec_ref(v___x_794_);
v___x_796_ = lean_box(v___x_791_);
v___f_797_ = lean_alloc_closure((void*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_797_, 0, v___x_796_);
v___x_798_ = 0;
v___x_799_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__0___redArg(v_a_795_, v___f_797_, v___x_798_, v___x_798_, v_a_785_, v_a_786_, v_a_787_, v_a_788_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___x_810_; lean_object* v___x_811_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_800_);
lean_dec_ref(v___x_799_);
v___x_810_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__2));
v___x_811_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__0___redArg(v___x_810_, v_a_787_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; uint8_t v___x_813_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_a_812_);
lean_dec_ref(v___x_811_);
v___x_813_ = lean_unbox(v_a_812_);
lean_dec(v_a_812_);
if (v___x_813_ == 0)
{
v___y_802_ = v_a_785_;
v___y_803_ = v_a_786_;
v___y_804_ = v_a_787_;
v___y_805_ = v_a_788_;
goto v___jp_801_;
}
else
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_814_ = lean_obj_once(&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__4, &l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__4_once, _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__4);
lean_inc(v_a_800_);
v___x_815_ = l_Lean_MessageData_ofExpr(v_a_800_);
v___x_816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_814_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1(v___x_810_, v___x_816_, v_a_785_, v_a_786_, v_a_787_, v_a_788_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_dec_ref(v___x_817_);
v___y_802_ = v_a_785_;
v___y_803_ = v_a_786_;
v___y_804_ = v_a_787_;
v___y_805_ = v_a_788_;
goto v___jp_801_;
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
lean_dec(v_a_800_);
lean_dec_ref(v_motives_784_);
lean_dec(v_i_783_);
lean_dec_ref(v_k_782_);
v_a_818_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_817_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_817_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
}
else
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
lean_dec(v_a_800_);
lean_dec_ref(v_motives_784_);
lean_dec(v_i_783_);
lean_dec_ref(v_k_782_);
v_a_826_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_811_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_811_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
v___jp_801_:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_806_ = lean_unsigned_to_nat(1u);
v___x_807_ = lean_nat_add(v_i_783_, v___x_806_);
lean_dec(v_i_783_);
v___x_808_ = lean_array_push(v_motives_784_, v_a_800_);
v_i_783_ = v___x_807_;
v_motives_784_ = v___x_808_;
v_a_785_ = v___y_802_;
v_a_786_ = v___y_803_;
v_a_787_ = v___y_804_;
v_a_788_ = v___y_805_;
goto _start;
}
}
else
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
lean_dec_ref(v_motives_784_);
lean_dec(v_i_783_);
lean_dec_ref(v_k_782_);
v_a_834_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_799_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_799_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_a_834_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
else
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
lean_dec_ref(v_motives_784_);
lean_dec(v_i_783_);
lean_dec_ref(v_k_782_);
v_a_842_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_794_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_794_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___boxed(lean_object* v_motiveFVars_850_, lean_object* v_k_851_, lean_object* v_i_852_, lean_object* v_motives_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg(v_motiveFVars_850_, v_k_851_, v_i_852_, v_motives_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec_ref(v_motiveFVars_850_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop(lean_object* v_00_u03b1_860_, lean_object* v_motiveFVars_861_, lean_object* v_k_862_, lean_object* v_i_863_, lean_object* v_motives_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg(v_motiveFVars_861_, v_k_862_, v_i_863_, v_motives_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___boxed(lean_object* v_00_u03b1_871_, lean_object* v_motiveFVars_872_, lean_object* v_k_873_, lean_object* v_i_874_, lean_object* v_motives_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop(v_00_u03b1_871_, v_motiveFVars_872_, v_k_873_, v_i_874_, v_motives_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec_ref(v_motiveFVars_872_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives___redArg(lean_object* v_motiveFVars_882_, lean_object* v_k_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_889_ = lean_unsigned_to_nat(0u);
v___x_890_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances___redArg___closed__0));
v___x_891_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg(v_motiveFVars_882_, v_k_883_, v___x_889_, v___x_890_, v_a_884_, v_a_885_, v_a_886_, v_a_887_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives___redArg___boxed(lean_object* v_motiveFVars_892_, lean_object* v_k_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives___redArg(v_motiveFVars_892_, v_k_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_);
lean_dec(v_a_897_);
lean_dec_ref(v_a_896_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
lean_dec_ref(v_motiveFVars_892_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives(lean_object* v_00_u03b1_900_, lean_object* v_motiveFVars_901_, lean_object* v_k_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives___redArg(v_motiveFVars_901_, v_k_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives___boxed(lean_object* v_00_u03b1_909_, lean_object* v_motiveFVars_910_, lean_object* v_k_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives(v_00_u03b1_909_, v_motiveFVars_910_, v_k_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec_ref(v_motiveFVars_910_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_ignoreFieldType(lean_object* v_type_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
lean_object* v___x_927_; 
lean_inc(v_a_925_);
lean_inc_ref(v_a_924_);
lean_inc(v_a_923_);
lean_inc_ref(v_a_922_);
v___x_927_ = lean_whnf(v_type_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_947_; 
v_a_928_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_947_ == 0)
{
v___x_930_ = v___x_927_;
v_isShared_931_ = v_isSharedCheck_947_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_927_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_947_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
uint8_t v___x_932_; uint8_t v___y_934_; 
v___x_932_ = l_Lean_Expr_isForall(v_a_928_);
if (v___x_932_ == 0)
{
lean_object* v___x_941_; lean_object* v___x_942_; 
lean_del_object(v___x_930_);
lean_dec(v_a_928_);
v___x_941_ = lean_box(v___x_932_);
v___x_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
return v___x_942_;
}
else
{
uint8_t v___x_943_; 
v___x_943_ = l_Lean_Expr_isArrow(v_a_928_);
if (v___x_943_ == 0)
{
v___y_934_ = v___x_943_;
goto v___jp_933_;
}
else
{
lean_object* v___x_944_; lean_object* v___x_945_; uint8_t v___x_946_; 
v___x_944_ = l_Lean_Expr_bindingDomain_x21(v_a_928_);
v___x_945_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_ignoreFieldType___closed__1));
v___x_946_ = l_Lean_Expr_isConstOf(v___x_944_, v___x_945_);
lean_dec_ref(v___x_944_);
v___y_934_ = v___x_946_;
goto v___jp_933_;
}
}
v___jp_933_:
{
if (v___y_934_ == 0)
{
lean_object* v___x_935_; lean_object* v___x_937_; 
lean_dec(v_a_928_);
v___x_935_ = lean_box(v___x_932_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v___x_935_);
v___x_937_ = v___x_930_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_935_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
else
{
lean_object* v___x_939_; 
lean_del_object(v___x_930_);
v___x_939_ = l_Lean_Expr_bindingBody_x21(v_a_928_);
lean_dec(v_a_928_);
v_type_921_ = v___x_939_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
v_a_948_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_927_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_927_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_ignoreFieldType___boxed(lean_object* v_type_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_ignoreFieldType(v_type_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_ignoreField(lean_object* v_x_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_){
_start:
{
lean_object* v___x_969_; 
lean_inc(v_a_967_);
lean_inc_ref(v_a_966_);
lean_inc(v_a_965_);
lean_inc_ref(v_a_964_);
v___x_969_ = lean_infer_type(v_x_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_971_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_970_);
lean_dec_ref(v___x_969_);
v___x_971_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_ignoreFieldType(v_a_970_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
return v___x_971_;
}
else
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
v_a_972_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_979_ == 0)
{
v___x_974_ = v___x_969_;
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_969_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_975_ == 0)
{
v___x_977_ = v___x_974_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_a_972_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_ignoreField___boxed(lean_object* v_x_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_ignoreField(v_x_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
return v_res_986_;
}
}
static lean_object* _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfRecFieldFormIH___closed__2(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_991_ = lean_box(0);
v___x_992_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfRecFieldFormIH___closed__1));
v___x_993_ = l_Lean_mkConst(v___x_992_, v___x_991_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfRecFieldFormIH(lean_object* v_ih_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
lean_object* v___x_1000_; 
lean_inc(v_a_998_);
lean_inc_ref(v_a_997_);
lean_inc(v_a_996_);
lean_inc_ref(v_a_995_);
lean_inc_ref(v_ih_994_);
v___x_1000_ = lean_infer_type(v_ih_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1002_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref(v___x_1000_);
lean_inc(v_a_998_);
lean_inc_ref(v_a_997_);
lean_inc(v_a_996_);
lean_inc_ref(v_a_995_);
v___x_1002_ = lean_whnf(v_a_1001_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1014_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1014_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1014_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
uint8_t v___x_1007_; 
v___x_1007_ = l_Lean_Expr_isForall(v_a_1003_);
lean_dec(v_a_1003_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1009_; 
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v_ih_994_);
v___x_1009_ = v___x_1005_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_ih_994_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
else
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
lean_del_object(v___x_1005_);
v___x_1011_ = lean_obj_once(&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfRecFieldFormIH___closed__2, &l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfRecFieldFormIH___closed__2_once, _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfRecFieldFormIH___closed__2);
v___x_1012_ = l_Lean_Expr_app___override(v_ih_994_, v___x_1011_);
v_ih_994_ = v___x_1012_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_ih_994_);
return v___x_1002_;
}
}
else
{
lean_dec_ref(v_ih_994_);
return v___x_1000_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfRecFieldFormIH___boxed(lean_object* v_ih_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfRecFieldFormIH(v_ih_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
lean_dec(v_a_1019_);
lean_dec_ref(v_a_1018_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop_spec__1___redArg(lean_object* v_type_1022_, lean_object* v_maxFVars_x3f_1023_, lean_object* v_k_1024_, uint8_t v_cleanupAnnotations_1025_, uint8_t v_whnfType_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v___f_1032_; lean_object* v___x_1033_; 
v___f_1032_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1032_, 0, v_k_1024_);
v___x_1033_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1022_, v_maxFVars_x3f_1023_, v___f_1032_, v_cleanupAnnotations_1025_, v_whnfType_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_1033_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1033_);
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
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
v_a_1042_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1033_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1033_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop_spec__1___redArg___boxed(lean_object* v_type_1050_, lean_object* v_maxFVars_x3f_1051_, lean_object* v_k_1052_, lean_object* v_cleanupAnnotations_1053_, lean_object* v_whnfType_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1060_; uint8_t v_whnfType_boxed_1061_; lean_object* v_res_1062_; 
v_cleanupAnnotations_boxed_1060_ = lean_unbox(v_cleanupAnnotations_1053_);
v_whnfType_boxed_1061_ = lean_unbox(v_whnfType_1054_);
v_res_1062_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop_spec__1___redArg(v_type_1050_, v_maxFVars_x3f_1051_, v_k_1052_, v_cleanupAnnotations_boxed_1060_, v_whnfType_boxed_1061_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop_spec__1(lean_object* v_00_u03b1_1063_, lean_object* v_type_1064_, lean_object* v_maxFVars_x3f_1065_, lean_object* v_k_1066_, uint8_t v_cleanupAnnotations_1067_, uint8_t v_whnfType_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop_spec__1___redArg(v_type_1064_, v_maxFVars_x3f_1065_, v_k_1066_, v_cleanupAnnotations_1067_, v_whnfType_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop_spec__1___boxed(lean_object* v_00_u03b1_1075_, lean_object* v_type_1076_, lean_object* v_maxFVars_x3f_1077_, lean_object* v_k_1078_, lean_object* v_cleanupAnnotations_1079_, lean_object* v_whnfType_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1086_; uint8_t v_whnfType_boxed_1087_; lean_object* v_res_1088_; 
v_cleanupAnnotations_boxed_1086_ = lean_unbox(v_cleanupAnnotations_1079_);
v_whnfType_boxed_1087_ = lean_unbox(v_whnfType_1080_);
v_res_1088_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop_spec__1(v_00_u03b1_1075_, v_type_1076_, v_maxFVars_x3f_1077_, v_k_1078_, v_cleanupAnnotations_boxed_1086_, v_whnfType_boxed_1087_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop_spec__0(lean_object* v_motiveFVars_1092_, lean_object* v_xs_1093_, lean_object* v_xs_x27_1094_, lean_object* v_as_1095_, size_t v_sz_1096_, size_t v_i_1097_, lean_object* v_b_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v_a_1105_; uint8_t v___x_1109_; 
v___x_1109_ = lean_usize_dec_lt(v_i_1097_, v_sz_1096_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1110_; 
lean_dec_ref(v_motiveFVars_1092_);
v___x_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1110_, 0, v_b_1098_);
return v___x_1110_;
}
else
{
lean_object* v_snd_1111_; lean_object* v_fst_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1228_; 
v_snd_1111_ = lean_ctor_get(v_b_1098_, 1);
v_fst_1112_ = lean_ctor_get(v_b_1098_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_b_1098_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1114_ = v_b_1098_;
v_isShared_1115_ = v_isSharedCheck_1228_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_snd_1111_);
lean_inc(v_fst_1112_);
lean_dec(v_b_1098_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1228_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v_array_1116_; lean_object* v_start_1117_; lean_object* v_stop_1118_; uint8_t v___x_1119_; 
v_array_1116_ = lean_ctor_get(v_snd_1111_, 0);
v_start_1117_ = lean_ctor_get(v_snd_1111_, 1);
v_stop_1118_ = lean_ctor_get(v_snd_1111_, 2);
v___x_1119_ = lean_nat_dec_lt(v_start_1117_, v_stop_1118_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1121_; 
lean_dec_ref(v_motiveFVars_1092_);
if (v_isShared_1115_ == 0)
{
v___x_1121_ = v___x_1114_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_fst_1112_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v_snd_1111_);
v___x_1121_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
lean_object* v___x_1122_; 
v___x_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
return v___x_1122_;
}
}
else
{
lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1224_; 
lean_inc(v_stop_1118_);
lean_inc(v_start_1117_);
lean_inc_ref(v_array_1116_);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_snd_1111_);
if (v_isSharedCheck_1224_ == 0)
{
lean_object* v_unused_1225_; lean_object* v_unused_1226_; lean_object* v_unused_1227_; 
v_unused_1225_ = lean_ctor_get(v_snd_1111_, 2);
lean_dec(v_unused_1225_);
v_unused_1226_ = lean_ctor_get(v_snd_1111_, 1);
lean_dec(v_unused_1226_);
v_unused_1227_ = lean_ctor_get(v_snd_1111_, 0);
lean_dec(v_unused_1227_);
v___x_1125_ = v_snd_1111_;
v_isShared_1126_ = v_isSharedCheck_1224_;
goto v_resetjp_1124_;
}
else
{
lean_dec(v_snd_1111_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1224_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v_a_1127_; lean_object* v___x_1128_; 
v_a_1127_ = lean_array_uget_borrowed(v_as_1095_, v_i_1097_);
lean_inc(v_a_1127_);
lean_inc_ref(v_motiveFVars_1092_);
v___x_1128_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_isInductiveHypothesis(v_motiveFVars_1092_, v_a_1127_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1134_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
lean_dec_ref(v___x_1128_);
v___x_1130_ = lean_array_fget(v_array_1116_, v_start_1117_);
v___x_1131_ = lean_unsigned_to_nat(1u);
v___x_1132_ = lean_nat_add(v_start_1117_, v___x_1131_);
lean_dec(v_start_1117_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 1, v___x_1132_);
v___x_1134_ = v___x_1125_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_array_1116_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v___x_1132_);
lean_ctor_set(v_reuseFailAlloc_1215_, 2, v_stop_1118_);
v___x_1134_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
uint8_t v___x_1135_; 
v___x_1135_ = lean_unbox(v_a_1129_);
lean_dec(v_a_1129_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; 
lean_inc(v_a_1127_);
v___x_1136_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_ignoreField(v_a_1127_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; uint8_t v___x_1138_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_a_1137_);
lean_dec_ref(v___x_1136_);
v___x_1138_ = lean_unbox(v_a_1137_);
lean_dec(v_a_1137_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; 
lean_inc_ref(v_motiveFVars_1092_);
v___x_1139_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_isRecField_x3f(v_motiveFVars_1092_, v_xs_1093_, v_a_1127_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1140_);
lean_dec_ref(v___x_1139_);
if (lean_obj_tag(v_a_1140_) == 0)
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1141_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop_spec__0___closed__0));
v___x_1142_ = lean_mk_empty_array_with_capacity(v___x_1131_);
v___x_1143_ = lean_array_push(v___x_1142_, v___x_1130_);
v___x_1144_ = l_Lean_Meta_mkAppM(v___x_1141_, v___x_1143_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1145_; lean_object* v___x_1146_; 
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_a_1145_);
lean_dec_ref(v___x_1144_);
v___x_1146_ = l_Lean_Meta_mkAdd(v_fst_1112_, v_a_1145_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1149_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_a_1147_);
lean_dec_ref(v___x_1146_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 1, v___x_1134_);
lean_ctor_set(v___x_1114_, 0, v_a_1147_);
v___x_1149_ = v___x_1114_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1147_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v___x_1134_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
v_a_1105_ = v___x_1149_;
goto v___jp_1104_;
}
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
lean_dec_ref(v___x_1134_);
lean_del_object(v___x_1114_);
lean_dec_ref(v_motiveFVars_1092_);
v_a_1151_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1153_ = v___x_1146_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1146_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1151_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
else
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
lean_dec_ref(v___x_1134_);
lean_del_object(v___x_1114_);
lean_dec(v_fst_1112_);
lean_dec_ref(v_motiveFVars_1092_);
v_a_1159_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1144_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1144_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
else
{
lean_object* v_val_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
lean_dec(v___x_1130_);
v_val_1167_ = lean_ctor_get(v_a_1140_, 0);
lean_inc(v_val_1167_);
lean_dec_ref(v_a_1140_);
v___x_1168_ = l_Lean_instInhabitedExpr;
v___x_1169_ = lean_array_get_borrowed(v___x_1168_, v_xs_x27_1094_, v_val_1167_);
lean_dec(v_val_1167_);
lean_inc(v___x_1169_);
v___x_1170_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfRecFieldFormIH(v___x_1169_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v___x_1172_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_a_1171_);
lean_dec_ref(v___x_1170_);
v___x_1172_ = l_Lean_Meta_mkAdd(v_fst_1112_, v_a_1171_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v___x_1175_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1173_);
lean_dec_ref(v___x_1172_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 1, v___x_1134_);
lean_ctor_set(v___x_1114_, 0, v_a_1173_);
v___x_1175_ = v___x_1114_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1173_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v___x_1134_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
v_a_1105_ = v___x_1175_;
goto v___jp_1104_;
}
}
else
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1184_; 
lean_dec_ref(v___x_1134_);
lean_del_object(v___x_1114_);
lean_dec_ref(v_motiveFVars_1092_);
v_a_1177_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1179_ = v___x_1172_;
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1172_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1177_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
else
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
lean_dec_ref(v___x_1134_);
lean_del_object(v___x_1114_);
lean_dec(v_fst_1112_);
lean_dec_ref(v_motiveFVars_1092_);
v_a_1185_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1170_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1170_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
lean_dec_ref(v___x_1134_);
lean_dec(v___x_1130_);
lean_del_object(v___x_1114_);
lean_dec(v_fst_1112_);
lean_dec_ref(v_motiveFVars_1092_);
v_a_1193_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1139_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1139_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
else
{
lean_object* v___x_1202_; 
lean_dec(v___x_1130_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 1, v___x_1134_);
v___x_1202_ = v___x_1114_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_fst_1112_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v___x_1134_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
v_a_1105_ = v___x_1202_;
goto v___jp_1104_;
}
}
}
else
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1211_; 
lean_dec_ref(v___x_1134_);
lean_dec(v___x_1130_);
lean_del_object(v___x_1114_);
lean_dec(v_fst_1112_);
lean_dec_ref(v_motiveFVars_1092_);
v_a_1204_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1206_ = v___x_1136_;
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1136_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_a_1204_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
else
{
lean_object* v___x_1213_; 
lean_dec(v___x_1130_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 1, v___x_1134_);
v___x_1213_ = v___x_1114_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_fst_1112_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v___x_1134_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
v_a_1105_ = v___x_1213_;
goto v___jp_1104_;
}
}
}
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_del_object(v___x_1125_);
lean_dec(v_stop_1118_);
lean_dec(v_start_1117_);
lean_dec_ref(v_array_1116_);
lean_del_object(v___x_1114_);
lean_dec(v_fst_1112_);
lean_dec_ref(v_motiveFVars_1092_);
v_a_1216_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1128_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1128_);
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
}
}
}
v___jp_1104_:
{
size_t v___x_1106_; size_t v___x_1107_; 
v___x_1106_ = ((size_t)1ULL);
v___x_1107_ = lean_usize_add(v_i_1097_, v___x_1106_);
v_i_1097_ = v___x_1107_;
v_b_1098_ = v_a_1105_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop_spec__0___boxed(lean_object* v_motiveFVars_1229_, lean_object* v_xs_1230_, lean_object* v_xs_x27_1231_, lean_object* v_as_1232_, lean_object* v_sz_1233_, lean_object* v_i_1234_, lean_object* v_b_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
size_t v_sz_boxed_1241_; size_t v_i_boxed_1242_; lean_object* v_res_1243_; 
v_sz_boxed_1241_ = lean_unbox_usize(v_sz_1233_);
lean_dec(v_sz_1233_);
v_i_boxed_1242_ = lean_unbox_usize(v_i_1234_);
lean_dec(v_i_1234_);
v_res_1243_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop_spec__0(v_motiveFVars_1229_, v_xs_1230_, v_xs_x27_1231_, v_as_1232_, v_sz_boxed_1241_, v_i_boxed_1242_, v_b_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec_ref(v_as_1232_);
lean_dec_ref(v_xs_x27_1231_);
lean_dec_ref(v_xs_1230_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop___redArg___lam__1___boxed(lean_object* v___x_1244_, lean_object* v_minorFVars_x27_1245_, lean_object* v_i_1246_, lean_object* v_motiveFVars_1247_, lean_object* v___x_1248_, lean_object* v_minors_1249_, lean_object* v_minorFVars_1250_, lean_object* v_k_1251_, lean_object* v_xs_1252_, lean_object* v_x_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
uint8_t v___x_5568__boxed_1259_; lean_object* v_res_1260_; 
v___x_5568__boxed_1259_ = lean_unbox(v___x_1248_);
v_res_1260_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop___redArg___lam__1(v___x_1244_, v_minorFVars_x27_1245_, v_i_1246_, v_motiveFVars_1247_, v___x_5568__boxed_1259_, v_minors_1249_, v_minorFVars_1250_, v_k_1251_, v_xs_1252_, v_x_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec_ref(v_x_1253_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop___redArg(lean_object* v_motiveFVars_1261_, lean_object* v_minorFVars_1262_, lean_object* v_minorFVars_x27_1263_, lean_object* v_k_1264_, lean_object* v_i_1265_, lean_object* v_minors_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_){
_start:
{
lean_object* v___x_1272_; uint8_t v___x_1273_; 
v___x_1272_ = lean_array_get_size(v_minorFVars_1262_);
v___x_1273_ = lean_nat_dec_lt(v_i_1265_, v___x_1272_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1274_; 
lean_dec(v_i_1265_);
lean_dec_ref(v_minorFVars_x27_1263_);
lean_dec_ref(v_minorFVars_1262_);
lean_dec_ref(v_motiveFVars_1261_);
lean_inc(v_a_1270_);
lean_inc_ref(v_a_1269_);
lean_inc(v_a_1268_);
lean_inc_ref(v_a_1267_);
v___x_1274_ = lean_apply_6(v_k_1264_, v_minors_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, lean_box(0));
return v___x_1274_;
}
else
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1275_ = l_Lean_instInhabitedExpr;
v___x_1276_ = lean_array_get_borrowed(v___x_1275_, v_minorFVars_1262_, v_i_1265_);
lean_inc(v_a_1270_);
lean_inc_ref(v_a_1269_);
lean_inc(v_a_1268_);
lean_inc_ref(v_a_1267_);
lean_inc(v___x_1276_);
v___x_1277_ = lean_infer_type(v___x_1276_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1279_; lean_object* v___f_1280_; uint8_t v___x_1281_; lean_object* v___x_1282_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_a_1278_);
lean_dec_ref(v___x_1277_);
v___x_1279_ = lean_box(v___x_1273_);
v___f_1280_ = lean_alloc_closure((void*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop___redArg___lam__1___boxed), 15, 8);
lean_closure_set(v___f_1280_, 0, v___x_1275_);
lean_closure_set(v___f_1280_, 1, v_minorFVars_x27_1263_);
lean_closure_set(v___f_1280_, 2, v_i_1265_);
lean_closure_set(v___f_1280_, 3, v_motiveFVars_1261_);
lean_closure_set(v___f_1280_, 4, v___x_1279_);
lean_closure_set(v___f_1280_, 5, v_minors_1266_);
lean_closure_set(v___f_1280_, 6, v_minorFVars_1262_);
lean_closure_set(v___f_1280_, 7, v_k_1264_);
v___x_1281_ = 0;
v___x_1282_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__0___redArg(v_a_1278_, v___f_1280_, v___x_1281_, v___x_1281_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
return v___x_1282_;
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_dec_ref(v_minors_1266_);
lean_dec(v_i_1265_);
lean_dec_ref(v_k_1264_);
lean_dec_ref(v_minorFVars_x27_1263_);
lean_dec_ref(v_minorFVars_1262_);
lean_dec_ref(v_motiveFVars_1261_);
v_a_1283_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1277_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1277_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop___redArg___lam__0___closed__0));
v___x_1293_ = l_Lean_stringToMessageData(v___x_1292_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop___redArg___lam__0(lean_object* v_xs_1294_, lean_object* v_motiveFVars_1295_, uint8_t v___x_1296_, lean_object* v_i_1297_, lean_object* v_minors_1298_, lean_object* v_minorFVars_1299_, lean_object* v_minorFVars_x27_1300_, lean_object* v_k_1301_, lean_object* v_xs_x27_1302_, lean_object* v_x_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = lean_obj_once(&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___lam__0___closed__2, &l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___lam__0___closed__2_once, _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___lam__0___closed__2);
v___x_1310_ = lean_unsigned_to_nat(1u);
v___x_1311_ = l_Lean_Meta_mkNumeral(v___x_1309_, v___x_1310_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; size_t v_sz_1317_; size_t v___x_1318_; lean_object* v___x_1319_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_a_1312_);
lean_dec_ref(v___x_1311_);
v___x_1313_ = lean_unsigned_to_nat(0u);
v___x_1314_ = lean_array_get_size(v_xs_x27_1302_);
lean_inc_ref(v_xs_x27_1302_);
v___x_1315_ = l_Array_toSubarray___redArg(v_xs_x27_1302_, v___x_1313_, v___x_1314_);
v___x_1316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1316_, 0, v_a_1312_);
lean_ctor_set(v___x_1316_, 1, v___x_1315_);
v_sz_1317_ = lean_array_size(v_xs_1294_);
v___x_1318_ = ((size_t)0ULL);
lean_inc_ref(v_motiveFVars_1295_);
v___x_1319_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop_spec__0(v_motiveFVars_1295_, v_xs_1294_, v_xs_x27_1302_, v_xs_1294_, v_sz_1317_, v___x_1318_, v___x_1316_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; lean_object* v_fst_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1371_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_a_1320_);
lean_dec_ref(v___x_1319_);
v_fst_1321_ = lean_ctor_get(v_a_1320_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v_a_1320_);
if (v_isSharedCheck_1371_ == 0)
{
lean_object* v_unused_1372_; 
v_unused_1372_ = lean_ctor_get(v_a_1320_, 1);
lean_dec(v_unused_1372_);
v___x_1323_ = v_a_1320_;
v_isShared_1324_ = v_isSharedCheck_1371_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_fst_1321_);
lean_dec(v_a_1320_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1371_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
uint8_t v___x_1325_; uint8_t v___x_1326_; lean_object* v___x_1327_; 
v___x_1325_ = 0;
v___x_1326_ = 1;
v___x_1327_ = l_Lean_Meta_mkLambdaFVars(v_xs_x27_1302_, v_fst_1321_, v___x_1325_, v___x_1296_, v___x_1325_, v___x_1296_, v___x_1326_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
lean_dec_ref(v_xs_x27_1302_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_a_1328_);
lean_dec_ref(v___x_1327_);
v___x_1337_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__2));
v___x_1338_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__0___redArg(v___x_1337_, v___y_1306_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v_a_1339_; uint8_t v___x_1340_; 
v_a_1339_ = lean_ctor_get(v___x_1338_, 0);
lean_inc(v_a_1339_);
lean_dec_ref(v___x_1338_);
v___x_1340_ = lean_unbox(v_a_1339_);
lean_dec(v_a_1339_);
if (v___x_1340_ == 0)
{
lean_del_object(v___x_1323_);
v___y_1330_ = v___y_1304_;
v___y_1331_ = v___y_1305_;
v___y_1332_ = v___y_1306_;
v___y_1333_ = v___y_1307_;
goto v___jp_1329_;
}
else
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1344_; 
v___x_1341_ = lean_obj_once(&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop___redArg___lam__0___closed__1, &l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop___redArg___lam__0___closed__1);
lean_inc(v_a_1328_);
v___x_1342_ = l_Lean_MessageData_ofExpr(v_a_1328_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set_tag(v___x_1323_, 7);
lean_ctor_set(v___x_1323_, 1, v___x_1342_);
lean_ctor_set(v___x_1323_, 0, v___x_1341_);
v___x_1344_ = v___x_1323_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1341_);
lean_ctor_set(v_reuseFailAlloc_1354_, 1, v___x_1342_);
v___x_1344_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
lean_object* v___x_1345_; 
v___x_1345_ = l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1(v___x_1337_, v___x_1344_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_dec_ref(v___x_1345_);
v___y_1330_ = v___y_1304_;
v___y_1331_ = v___y_1305_;
v___y_1332_ = v___y_1306_;
v___y_1333_ = v___y_1307_;
goto v___jp_1329_;
}
else
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
lean_dec(v_a_1328_);
lean_dec_ref(v_k_1301_);
lean_dec_ref(v_minorFVars_x27_1300_);
lean_dec_ref(v_minorFVars_1299_);
lean_dec_ref(v_minors_1298_);
lean_dec_ref(v_motiveFVars_1295_);
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1345_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1345_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1346_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
}
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
lean_dec(v_a_1328_);
lean_del_object(v___x_1323_);
lean_dec_ref(v_k_1301_);
lean_dec_ref(v_minorFVars_x27_1300_);
lean_dec_ref(v_minorFVars_1299_);
lean_dec_ref(v_minors_1298_);
lean_dec_ref(v_motiveFVars_1295_);
v_a_1355_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1338_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1338_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
v___jp_1329_:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1334_ = lean_nat_add(v_i_1297_, v___x_1310_);
v___x_1335_ = lean_array_push(v_minors_1298_, v_a_1328_);
v___x_1336_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop___redArg(v_motiveFVars_1295_, v_minorFVars_1299_, v_minorFVars_x27_1300_, v_k_1301_, v___x_1334_, v___x_1335_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
return v___x_1336_;
}
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
lean_del_object(v___x_1323_);
lean_dec_ref(v_k_1301_);
lean_dec_ref(v_minorFVars_x27_1300_);
lean_dec_ref(v_minorFVars_1299_);
lean_dec_ref(v_minors_1298_);
lean_dec_ref(v_motiveFVars_1295_);
v_a_1363_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1327_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1327_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
lean_dec_ref(v_xs_x27_1302_);
lean_dec_ref(v_k_1301_);
lean_dec_ref(v_minorFVars_x27_1300_);
lean_dec_ref(v_minorFVars_1299_);
lean_dec_ref(v_minors_1298_);
lean_dec_ref(v_motiveFVars_1295_);
v_a_1373_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1375_ = v___x_1319_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1319_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
lean_dec_ref(v_xs_x27_1302_);
lean_dec_ref(v_k_1301_);
lean_dec_ref(v_minorFVars_x27_1300_);
lean_dec_ref(v_minorFVars_1299_);
lean_dec_ref(v_minors_1298_);
lean_dec_ref(v_motiveFVars_1295_);
v_a_1381_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1311_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1311_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop___redArg___lam__0___boxed(lean_object* v_xs_1389_, lean_object* v_motiveFVars_1390_, lean_object* v___x_1391_, lean_object* v_i_1392_, lean_object* v_minors_1393_, lean_object* v_minorFVars_1394_, lean_object* v_minorFVars_x27_1395_, lean_object* v_k_1396_, lean_object* v_xs_x27_1397_, lean_object* v_x_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
uint8_t v___x_5601__boxed_1404_; lean_object* v_res_1405_; 
v___x_5601__boxed_1404_ = lean_unbox(v___x_1391_);
v_res_1405_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop___redArg___lam__0(v_xs_1389_, v_motiveFVars_1390_, v___x_5601__boxed_1404_, v_i_1392_, v_minors_1393_, v_minorFVars_1394_, v_minorFVars_x27_1395_, v_k_1396_, v_xs_x27_1397_, v_x_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec_ref(v_x_1398_);
lean_dec(v_i_1392_);
lean_dec_ref(v_xs_1389_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop___redArg___lam__1(lean_object* v___x_1406_, lean_object* v_minorFVars_x27_1407_, lean_object* v_i_1408_, lean_object* v_motiveFVars_1409_, uint8_t v___x_1410_, lean_object* v_minors_1411_, lean_object* v_minorFVars_1412_, lean_object* v_k_1413_, lean_object* v_xs_1414_, lean_object* v_x_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = lean_array_get_borrowed(v___x_1406_, v_minorFVars_x27_1407_, v_i_1408_);
lean_inc(v___y_1419_);
lean_inc_ref(v___y_1418_);
lean_inc(v___y_1417_);
lean_inc_ref(v___y_1416_);
lean_inc(v___x_1421_);
v___x_1422_ = lean_infer_type(v___x_1421_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1424_; lean_object* v___f_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; uint8_t v___x_1428_; lean_object* v___x_1429_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1423_);
lean_dec_ref(v___x_1422_);
v___x_1424_ = lean_box(v___x_1410_);
lean_inc_ref(v_xs_1414_);
v___f_1425_ = lean_alloc_closure((void*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop___redArg___lam__0___boxed), 15, 8);
lean_closure_set(v___f_1425_, 0, v_xs_1414_);
lean_closure_set(v___f_1425_, 1, v_motiveFVars_1409_);
lean_closure_set(v___f_1425_, 2, v___x_1424_);
lean_closure_set(v___f_1425_, 3, v_i_1408_);
lean_closure_set(v___f_1425_, 4, v_minors_1411_);
lean_closure_set(v___f_1425_, 5, v_minorFVars_1412_);
lean_closure_set(v___f_1425_, 6, v_minorFVars_x27_1407_);
lean_closure_set(v___f_1425_, 7, v_k_1413_);
v___x_1426_ = lean_array_get_size(v_xs_1414_);
lean_dec_ref(v_xs_1414_);
v___x_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
v___x_1428_ = 0;
v___x_1429_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop_spec__1___redArg(v_a_1423_, v___x_1427_, v___f_1425_, v___x_1428_, v___x_1428_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
return v___x_1429_;
}
else
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
lean_dec_ref(v_xs_1414_);
lean_dec_ref(v_k_1413_);
lean_dec_ref(v_minorFVars_1412_);
lean_dec_ref(v_minors_1411_);
lean_dec_ref(v_motiveFVars_1409_);
lean_dec(v_i_1408_);
lean_dec_ref(v_minorFVars_x27_1407_);
v_a_1430_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1422_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1422_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop___redArg___boxed(lean_object* v_motiveFVars_1438_, lean_object* v_minorFVars_1439_, lean_object* v_minorFVars_x27_1440_, lean_object* v_k_1441_, lean_object* v_i_1442_, lean_object* v_minors_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop___redArg(v_motiveFVars_1438_, v_minorFVars_1439_, v_minorFVars_x27_1440_, v_k_1441_, v_i_1442_, v_minors_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
lean_dec(v_a_1445_);
lean_dec_ref(v_a_1444_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop(lean_object* v_00_u03b1_1450_, lean_object* v_motiveFVars_1451_, lean_object* v_minorFVars_1452_, lean_object* v_minorFVars_x27_1453_, lean_object* v_k_1454_, lean_object* v_i_1455_, lean_object* v_minors_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop___redArg(v_motiveFVars_1451_, v_minorFVars_1452_, v_minorFVars_x27_1453_, v_k_1454_, v_i_1455_, v_minors_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop___boxed(lean_object* v_00_u03b1_1463_, lean_object* v_motiveFVars_1464_, lean_object* v_minorFVars_1465_, lean_object* v_minorFVars_x27_1466_, lean_object* v_k_1467_, lean_object* v_i_1468_, lean_object* v_minors_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop(v_00_u03b1_1463_, v_motiveFVars_1464_, v_minorFVars_1465_, v_minorFVars_x27_1466_, v_k_1467_, v_i_1468_, v_minors_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_);
lean_dec(v_a_1473_);
lean_dec_ref(v_a_1472_);
lean_dec(v_a_1471_);
lean_dec_ref(v_a_1470_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_spec__0___redArg(lean_object* v_msg_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v___f_1483_; lean_object* v___x_138__overap_1484_; lean_object* v___x_1485_; 
v___f_1483_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_spec__0___redArg___closed__0));
v___x_138__overap_1484_ = lean_panic_fn(v___f_1483_, v_msg_1477_);
lean_inc(v___y_1481_);
lean_inc_ref(v___y_1480_);
lean_inc(v___y_1479_);
lean_inc_ref(v___y_1478_);
v___x_1485_ = lean_apply_5(v___x_138__overap_1484_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, lean_box(0));
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_spec__0___redArg___boxed(lean_object* v_msg_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_panic___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_spec__0___redArg(v_msg_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_spec__0(lean_object* v_00_u03b1_1493_, lean_object* v_msg_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_panic___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_spec__0___redArg(v_msg_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_spec__0___boxed(lean_object* v_00_u03b1_1501_, lean_object* v_msg_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_panic___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_spec__0(v_00_u03b1_1501_, v_msg_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
return v_res_1508_;
}
}
static lean_object* _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors___redArg___closed__3(void){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1512_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors___redArg___closed__2));
v___x_1513_ = lean_unsigned_to_nat(2u);
v___x_1514_ = lean_unsigned_to_nat(103u);
v___x_1515_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors___redArg___closed__1));
v___x_1516_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors___redArg___closed__0));
v___x_1517_ = l_mkPanicMessageWithDecl(v___x_1516_, v___x_1515_, v___x_1514_, v___x_1513_, v___x_1512_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors___redArg(lean_object* v_motiveFVars_1518_, lean_object* v_minorFVars_1519_, lean_object* v_minorFVars_x27_1520_, lean_object* v_k_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; uint8_t v___x_1529_; 
v___x_1527_ = lean_array_get_size(v_minorFVars_1519_);
v___x_1528_ = lean_array_get_size(v_minorFVars_x27_1520_);
v___x_1529_ = lean_nat_dec_eq(v___x_1527_, v___x_1528_);
if (v___x_1529_ == 0)
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
lean_dec_ref(v_k_1521_);
lean_dec_ref(v_minorFVars_x27_1520_);
lean_dec_ref(v_minorFVars_1519_);
lean_dec_ref(v_motiveFVars_1518_);
v___x_1530_ = lean_obj_once(&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors___redArg___closed__3, &l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors___redArg___closed__3_once, _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors___redArg___closed__3);
v___x_1531_ = l_panic___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_spec__0___redArg(v___x_1530_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_);
return v___x_1531_;
}
else
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1532_ = lean_unsigned_to_nat(0u);
v___x_1533_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances___redArg___closed__0));
v___x_1534_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop___redArg(v_motiveFVars_1518_, v_minorFVars_1519_, v_minorFVars_x27_1520_, v_k_1521_, v___x_1532_, v___x_1533_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_);
return v___x_1534_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors___redArg___boxed(lean_object* v_motiveFVars_1535_, lean_object* v_minorFVars_1536_, lean_object* v_minorFVars_x27_1537_, lean_object* v_k_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors___redArg(v_motiveFVars_1535_, v_minorFVars_1536_, v_minorFVars_x27_1537_, v_k_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_);
lean_dec(v_a_1542_);
lean_dec_ref(v_a_1541_);
lean_dec(v_a_1540_);
lean_dec_ref(v_a_1539_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors(lean_object* v_00_u03b1_1545_, lean_object* v_motiveFVars_1546_, lean_object* v_minorFVars_1547_, lean_object* v_minorFVars_x27_1548_, lean_object* v_k_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors___redArg(v_motiveFVars_1546_, v_minorFVars_1547_, v_minorFVars_x27_1548_, v_k_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors___boxed(lean_object* v_00_u03b1_1556_, lean_object* v_motiveFVars_1557_, lean_object* v_minorFVars_1558_, lean_object* v_minorFVars_x27_1559_, lean_object* v_k_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors(v_00_u03b1_1556_, v_motiveFVars_1557_, v_minorFVars_1558_, v_minorFVars_x27_1559_, v_k_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
lean_dec(v_a_1564_);
lean_dec_ref(v_a_1563_);
lean_dec(v_a_1562_);
lean_dec_ref(v_a_1561_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___lam__0(lean_object* v___y_1567_, uint8_t v_isExporting_1568_, lean_object* v___x_1569_, lean_object* v___y_1570_, lean_object* v___x_1571_, lean_object* v_a_x3f_1572_){
_start:
{
lean_object* v___x_1574_; lean_object* v_env_1575_; lean_object* v_nextMacroScope_1576_; lean_object* v_ngen_1577_; lean_object* v_auxDeclNGen_1578_; lean_object* v_traceState_1579_; lean_object* v_messages_1580_; lean_object* v_infoState_1581_; lean_object* v_snapshotTasks_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1607_; 
v___x_1574_ = lean_st_ref_take(v___y_1567_);
v_env_1575_ = lean_ctor_get(v___x_1574_, 0);
v_nextMacroScope_1576_ = lean_ctor_get(v___x_1574_, 1);
v_ngen_1577_ = lean_ctor_get(v___x_1574_, 2);
v_auxDeclNGen_1578_ = lean_ctor_get(v___x_1574_, 3);
v_traceState_1579_ = lean_ctor_get(v___x_1574_, 4);
v_messages_1580_ = lean_ctor_get(v___x_1574_, 6);
v_infoState_1581_ = lean_ctor_get(v___x_1574_, 7);
v_snapshotTasks_1582_ = lean_ctor_get(v___x_1574_, 8);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1607_ == 0)
{
lean_object* v_unused_1608_; 
v_unused_1608_ = lean_ctor_get(v___x_1574_, 5);
lean_dec(v_unused_1608_);
v___x_1584_ = v___x_1574_;
v_isShared_1585_ = v_isSharedCheck_1607_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_snapshotTasks_1582_);
lean_inc(v_infoState_1581_);
lean_inc(v_messages_1580_);
lean_inc(v_traceState_1579_);
lean_inc(v_auxDeclNGen_1578_);
lean_inc(v_ngen_1577_);
lean_inc(v_nextMacroScope_1576_);
lean_inc(v_env_1575_);
lean_dec(v___x_1574_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1607_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1586_; lean_object* v___x_1588_; 
v___x_1586_ = l_Lean_Environment_setExporting(v_env_1575_, v_isExporting_1568_);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 5, v___x_1569_);
lean_ctor_set(v___x_1584_, 0, v___x_1586_);
v___x_1588_ = v___x_1584_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1586_);
lean_ctor_set(v_reuseFailAlloc_1606_, 1, v_nextMacroScope_1576_);
lean_ctor_set(v_reuseFailAlloc_1606_, 2, v_ngen_1577_);
lean_ctor_set(v_reuseFailAlloc_1606_, 3, v_auxDeclNGen_1578_);
lean_ctor_set(v_reuseFailAlloc_1606_, 4, v_traceState_1579_);
lean_ctor_set(v_reuseFailAlloc_1606_, 5, v___x_1569_);
lean_ctor_set(v_reuseFailAlloc_1606_, 6, v_messages_1580_);
lean_ctor_set(v_reuseFailAlloc_1606_, 7, v_infoState_1581_);
lean_ctor_set(v_reuseFailAlloc_1606_, 8, v_snapshotTasks_1582_);
v___x_1588_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v_mctx_1591_; lean_object* v_zetaDeltaFVarIds_1592_; lean_object* v_postponed_1593_; lean_object* v_diag_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1604_; 
v___x_1589_ = lean_st_ref_set(v___y_1567_, v___x_1588_);
v___x_1590_ = lean_st_ref_take(v___y_1570_);
v_mctx_1591_ = lean_ctor_get(v___x_1590_, 0);
v_zetaDeltaFVarIds_1592_ = lean_ctor_get(v___x_1590_, 2);
v_postponed_1593_ = lean_ctor_get(v___x_1590_, 3);
v_diag_1594_ = lean_ctor_get(v___x_1590_, 4);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1604_ == 0)
{
lean_object* v_unused_1605_; 
v_unused_1605_ = lean_ctor_get(v___x_1590_, 1);
lean_dec(v_unused_1605_);
v___x_1596_ = v___x_1590_;
v_isShared_1597_ = v_isSharedCheck_1604_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_diag_1594_);
lean_inc(v_postponed_1593_);
lean_inc(v_zetaDeltaFVarIds_1592_);
lean_inc(v_mctx_1591_);
lean_dec(v___x_1590_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1604_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 1, v___x_1571_);
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_mctx_1591_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v___x_1571_);
lean_ctor_set(v_reuseFailAlloc_1603_, 2, v_zetaDeltaFVarIds_1592_);
lean_ctor_set(v_reuseFailAlloc_1603_, 3, v_postponed_1593_);
lean_ctor_set(v_reuseFailAlloc_1603_, 4, v_diag_1594_);
v___x_1599_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1600_ = lean_st_ref_set(v___y_1570_, v___x_1599_);
v___x_1601_ = lean_box(0);
v___x_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
return v___x_1602_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___lam__0___boxed(lean_object* v___y_1609_, lean_object* v_isExporting_1610_, lean_object* v___x_1611_, lean_object* v___y_1612_, lean_object* v___x_1613_, lean_object* v_a_x3f_1614_, lean_object* v___y_1615_){
_start:
{
uint8_t v_isExporting_boxed_1616_; lean_object* v_res_1617_; 
v_isExporting_boxed_1616_ = lean_unbox(v_isExporting_1610_);
v_res_1617_ = l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___lam__0(v___y_1609_, v_isExporting_boxed_1616_, v___x_1611_, v___y_1612_, v___x_1613_, v_a_x3f_1614_);
lean_dec(v_a_x3f_1614_);
lean_dec(v___y_1612_);
lean_dec(v___y_1609_);
return v_res_1617_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1618_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___closed__0);
v___x_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1619_);
return v___x_1620_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___closed__1);
v___x_1622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
return v___x_1622_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1623_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___closed__1);
v___x_1624_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1623_);
lean_ctor_set(v___x_1624_, 1, v___x_1623_);
lean_ctor_set(v___x_1624_, 2, v___x_1623_);
lean_ctor_set(v___x_1624_, 3, v___x_1623_);
lean_ctor_set(v___x_1624_, 4, v___x_1623_);
lean_ctor_set(v___x_1624_, 5, v___x_1623_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg(lean_object* v_x_1625_, uint8_t v_isExporting_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v___x_1632_; lean_object* v_env_1633_; uint8_t v_isExporting_1634_; lean_object* v___x_1635_; lean_object* v_env_1636_; lean_object* v_nextMacroScope_1637_; lean_object* v_ngen_1638_; lean_object* v_auxDeclNGen_1639_; lean_object* v_traceState_1640_; lean_object* v_messages_1641_; lean_object* v_infoState_1642_; lean_object* v_snapshotTasks_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1697_; 
v___x_1632_ = lean_st_ref_get(v___y_1630_);
v_env_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc_ref(v_env_1633_);
lean_dec(v___x_1632_);
v_isExporting_1634_ = lean_ctor_get_uint8(v_env_1633_, sizeof(void*)*8);
lean_dec_ref(v_env_1633_);
v___x_1635_ = lean_st_ref_take(v___y_1630_);
v_env_1636_ = lean_ctor_get(v___x_1635_, 0);
v_nextMacroScope_1637_ = lean_ctor_get(v___x_1635_, 1);
v_ngen_1638_ = lean_ctor_get(v___x_1635_, 2);
v_auxDeclNGen_1639_ = lean_ctor_get(v___x_1635_, 3);
v_traceState_1640_ = lean_ctor_get(v___x_1635_, 4);
v_messages_1641_ = lean_ctor_get(v___x_1635_, 6);
v_infoState_1642_ = lean_ctor_get(v___x_1635_, 7);
v_snapshotTasks_1643_ = lean_ctor_get(v___x_1635_, 8);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1697_ == 0)
{
lean_object* v_unused_1698_; 
v_unused_1698_ = lean_ctor_get(v___x_1635_, 5);
lean_dec(v_unused_1698_);
v___x_1645_ = v___x_1635_;
v_isShared_1646_ = v_isSharedCheck_1697_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_snapshotTasks_1643_);
lean_inc(v_infoState_1642_);
lean_inc(v_messages_1641_);
lean_inc(v_traceState_1640_);
lean_inc(v_auxDeclNGen_1639_);
lean_inc(v_ngen_1638_);
lean_inc(v_nextMacroScope_1637_);
lean_inc(v_env_1636_);
lean_dec(v___x_1635_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1697_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1650_; 
v___x_1647_ = l_Lean_Environment_setExporting(v_env_1636_, v_isExporting_1626_);
v___x_1648_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___closed__2);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 5, v___x_1648_);
lean_ctor_set(v___x_1645_, 0, v___x_1647_);
v___x_1650_ = v___x_1645_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1647_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_nextMacroScope_1637_);
lean_ctor_set(v_reuseFailAlloc_1696_, 2, v_ngen_1638_);
lean_ctor_set(v_reuseFailAlloc_1696_, 3, v_auxDeclNGen_1639_);
lean_ctor_set(v_reuseFailAlloc_1696_, 4, v_traceState_1640_);
lean_ctor_set(v_reuseFailAlloc_1696_, 5, v___x_1648_);
lean_ctor_set(v_reuseFailAlloc_1696_, 6, v_messages_1641_);
lean_ctor_set(v_reuseFailAlloc_1696_, 7, v_infoState_1642_);
lean_ctor_set(v_reuseFailAlloc_1696_, 8, v_snapshotTasks_1643_);
v___x_1650_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v_mctx_1653_; lean_object* v_zetaDeltaFVarIds_1654_; lean_object* v_postponed_1655_; lean_object* v_diag_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1694_; 
v___x_1651_ = lean_st_ref_set(v___y_1630_, v___x_1650_);
v___x_1652_ = lean_st_ref_take(v___y_1628_);
v_mctx_1653_ = lean_ctor_get(v___x_1652_, 0);
v_zetaDeltaFVarIds_1654_ = lean_ctor_get(v___x_1652_, 2);
v_postponed_1655_ = lean_ctor_get(v___x_1652_, 3);
v_diag_1656_ = lean_ctor_get(v___x_1652_, 4);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1694_ == 0)
{
lean_object* v_unused_1695_; 
v_unused_1695_ = lean_ctor_get(v___x_1652_, 1);
lean_dec(v_unused_1695_);
v___x_1658_ = v___x_1652_;
v_isShared_1659_ = v_isSharedCheck_1694_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_diag_1656_);
lean_inc(v_postponed_1655_);
lean_inc(v_zetaDeltaFVarIds_1654_);
lean_inc(v_mctx_1653_);
lean_dec(v___x_1652_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1694_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1660_; lean_object* v___x_1662_; 
v___x_1660_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___closed__3);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 1, v___x_1660_);
v___x_1662_ = v___x_1658_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_mctx_1653_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v___x_1660_);
lean_ctor_set(v_reuseFailAlloc_1693_, 2, v_zetaDeltaFVarIds_1654_);
lean_ctor_set(v_reuseFailAlloc_1693_, 3, v_postponed_1655_);
lean_ctor_set(v_reuseFailAlloc_1693_, 4, v_diag_1656_);
v___x_1662_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
lean_object* v___x_1663_; lean_object* v_r_1664_; 
v___x_1663_ = lean_st_ref_set(v___y_1628_, v___x_1662_);
lean_inc(v___y_1630_);
lean_inc_ref(v___y_1629_);
lean_inc(v___y_1628_);
lean_inc_ref(v___y_1627_);
v_r_1664_ = lean_apply_5(v_x_1625_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, lean_box(0));
if (lean_obj_tag(v_r_1664_) == 0)
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1681_; 
v_a_1665_ = lean_ctor_get(v_r_1664_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v_r_1664_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1667_ = v_r_1664_;
v_isShared_1668_ = v_isSharedCheck_1681_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v_r_1664_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1681_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
lean_inc(v_a_1665_);
if (v_isShared_1668_ == 0)
{
lean_ctor_set_tag(v___x_1667_, 1);
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
lean_object* v___x_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
v___x_1671_ = l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___lam__0(v___y_1630_, v_isExporting_1634_, v___x_1648_, v___y_1628_, v___x_1660_, v___x_1670_);
lean_dec_ref(v___x_1670_);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1678_ == 0)
{
lean_object* v_unused_1679_; 
v_unused_1679_ = lean_ctor_get(v___x_1671_, 0);
lean_dec(v_unused_1679_);
v___x_1673_ = v___x_1671_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_dec(v___x_1671_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v_a_1665_);
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_a_1665_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
}
else
{
lean_object* v_a_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1691_; 
v_a_1682_ = lean_ctor_get(v_r_1664_, 0);
lean_inc(v_a_1682_);
lean_dec_ref(v_r_1664_);
v___x_1683_ = lean_box(0);
v___x_1684_ = l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___lam__0(v___y_1630_, v_isExporting_1634_, v___x_1648_, v___y_1628_, v___x_1660_, v___x_1683_);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1691_ == 0)
{
lean_object* v_unused_1692_; 
v_unused_1692_ = lean_ctor_get(v___x_1684_, 0);
lean_dec(v_unused_1692_);
v___x_1686_ = v___x_1684_;
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
else
{
lean_dec(v___x_1684_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1689_; 
if (v_isShared_1687_ == 0)
{
lean_ctor_set_tag(v___x_1686_, 1);
lean_ctor_set(v___x_1686_, 0, v_a_1682_);
v___x_1689_ = v___x_1686_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_a_1682_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg___boxed(lean_object* v_x_1699_, lean_object* v_isExporting_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
uint8_t v_isExporting_boxed_1706_; lean_object* v_res_1707_; 
v_isExporting_boxed_1706_ = lean_unbox(v_isExporting_1700_);
v_res_1707_ = l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg(v_x_1699_, v_isExporting_boxed_1706_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2(lean_object* v_00_u03b1_1708_, lean_object* v_x_1709_, uint8_t v_isExporting_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v___x_1716_; 
v___x_1716_ = l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg(v_x_1709_, v_isExporting_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___boxed(lean_object* v_00_u03b1_1717_, lean_object* v_x_1718_, lean_object* v_isExporting_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
uint8_t v_isExporting_boxed_1725_; lean_object* v_res_1726_; 
v_isExporting_boxed_1725_ = lean_unbox(v_isExporting_1719_);
v_res_1726_ = l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2(v_00_u03b1_1717_, v_x_1718_, v_isExporting_boxed_1725_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFn___lam__0(lean_object* v___x_1727_, uint8_t v___x_1728_, lean_object* v_declName_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Lean_addDecl(v___x_1727_, v___x_1728_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v___x_1736_; 
lean_dec_ref(v___x_1735_);
v___x_1736_ = l_Lean_enableRealizationsForConst(v_declName_1729_, v___y_1732_, v___y_1733_);
return v___x_1736_;
}
else
{
lean_dec_ref(v___y_1732_);
lean_dec(v_declName_1729_);
return v___x_1735_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFn___lam__0___boxed(lean_object* v___x_1737_, lean_object* v___x_1738_, lean_object* v_declName_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
uint8_t v___x_7486__boxed_1745_; lean_object* v_res_1746_; 
v___x_7486__boxed_1745_ = lean_unbox(v___x_1738_);
v_res_1746_ = l_Lean_Meta_mkSizeOfFn___lam__0(v___x_1737_, v___x_7486__boxed_1745_, v_declName_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
lean_dec(v___y_1743_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
return v_res_1746_;
}
}
static lean_object* _init_l_Lean_Meta_mkSizeOfFn___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1748_ = ((lean_object*)(l_Lean_Meta_mkSizeOfFn___lam__1___closed__0));
v___x_1749_ = l_Lean_stringToMessageData(v___x_1748_);
return v___x_1749_;
}
}
static lean_object* _init_l_Lean_Meta_mkSizeOfFn___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = ((lean_object*)(l_Lean_Meta_mkSizeOfFn___lam__1___closed__2));
v___x_1752_ = l_Lean_stringToMessageData(v___x_1751_);
return v___x_1752_;
}
}
static lean_object* _init_l_Lean_Meta_mkSizeOfFn___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1754_ = ((lean_object*)(l_Lean_Meta_mkSizeOfFn___lam__1___closed__4));
v___x_1755_ = l_Lean_stringToMessageData(v___x_1754_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFn___lam__1(lean_object* v___x_1756_, lean_object* v___x_1757_, uint8_t v___x_1758_, uint8_t v___x_1759_, uint8_t v___x_1760_, lean_object* v_minors_1761_, lean_object* v___x_1762_, lean_object* v___x_1763_, lean_object* v___x_1764_, lean_object* v_cls_1765_, lean_object* v_declName_1766_, lean_object* v___x_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = l_Lean_Meta_mkForallFVars(v___x_1756_, v___x_1757_, v___x_1758_, v___x_1759_, v___x_1759_, v___x_1760_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_a_1774_);
lean_dec_ref(v___x_1773_);
v___x_1775_ = l_Array_append___redArg(v_minors_1761_, v___x_1762_);
v___x_1776_ = l_Array_append___redArg(v___x_1775_, v___x_1763_);
v___x_1777_ = l_Lean_mkAppN(v___x_1764_, v___x_1776_);
lean_dec_ref(v___x_1776_);
v___x_1778_ = l_Lean_Meta_mkLambdaFVars(v___x_1756_, v___x_1777_, v___x_1758_, v___x_1759_, v___x_1758_, v___x_1759_, v___x_1760_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_a_1779_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___x_1819_; lean_object* v_a_1820_; uint8_t v___x_1821_; 
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_a_1779_);
lean_dec_ref(v___x_1778_);
lean_inc(v_cls_1765_);
v___x_1819_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__0___redArg(v_cls_1765_, v___y_1770_);
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_a_1820_);
lean_dec_ref(v___x_1819_);
v___x_1821_ = lean_unbox(v_a_1820_);
lean_dec(v_a_1820_);
if (v___x_1821_ == 0)
{
v___y_1808_ = v___y_1768_;
v___y_1809_ = v___y_1769_;
v___y_1810_ = v___y_1770_;
v___y_1811_ = v___y_1771_;
goto v___jp_1807_;
}
else
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1822_ = lean_obj_once(&l_Lean_Meta_mkSizeOfFn___lam__1___closed__5, &l_Lean_Meta_mkSizeOfFn___lam__1___closed__5_once, _init_l_Lean_Meta_mkSizeOfFn___lam__1___closed__5);
lean_inc(v_declName_1766_);
v___x_1823_ = l_Lean_MessageData_ofName(v_declName_1766_);
v___x_1824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1822_);
lean_ctor_set(v___x_1824_, 1, v___x_1823_);
lean_inc(v_cls_1765_);
v___x_1825_ = l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1(v_cls_1765_, v___x_1824_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_dec_ref(v___x_1825_);
v___y_1808_ = v___y_1768_;
v___y_1809_ = v___y_1769_;
v___y_1810_ = v___y_1770_;
v___y_1811_ = v___y_1771_;
goto v___jp_1807_;
}
else
{
lean_dec(v_a_1779_);
lean_dec(v_a_1774_);
lean_dec(v___x_1767_);
lean_dec(v_declName_1766_);
lean_dec(v_cls_1765_);
return v___x_1825_;
}
}
v___jp_1780_:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; uint8_t v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___f_1793_; lean_object* v___x_1794_; 
lean_inc(v_declName_1766_);
v___x_1785_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1785_, 0, v_declName_1766_);
lean_ctor_set(v___x_1785_, 1, v___x_1767_);
lean_ctor_set(v___x_1785_, 2, v_a_1774_);
v___x_1786_ = lean_box(1);
v___x_1787_ = 1;
v___x_1788_ = lean_box(0);
lean_inc(v_declName_1766_);
v___x_1789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1789_, 0, v_declName_1766_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
v___x_1790_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1790_, 0, v___x_1785_);
lean_ctor_set(v___x_1790_, 1, v_a_1779_);
lean_ctor_set(v___x_1790_, 2, v___x_1786_);
lean_ctor_set(v___x_1790_, 3, v___x_1789_);
lean_ctor_set_uint8(v___x_1790_, sizeof(void*)*4, v___x_1787_);
v___x_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1790_);
v___x_1792_ = lean_box(v___x_1758_);
v___f_1793_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSizeOfFn___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1793_, 0, v___x_1791_);
lean_closure_set(v___f_1793_, 1, v___x_1792_);
lean_closure_set(v___f_1793_, 2, v_declName_1766_);
v___x_1794_ = l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg(v___f_1793_, v___x_1759_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
return v___x_1794_;
}
v___jp_1795_:
{
lean_object* v___x_1800_; lean_object* v_a_1801_; uint8_t v___x_1802_; 
lean_inc(v_cls_1765_);
v___x_1800_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__0___redArg(v_cls_1765_, v___y_1798_);
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
lean_inc(v_a_1801_);
lean_dec_ref(v___x_1800_);
v___x_1802_ = lean_unbox(v_a_1801_);
lean_dec(v_a_1801_);
if (v___x_1802_ == 0)
{
lean_dec(v_cls_1765_);
v___y_1781_ = v___y_1796_;
v___y_1782_ = v___y_1797_;
v___y_1783_ = v___y_1798_;
v___y_1784_ = v___y_1799_;
goto v___jp_1780_;
}
else
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1803_ = lean_obj_once(&l_Lean_Meta_mkSizeOfFn___lam__1___closed__1, &l_Lean_Meta_mkSizeOfFn___lam__1___closed__1_once, _init_l_Lean_Meta_mkSizeOfFn___lam__1___closed__1);
lean_inc(v_a_1779_);
v___x_1804_ = l_Lean_MessageData_ofExpr(v_a_1779_);
v___x_1805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1803_);
lean_ctor_set(v___x_1805_, 1, v___x_1804_);
v___x_1806_ = l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1(v_cls_1765_, v___x_1805_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_dec_ref(v___x_1806_);
v___y_1781_ = v___y_1796_;
v___y_1782_ = v___y_1797_;
v___y_1783_ = v___y_1798_;
v___y_1784_ = v___y_1799_;
goto v___jp_1780_;
}
else
{
lean_dec(v_a_1779_);
lean_dec(v_a_1774_);
lean_dec(v___x_1767_);
lean_dec(v_declName_1766_);
return v___x_1806_;
}
}
}
v___jp_1807_:
{
lean_object* v___x_1812_; lean_object* v_a_1813_; uint8_t v___x_1814_; 
lean_inc(v_cls_1765_);
v___x_1812_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__0___redArg(v_cls_1765_, v___y_1810_);
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_a_1813_);
lean_dec_ref(v___x_1812_);
v___x_1814_ = lean_unbox(v_a_1813_);
lean_dec(v_a_1813_);
if (v___x_1814_ == 0)
{
v___y_1796_ = v___y_1808_;
v___y_1797_ = v___y_1809_;
v___y_1798_ = v___y_1810_;
v___y_1799_ = v___y_1811_;
goto v___jp_1795_;
}
else
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1815_ = lean_obj_once(&l_Lean_Meta_mkSizeOfFn___lam__1___closed__3, &l_Lean_Meta_mkSizeOfFn___lam__1___closed__3_once, _init_l_Lean_Meta_mkSizeOfFn___lam__1___closed__3);
lean_inc(v_a_1774_);
v___x_1816_ = l_Lean_MessageData_ofExpr(v_a_1774_);
v___x_1817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1815_);
lean_ctor_set(v___x_1817_, 1, v___x_1816_);
lean_inc(v_cls_1765_);
v___x_1818_ = l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1(v_cls_1765_, v___x_1817_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_dec_ref(v___x_1818_);
v___y_1796_ = v___y_1808_;
v___y_1797_ = v___y_1809_;
v___y_1798_ = v___y_1810_;
v___y_1799_ = v___y_1811_;
goto v___jp_1795_;
}
else
{
lean_dec(v_a_1779_);
lean_dec(v_a_1774_);
lean_dec(v___x_1767_);
lean_dec(v_declName_1766_);
lean_dec(v_cls_1765_);
return v___x_1818_;
}
}
}
}
else
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
lean_dec(v_a_1774_);
lean_dec(v___x_1767_);
lean_dec(v_declName_1766_);
lean_dec(v_cls_1765_);
v_a_1826_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1778_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1778_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
else
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1841_; 
lean_dec(v___x_1767_);
lean_dec(v_declName_1766_);
lean_dec(v_cls_1765_);
lean_dec_ref(v___x_1764_);
lean_dec_ref(v_minors_1761_);
v_a_1834_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1836_ = v___x_1773_;
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1773_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1839_; 
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
return v___x_1839_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFn___lam__1___boxed(lean_object** _args){
lean_object* v___x_1842_ = _args[0];
lean_object* v___x_1843_ = _args[1];
lean_object* v___x_1844_ = _args[2];
lean_object* v___x_1845_ = _args[3];
lean_object* v___x_1846_ = _args[4];
lean_object* v_minors_1847_ = _args[5];
lean_object* v___x_1848_ = _args[6];
lean_object* v___x_1849_ = _args[7];
lean_object* v___x_1850_ = _args[8];
lean_object* v_cls_1851_ = _args[9];
lean_object* v_declName_1852_ = _args[10];
lean_object* v___x_1853_ = _args[11];
lean_object* v___y_1854_ = _args[12];
lean_object* v___y_1855_ = _args[13];
lean_object* v___y_1856_ = _args[14];
lean_object* v___y_1857_ = _args[15];
lean_object* v___y_1858_ = _args[16];
_start:
{
uint8_t v___x_7532__boxed_1859_; uint8_t v___x_7533__boxed_1860_; uint8_t v___x_7534__boxed_1861_; lean_object* v_res_1862_; 
v___x_7532__boxed_1859_ = lean_unbox(v___x_1844_);
v___x_7533__boxed_1860_ = lean_unbox(v___x_1845_);
v___x_7534__boxed_1861_ = lean_unbox(v___x_1846_);
v_res_1862_ = l_Lean_Meta_mkSizeOfFn___lam__1(v___x_1842_, v___x_1843_, v___x_7532__boxed_1859_, v___x_7533__boxed_1860_, v___x_7534__boxed_1861_, v_minors_1847_, v___x_1848_, v___x_1849_, v___x_1850_, v_cls_1851_, v_declName_1852_, v___x_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec_ref(v___x_1849_);
lean_dec_ref(v___x_1848_);
lean_dec_ref(v___x_1842_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFn___lam__2(lean_object* v___x_1863_, lean_object* v_localInsts_1864_, lean_object* v___x_1865_, lean_object* v___x_1866_, lean_object* v___x_1867_, lean_object* v___x_1868_, lean_object* v_cls_1869_, lean_object* v_declName_1870_, lean_object* v___x_1871_, lean_object* v_minors_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; uint8_t v___x_1885_; uint8_t v___x_1886_; uint8_t v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___f_1891_; lean_object* v___x_1892_; 
lean_inc_ref(v___x_1863_);
v___x_1878_ = l_Array_append___redArg(v___x_1863_, v_localInsts_1864_);
v___x_1879_ = l_Subarray_copy___redArg(v___x_1865_);
v___x_1880_ = l_Array_append___redArg(v___x_1878_, v___x_1879_);
v___x_1881_ = lean_unsigned_to_nat(1u);
v___x_1882_ = lean_mk_empty_array_with_capacity(v___x_1881_);
v___x_1883_ = lean_array_push(v___x_1882_, v___x_1866_);
v___x_1884_ = l_Array_append___redArg(v___x_1880_, v___x_1883_);
v___x_1885_ = 0;
v___x_1886_ = 1;
v___x_1887_ = 1;
v___x_1888_ = lean_box(v___x_1885_);
v___x_1889_ = lean_box(v___x_1886_);
v___x_1890_ = lean_box(v___x_1887_);
v___f_1891_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSizeOfFn___lam__1___boxed), 17, 12);
lean_closure_set(v___f_1891_, 0, v___x_1884_);
lean_closure_set(v___f_1891_, 1, v___x_1867_);
lean_closure_set(v___f_1891_, 2, v___x_1888_);
lean_closure_set(v___f_1891_, 3, v___x_1889_);
lean_closure_set(v___f_1891_, 4, v___x_1890_);
lean_closure_set(v___f_1891_, 5, v_minors_1872_);
lean_closure_set(v___f_1891_, 6, v___x_1879_);
lean_closure_set(v___f_1891_, 7, v___x_1883_);
lean_closure_set(v___f_1891_, 8, v___x_1868_);
lean_closure_set(v___f_1891_, 9, v_cls_1869_);
lean_closure_set(v___f_1891_, 10, v_declName_1870_);
lean_closure_set(v___f_1891_, 11, v___x_1871_);
v___x_1892_ = l_Lean_Meta_withInstImplicitAsImplicit___redArg(v___x_1863_, v___f_1891_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
lean_dec_ref(v___x_1863_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFn___lam__2___boxed(lean_object* v___x_1893_, lean_object* v_localInsts_1894_, lean_object* v___x_1895_, lean_object* v___x_1896_, lean_object* v___x_1897_, lean_object* v___x_1898_, lean_object* v_cls_1899_, lean_object* v_declName_1900_, lean_object* v___x_1901_, lean_object* v_minors_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Lean_Meta_mkSizeOfFn___lam__2(v___x_1893_, v_localInsts_1894_, v___x_1895_, v___x_1896_, v___x_1897_, v___x_1898_, v_cls_1899_, v_declName_1900_, v___x_1901_, v_minors_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec_ref(v_localInsts_1894_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFn___lam__3(lean_object* v___x_1909_, lean_object* v___x_1910_, lean_object* v___f_1911_, lean_object* v_minorFVars_x27_1912_, lean_object* v_x_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1919_ = l_Subarray_copy___redArg(v___x_1909_);
v___x_1920_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors___redArg(v___x_1910_, v___x_1919_, v_minorFVars_x27_1912_, v___f_1911_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFn___lam__3___boxed(lean_object* v___x_1921_, lean_object* v___x_1922_, lean_object* v___f_1923_, lean_object* v_minorFVars_x27_1924_, lean_object* v_x_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Lean_Meta_mkSizeOfFn___lam__3(v___x_1921_, v___x_1922_, v___f_1923_, v_minorFVars_x27_1924_, v_x_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec_ref(v_x_1925_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_mkSizeOfFn_spec__1(lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
if (lean_obj_tag(v_a_1932_) == 0)
{
lean_object* v___x_1934_; 
v___x_1934_ = l_List_reverse___redArg(v_a_1933_);
return v___x_1934_;
}
else
{
lean_object* v_head_1935_; lean_object* v_tail_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1945_; 
v_head_1935_ = lean_ctor_get(v_a_1932_, 0);
v_tail_1936_ = lean_ctor_get(v_a_1932_, 1);
v_isSharedCheck_1945_ = !lean_is_exclusive(v_a_1932_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1938_ = v_a_1932_;
v_isShared_1939_ = v_isSharedCheck_1945_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_tail_1936_);
lean_inc(v_head_1935_);
lean_dec(v_a_1932_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1945_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1940_; lean_object* v___x_1942_; 
v___x_1940_ = l_Lean_mkLevelParam(v_head_1935_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 1, v_a_1933_);
lean_ctor_set(v___x_1938_, 0, v___x_1940_);
v___x_1942_ = v___x_1938_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1940_);
lean_ctor_set(v_reuseFailAlloc_1944_, 1, v_a_1933_);
v___x_1942_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
v_a_1932_ = v_tail_1936_;
v_a_1933_ = v___x_1942_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_mkSizeOfFn___lam__4___closed__0(void){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1946_ = lean_box(0);
v___x_1947_ = l_Lean_Level_succ___override(v___x_1946_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFn___lam__4(lean_object* v___x_1948_, lean_object* v___x_1949_, lean_object* v_recName_1950_, lean_object* v___x_1951_, lean_object* v_localInsts_1952_, lean_object* v___x_1953_, lean_object* v___x_1954_, lean_object* v___x_1955_, lean_object* v_cls_1956_, lean_object* v_declName_1957_, lean_object* v___x_1958_, lean_object* v___x_1959_, lean_object* v_numMinors_1960_, lean_object* v_motives_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1967_ = lean_obj_once(&l_Lean_Meta_mkSizeOfFn___lam__4___closed__0, &l_Lean_Meta_mkSizeOfFn___lam__4___closed__0_once, _init_l_Lean_Meta_mkSizeOfFn___lam__4___closed__0);
lean_inc(v___x_1948_);
v___x_1968_ = l_List_mapTR_loop___at___00Lean_Meta_mkSizeOfFn_spec__1(v___x_1948_, v___x_1949_);
v___x_1969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1967_);
lean_ctor_set(v___x_1969_, 1, v___x_1968_);
v___x_1970_ = l_Lean_mkConst(v_recName_1950_, v___x_1969_);
lean_inc_ref(v___x_1951_);
v___x_1971_ = l_Array_append___redArg(v___x_1951_, v_motives_1961_);
v___x_1972_ = l_Lean_mkAppN(v___x_1970_, v___x_1971_);
lean_dec_ref(v___x_1971_);
lean_inc(v___y_1965_);
lean_inc_ref(v___y_1964_);
lean_inc(v___y_1963_);
lean_inc_ref(v___y_1962_);
lean_inc_ref(v___x_1972_);
v___x_1973_ = lean_infer_type(v___x_1972_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v___f_1975_; lean_object* v___f_1976_; lean_object* v___x_1977_; uint8_t v___x_1978_; lean_object* v___x_1979_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
lean_inc(v_a_1974_);
lean_dec_ref(v___x_1973_);
v___f_1975_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSizeOfFn___lam__2___boxed), 15, 9);
lean_closure_set(v___f_1975_, 0, v___x_1951_);
lean_closure_set(v___f_1975_, 1, v_localInsts_1952_);
lean_closure_set(v___f_1975_, 2, v___x_1953_);
lean_closure_set(v___f_1975_, 3, v___x_1954_);
lean_closure_set(v___f_1975_, 4, v___x_1955_);
lean_closure_set(v___f_1975_, 5, v___x_1972_);
lean_closure_set(v___f_1975_, 6, v_cls_1956_);
lean_closure_set(v___f_1975_, 7, v_declName_1957_);
lean_closure_set(v___f_1975_, 8, v___x_1948_);
v___f_1976_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSizeOfFn___lam__3___boxed), 10, 3);
lean_closure_set(v___f_1976_, 0, v___x_1958_);
lean_closure_set(v___f_1976_, 1, v___x_1959_);
lean_closure_set(v___f_1976_, 2, v___f_1975_);
v___x_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1977_, 0, v_numMinors_1960_);
v___x_1978_ = 0;
v___x_1979_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop_spec__1___redArg(v_a_1974_, v___x_1977_, v___f_1976_, v___x_1978_, v___x_1978_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
return v___x_1979_;
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_dec_ref(v___x_1972_);
lean_dec(v_numMinors_1960_);
lean_dec_ref(v___x_1959_);
lean_dec_ref(v___x_1958_);
lean_dec(v_declName_1957_);
lean_dec(v_cls_1956_);
lean_dec_ref(v___x_1955_);
lean_dec_ref(v___x_1954_);
lean_dec_ref(v___x_1953_);
lean_dec_ref(v_localInsts_1952_);
lean_dec_ref(v___x_1951_);
lean_dec(v___x_1948_);
v_a_1980_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1973_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1973_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFn___lam__4___boxed(lean_object** _args){
lean_object* v___x_1988_ = _args[0];
lean_object* v___x_1989_ = _args[1];
lean_object* v_recName_1990_ = _args[2];
lean_object* v___x_1991_ = _args[3];
lean_object* v_localInsts_1992_ = _args[4];
lean_object* v___x_1993_ = _args[5];
lean_object* v___x_1994_ = _args[6];
lean_object* v___x_1995_ = _args[7];
lean_object* v_cls_1996_ = _args[8];
lean_object* v_declName_1997_ = _args[9];
lean_object* v___x_1998_ = _args[10];
lean_object* v___x_1999_ = _args[11];
lean_object* v_numMinors_2000_ = _args[12];
lean_object* v_motives_2001_ = _args[13];
lean_object* v___y_2002_ = _args[14];
lean_object* v___y_2003_ = _args[15];
lean_object* v___y_2004_ = _args[16];
lean_object* v___y_2005_ = _args[17];
lean_object* v___y_2006_ = _args[18];
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_Lean_Meta_mkSizeOfFn___lam__4(v___x_1988_, v___x_1989_, v_recName_1990_, v___x_1991_, v_localInsts_1992_, v___x_1993_, v___x_1994_, v___x_1995_, v_cls_1996_, v_declName_1997_, v___x_1998_, v___x_1999_, v_numMinors_2000_, v_motives_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec_ref(v_motives_2001_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFn___lam__5(lean_object* v___x_2008_, lean_object* v___x_2009_, lean_object* v___x_2010_, lean_object* v_recName_2011_, lean_object* v___x_2012_, lean_object* v___x_2013_, lean_object* v___x_2014_, lean_object* v___x_2015_, lean_object* v_cls_2016_, lean_object* v_declName_2017_, lean_object* v___x_2018_, lean_object* v_numMinors_2019_, lean_object* v_localInsts_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v___x_2026_; lean_object* v___f_2027_; lean_object* v___x_2028_; 
v___x_2026_ = l_Subarray_copy___redArg(v___x_2008_);
lean_inc_ref(v___x_2026_);
v___f_2027_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSizeOfFn___lam__4___boxed), 19, 13);
lean_closure_set(v___f_2027_, 0, v___x_2009_);
lean_closure_set(v___f_2027_, 1, v___x_2010_);
lean_closure_set(v___f_2027_, 2, v_recName_2011_);
lean_closure_set(v___f_2027_, 3, v___x_2012_);
lean_closure_set(v___f_2027_, 4, v_localInsts_2020_);
lean_closure_set(v___f_2027_, 5, v___x_2013_);
lean_closure_set(v___f_2027_, 6, v___x_2014_);
lean_closure_set(v___f_2027_, 7, v___x_2015_);
lean_closure_set(v___f_2027_, 8, v_cls_2016_);
lean_closure_set(v___f_2027_, 9, v_declName_2017_);
lean_closure_set(v___f_2027_, 10, v___x_2018_);
lean_closure_set(v___f_2027_, 11, v___x_2026_);
lean_closure_set(v___f_2027_, 12, v_numMinors_2019_);
v___x_2028_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives___redArg(v___x_2026_, v___f_2027_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
lean_dec_ref(v___x_2026_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFn___lam__5___boxed(lean_object** _args){
lean_object* v___x_2029_ = _args[0];
lean_object* v___x_2030_ = _args[1];
lean_object* v___x_2031_ = _args[2];
lean_object* v_recName_2032_ = _args[3];
lean_object* v___x_2033_ = _args[4];
lean_object* v___x_2034_ = _args[5];
lean_object* v___x_2035_ = _args[6];
lean_object* v___x_2036_ = _args[7];
lean_object* v_cls_2037_ = _args[8];
lean_object* v_declName_2038_ = _args[9];
lean_object* v___x_2039_ = _args[10];
lean_object* v_numMinors_2040_ = _args[11];
lean_object* v_localInsts_2041_ = _args[12];
lean_object* v___y_2042_ = _args[13];
lean_object* v___y_2043_ = _args[14];
lean_object* v___y_2044_ = _args[15];
lean_object* v___y_2045_ = _args[16];
lean_object* v___y_2046_ = _args[17];
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_Lean_Meta_mkSizeOfFn___lam__5(v___x_2029_, v___x_2030_, v___x_2031_, v_recName_2032_, v___x_2033_, v___x_2034_, v___x_2035_, v___x_2036_, v_cls_2037_, v_declName_2038_, v___x_2039_, v_numMinors_2040_, v_localInsts_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFn___lam__6(lean_object* v_levelParams_2048_, lean_object* v_numParams_2049_, lean_object* v_numMotives_2050_, lean_object* v_a_2051_, lean_object* v_numMinors_2052_, lean_object* v_numIndices_2053_, lean_object* v___x_2054_, lean_object* v_recName_2055_, lean_object* v_cls_2056_, lean_object* v_declName_2057_, lean_object* v_xs_2058_, lean_object* v_x_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___f_2081_; lean_object* v___x_2082_; 
v___x_2065_ = l_List_tail_x21___redArg(v_levelParams_2048_);
v___x_2066_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2049_);
lean_inc_ref(v_xs_2058_);
v___x_2067_ = l_Array_toSubarray___redArg(v_xs_2058_, v___x_2066_, v_numParams_2049_);
v___x_2068_ = lean_nat_add(v_numParams_2049_, v_numMotives_2050_);
lean_inc_ref(v_xs_2058_);
v___x_2069_ = l_Array_toSubarray___redArg(v_xs_2058_, v_numParams_2049_, v___x_2068_);
v___x_2070_ = l_Lean_RecursorVal_getFirstMinorIdx(v_a_2051_);
v___x_2071_ = lean_nat_add(v___x_2070_, v_numMinors_2052_);
lean_inc_ref(v_xs_2058_);
v___x_2072_ = l_Array_toSubarray___redArg(v_xs_2058_, v___x_2070_, v___x_2071_);
v___x_2073_ = l_Lean_RecursorVal_getFirstIndexIdx(v_a_2051_);
v___x_2074_ = lean_nat_add(v___x_2073_, v_numIndices_2053_);
lean_inc_ref(v_xs_2058_);
v___x_2075_ = l_Array_toSubarray___redArg(v_xs_2058_, v___x_2073_, v___x_2074_);
v___x_2076_ = l_Lean_RecursorVal_getMajorIdx(v_a_2051_);
v___x_2077_ = lean_array_get(v___x_2054_, v_xs_2058_, v___x_2076_);
lean_dec(v___x_2076_);
lean_dec_ref(v_xs_2058_);
v___x_2078_ = lean_box(0);
v___x_2079_ = lean_obj_once(&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___lam__0___closed__2, &l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___lam__0___closed__2_once, _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___lam__0___closed__2);
v___x_2080_ = l_Subarray_copy___redArg(v___x_2067_);
lean_inc_ref(v___x_2080_);
v___f_2081_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSizeOfFn___lam__5___boxed), 18, 12);
lean_closure_set(v___f_2081_, 0, v___x_2069_);
lean_closure_set(v___f_2081_, 1, v___x_2065_);
lean_closure_set(v___f_2081_, 2, v___x_2078_);
lean_closure_set(v___f_2081_, 3, v_recName_2055_);
lean_closure_set(v___f_2081_, 4, v___x_2080_);
lean_closure_set(v___f_2081_, 5, v___x_2075_);
lean_closure_set(v___f_2081_, 6, v___x_2077_);
lean_closure_set(v___f_2081_, 7, v___x_2079_);
lean_closure_set(v___f_2081_, 8, v_cls_2056_);
lean_closure_set(v___f_2081_, 9, v_declName_2057_);
lean_closure_set(v___f_2081_, 10, v___x_2072_);
lean_closure_set(v___f_2081_, 11, v_numMinors_2052_);
v___x_2082_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances___redArg(v___x_2080_, v___f_2081_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFn___lam__6___boxed(lean_object** _args){
lean_object* v_levelParams_2083_ = _args[0];
lean_object* v_numParams_2084_ = _args[1];
lean_object* v_numMotives_2085_ = _args[2];
lean_object* v_a_2086_ = _args[3];
lean_object* v_numMinors_2087_ = _args[4];
lean_object* v_numIndices_2088_ = _args[5];
lean_object* v___x_2089_ = _args[6];
lean_object* v_recName_2090_ = _args[7];
lean_object* v_cls_2091_ = _args[8];
lean_object* v_declName_2092_ = _args[9];
lean_object* v_xs_2093_ = _args[10];
lean_object* v_x_2094_ = _args[11];
lean_object* v___y_2095_ = _args[12];
lean_object* v___y_2096_ = _args[13];
lean_object* v___y_2097_ = _args[14];
lean_object* v___y_2098_ = _args[15];
lean_object* v___y_2099_ = _args[16];
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l_Lean_Meta_mkSizeOfFn___lam__6(v_levelParams_2083_, v_numParams_2084_, v_numMotives_2085_, v_a_2086_, v_numMinors_2087_, v_numIndices_2088_, v___x_2089_, v_recName_2090_, v_cls_2091_, v_declName_2092_, v_xs_2093_, v_x_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec_ref(v_x_2094_);
lean_dec(v_numIndices_2088_);
lean_dec_ref(v_a_2086_);
lean_dec(v_numMotives_2085_);
lean_dec(v_levelParams_2083_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__0___redArg(lean_object* v_msg_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v_ref_2107_; lean_object* v___x_2108_; lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2117_; 
v_ref_2107_ = lean_ctor_get(v___y_2104_, 5);
v___x_2108_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1_spec__1(v_msg_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2111_ = v___x_2108_;
v_isShared_2112_ = v_isSharedCheck_2117_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2108_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2117_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2113_; lean_object* v___x_2115_; 
lean_inc(v_ref_2107_);
v___x_2113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2113_, 0, v_ref_2107_);
lean_ctor_set(v___x_2113_, 1, v_a_2109_);
if (v_isShared_2112_ == 0)
{
lean_ctor_set_tag(v___x_2111_, 1);
lean_ctor_set(v___x_2111_, 0, v___x_2113_);
v___x_2115_ = v___x_2111_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2113_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__0___redArg___boxed(lean_object* v_msg_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__0___redArg(v_msg_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
return v_res_2124_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = l_instMonadEIO(lean_box(0));
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1(lean_object* v_msg_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_){
_start:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v_toApplicative_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2199_; 
v___x_2136_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__0);
v___x_2137_ = l_StateRefT_x27_instMonad___redArg(v___x_2136_);
v_toApplicative_2138_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2199_ == 0)
{
lean_object* v_unused_2200_; 
v_unused_2200_ = lean_ctor_get(v___x_2137_, 1);
lean_dec(v_unused_2200_);
v___x_2140_ = v___x_2137_;
v_isShared_2141_ = v_isSharedCheck_2199_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_toApplicative_2138_);
lean_dec(v___x_2137_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2199_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v_toFunctor_2142_; lean_object* v_toSeq_2143_; lean_object* v_toSeqLeft_2144_; lean_object* v_toSeqRight_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2197_; 
v_toFunctor_2142_ = lean_ctor_get(v_toApplicative_2138_, 0);
v_toSeq_2143_ = lean_ctor_get(v_toApplicative_2138_, 2);
v_toSeqLeft_2144_ = lean_ctor_get(v_toApplicative_2138_, 3);
v_toSeqRight_2145_ = lean_ctor_get(v_toApplicative_2138_, 4);
v_isSharedCheck_2197_ = !lean_is_exclusive(v_toApplicative_2138_);
if (v_isSharedCheck_2197_ == 0)
{
lean_object* v_unused_2198_; 
v_unused_2198_ = lean_ctor_get(v_toApplicative_2138_, 1);
lean_dec(v_unused_2198_);
v___x_2147_ = v_toApplicative_2138_;
v_isShared_2148_ = v_isSharedCheck_2197_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_toSeqRight_2145_);
lean_inc(v_toSeqLeft_2144_);
lean_inc(v_toSeq_2143_);
lean_inc(v_toFunctor_2142_);
lean_dec(v_toApplicative_2138_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2197_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___f_2149_; lean_object* v___f_2150_; lean_object* v___f_2151_; lean_object* v___f_2152_; lean_object* v___x_2153_; lean_object* v___f_2154_; lean_object* v___f_2155_; lean_object* v___f_2156_; lean_object* v___x_2158_; 
v___f_2149_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__1));
v___f_2150_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_2142_);
v___f_2151_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2151_, 0, v_toFunctor_2142_);
v___f_2152_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2152_, 0, v_toFunctor_2142_);
v___x_2153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2153_, 0, v___f_2151_);
lean_ctor_set(v___x_2153_, 1, v___f_2152_);
v___f_2154_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2154_, 0, v_toSeqRight_2145_);
v___f_2155_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2155_, 0, v_toSeqLeft_2144_);
v___f_2156_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2156_, 0, v_toSeq_2143_);
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 4, v___f_2154_);
lean_ctor_set(v___x_2147_, 3, v___f_2155_);
lean_ctor_set(v___x_2147_, 2, v___f_2156_);
lean_ctor_set(v___x_2147_, 1, v___f_2149_);
lean_ctor_set(v___x_2147_, 0, v___x_2153_);
v___x_2158_ = v___x_2147_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2153_);
lean_ctor_set(v_reuseFailAlloc_2196_, 1, v___f_2149_);
lean_ctor_set(v_reuseFailAlloc_2196_, 2, v___f_2156_);
lean_ctor_set(v_reuseFailAlloc_2196_, 3, v___f_2155_);
lean_ctor_set(v_reuseFailAlloc_2196_, 4, v___f_2154_);
v___x_2158_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
lean_object* v___x_2160_; 
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 1, v___f_2150_);
lean_ctor_set(v___x_2140_, 0, v___x_2158_);
v___x_2160_ = v___x_2140_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2158_);
lean_ctor_set(v_reuseFailAlloc_2195_, 1, v___f_2150_);
v___x_2160_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
lean_object* v___x_2161_; lean_object* v_toApplicative_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2193_; 
v___x_2161_ = l_StateRefT_x27_instMonad___redArg(v___x_2160_);
v_toApplicative_2162_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2193_ == 0)
{
lean_object* v_unused_2194_; 
v_unused_2194_ = lean_ctor_get(v___x_2161_, 1);
lean_dec(v_unused_2194_);
v___x_2164_ = v___x_2161_;
v_isShared_2165_ = v_isSharedCheck_2193_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_toApplicative_2162_);
lean_dec(v___x_2161_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2193_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v_toFunctor_2166_; lean_object* v_toSeq_2167_; lean_object* v_toSeqLeft_2168_; lean_object* v_toSeqRight_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2191_; 
v_toFunctor_2166_ = lean_ctor_get(v_toApplicative_2162_, 0);
v_toSeq_2167_ = lean_ctor_get(v_toApplicative_2162_, 2);
v_toSeqLeft_2168_ = lean_ctor_get(v_toApplicative_2162_, 3);
v_toSeqRight_2169_ = lean_ctor_get(v_toApplicative_2162_, 4);
v_isSharedCheck_2191_ = !lean_is_exclusive(v_toApplicative_2162_);
if (v_isSharedCheck_2191_ == 0)
{
lean_object* v_unused_2192_; 
v_unused_2192_ = lean_ctor_get(v_toApplicative_2162_, 1);
lean_dec(v_unused_2192_);
v___x_2171_ = v_toApplicative_2162_;
v_isShared_2172_ = v_isSharedCheck_2191_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_toSeqRight_2169_);
lean_inc(v_toSeqLeft_2168_);
lean_inc(v_toSeq_2167_);
lean_inc(v_toFunctor_2166_);
lean_dec(v_toApplicative_2162_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2191_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___f_2173_; lean_object* v___f_2174_; lean_object* v___f_2175_; lean_object* v___f_2176_; lean_object* v___x_2177_; lean_object* v___f_2178_; lean_object* v___f_2179_; lean_object* v___f_2180_; lean_object* v___x_2182_; 
v___f_2173_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__3));
v___f_2174_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_2166_);
v___f_2175_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2175_, 0, v_toFunctor_2166_);
v___f_2176_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2176_, 0, v_toFunctor_2166_);
v___x_2177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___f_2175_);
lean_ctor_set(v___x_2177_, 1, v___f_2176_);
v___f_2178_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2178_, 0, v_toSeqRight_2169_);
v___f_2179_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2179_, 0, v_toSeqLeft_2168_);
v___f_2180_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2180_, 0, v_toSeq_2167_);
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 4, v___f_2178_);
lean_ctor_set(v___x_2171_, 3, v___f_2179_);
lean_ctor_set(v___x_2171_, 2, v___f_2180_);
lean_ctor_set(v___x_2171_, 1, v___f_2173_);
lean_ctor_set(v___x_2171_, 0, v___x_2177_);
v___x_2182_ = v___x_2171_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2177_);
lean_ctor_set(v_reuseFailAlloc_2190_, 1, v___f_2173_);
lean_ctor_set(v_reuseFailAlloc_2190_, 2, v___f_2180_);
lean_ctor_set(v_reuseFailAlloc_2190_, 3, v___f_2179_);
lean_ctor_set(v_reuseFailAlloc_2190_, 4, v___f_2178_);
v___x_2182_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
lean_object* v___x_2184_; 
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 1, v___f_2174_);
lean_ctor_set(v___x_2164_, 0, v___x_2182_);
v___x_2184_ = v___x_2164_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v___x_2182_);
lean_ctor_set(v_reuseFailAlloc_2189_, 1, v___f_2174_);
v___x_2184_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_6951__overap_2187_; lean_object* v___x_2188_; 
v___x_2185_ = lean_box(0);
v___x_2186_ = l_instInhabitedOfMonad___redArg(v___x_2184_, v___x_2185_);
v___x_6951__overap_2187_ = lean_panic_fn(v___x_2186_, v_msg_2130_);
lean_inc(v___y_2134_);
lean_inc_ref(v___y_2133_);
lean_inc(v___y_2132_);
lean_inc_ref(v___y_2131_);
v___x_2188_ = lean_apply_5(v___x_6951__overap_2187_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, lean_box(0));
return v___x_2188_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___boxed(lean_object* v_msg_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1(v_msg_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
return v_res_2207_;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2209_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__0));
v___x_2210_ = l_Lean_stringToMessageData(v___x_2209_);
return v___x_2210_;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2212_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__2));
v___x_2213_ = l_Lean_stringToMessageData(v___x_2212_);
return v___x_2213_;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__7(void){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2217_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__6));
v___x_2218_ = lean_unsigned_to_nat(11u);
v___x_2219_ = lean_unsigned_to_nat(129u);
v___x_2220_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__5));
v___x_2221_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__4));
v___x_2222_ = l_mkPanicMessageWithDecl(v___x_2221_, v___x_2220_, v___x_2219_, v___x_2218_, v___x_2217_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0(lean_object* v_constName_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v___x_2237_; lean_object* v_env_2238_; uint8_t v___x_2239_; lean_object* v___x_2240_; 
v___x_2237_ = lean_st_ref_get(v___y_2227_);
v_env_2238_ = lean_ctor_get(v___x_2237_, 0);
lean_inc_ref(v_env_2238_);
lean_dec(v___x_2237_);
v___x_2239_ = 0;
lean_inc(v_constName_2223_);
v___x_2240_ = l_Lean_Environment_findAsync_x3f(v_env_2238_, v_constName_2223_, v___x_2239_);
if (lean_obj_tag(v___x_2240_) == 1)
{
lean_object* v_val_2241_; uint8_t v_kind_2242_; 
v_val_2241_ = lean_ctor_get(v___x_2240_, 0);
lean_inc(v_val_2241_);
lean_dec_ref(v___x_2240_);
v_kind_2242_ = lean_ctor_get_uint8(v_val_2241_, sizeof(void*)*3);
if (v_kind_2242_ == 7)
{
lean_object* v___x_2243_; 
v___x_2243_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2241_);
if (lean_obj_tag(v___x_2243_) == 7)
{
lean_object* v_val_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2251_; 
lean_dec(v_constName_2223_);
v_val_2244_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2246_ = v___x_2243_;
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_val_2244_);
lean_dec(v___x_2243_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2249_; 
if (v_isShared_2247_ == 0)
{
lean_ctor_set_tag(v___x_2246_, 0);
v___x_2249_ = v___x_2246_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_val_2244_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
else
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
lean_dec_ref(v___x_2243_);
v___x_2252_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__7, &l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__7_once, _init_l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__7);
v___x_2253_ = l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1(v___x_2252_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2262_; 
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2256_ = v___x_2253_;
v_isShared_2257_ = v_isSharedCheck_2262_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2253_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2262_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
if (lean_obj_tag(v_a_2254_) == 0)
{
lean_del_object(v___x_2256_);
goto v___jp_2229_;
}
else
{
lean_object* v_val_2258_; lean_object* v___x_2260_; 
lean_dec(v_constName_2223_);
v_val_2258_ = lean_ctor_get(v_a_2254_, 0);
lean_inc(v_val_2258_);
lean_dec_ref(v_a_2254_);
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 0, v_val_2258_);
v___x_2260_ = v___x_2256_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_val_2258_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
else
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2270_; 
lean_dec(v_constName_2223_);
v_a_2263_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2265_ = v___x_2253_;
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___x_2253_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2268_; 
if (v_isShared_2266_ == 0)
{
v___x_2268_ = v___x_2265_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
}
}
else
{
lean_dec(v_val_2241_);
goto v___jp_2229_;
}
}
else
{
lean_dec(v___x_2240_);
goto v___jp_2229_;
}
v___jp_2229_:
{
lean_object* v___x_2230_; uint8_t v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2230_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__1, &l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__1_once, _init_l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__1);
v___x_2231_ = 0;
v___x_2232_ = l_Lean_MessageData_ofConstName(v_constName_2223_, v___x_2231_);
v___x_2233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2230_);
lean_ctor_set(v___x_2233_, 1, v___x_2232_);
v___x_2234_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__3, &l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__3_once, _init_l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__3);
v___x_2235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2233_);
lean_ctor_set(v___x_2235_, 1, v___x_2234_);
v___x_2236_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__0___redArg(v___x_2235_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
return v___x_2236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___boxed(lean_object* v_constName_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0(v_constName_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
return v_res_2277_;
}
}
static lean_object* _init_l_Lean_Meta_mkSizeOfFn___closed__1(void){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2279_ = ((lean_object*)(l_Lean_Meta_mkSizeOfFn___closed__0));
v___x_2280_ = l_Lean_stringToMessageData(v___x_2279_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFn(lean_object* v_recName_2281_, lean_object* v_declName_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_){
_start:
{
lean_object* v_cls_2288_; lean_object* v___x_2289_; lean_object* v_a_2290_; lean_object* v___x_2291_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; uint8_t v___x_2317_; 
v_cls_2288_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__2));
v___x_2289_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__0___redArg(v_cls_2288_, v_a_2285_);
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_a_2290_);
lean_dec_ref(v___x_2289_);
v___x_2291_ = l_Lean_instInhabitedExpr;
v___x_2317_ = lean_unbox(v_a_2290_);
lean_dec(v_a_2290_);
if (v___x_2317_ == 0)
{
v___y_2293_ = v_a_2283_;
v___y_2294_ = v_a_2284_;
v___y_2295_ = v_a_2285_;
v___y_2296_ = v_a_2286_;
goto v___jp_2292_;
}
else
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2318_ = lean_obj_once(&l_Lean_Meta_mkSizeOfFn___closed__1, &l_Lean_Meta_mkSizeOfFn___closed__1_once, _init_l_Lean_Meta_mkSizeOfFn___closed__1);
lean_inc(v_recName_2281_);
v___x_2319_ = l_Lean_MessageData_ofName(v_recName_2281_);
v___x_2320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2318_);
lean_ctor_set(v___x_2320_, 1, v___x_2319_);
v___x_2321_ = l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1(v_cls_2288_, v___x_2320_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_dec_ref(v___x_2321_);
v___y_2293_ = v_a_2283_;
v___y_2294_ = v_a_2284_;
v___y_2295_ = v_a_2285_;
v___y_2296_ = v_a_2286_;
goto v___jp_2292_;
}
else
{
lean_dec(v_declName_2282_);
lean_dec(v_recName_2281_);
return v___x_2321_;
}
}
v___jp_2292_:
{
lean_object* v___x_2297_; 
lean_inc(v_recName_2281_);
v___x_2297_ = l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0(v_recName_2281_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; lean_object* v_toConstantVal_2299_; lean_object* v_numParams_2300_; lean_object* v_numIndices_2301_; lean_object* v_numMotives_2302_; lean_object* v_numMinors_2303_; lean_object* v_levelParams_2304_; lean_object* v_type_2305_; lean_object* v___f_2306_; uint8_t v___x_2307_; lean_object* v___x_2308_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_a_2298_);
lean_dec_ref(v___x_2297_);
v_toConstantVal_2299_ = lean_ctor_get(v_a_2298_, 0);
v_numParams_2300_ = lean_ctor_get(v_a_2298_, 2);
lean_inc(v_numParams_2300_);
v_numIndices_2301_ = lean_ctor_get(v_a_2298_, 3);
lean_inc(v_numIndices_2301_);
v_numMotives_2302_ = lean_ctor_get(v_a_2298_, 4);
lean_inc(v_numMotives_2302_);
v_numMinors_2303_ = lean_ctor_get(v_a_2298_, 5);
lean_inc(v_numMinors_2303_);
v_levelParams_2304_ = lean_ctor_get(v_toConstantVal_2299_, 1);
lean_inc(v_levelParams_2304_);
v_type_2305_ = lean_ctor_get(v_toConstantVal_2299_, 2);
lean_inc_ref(v_type_2305_);
v___f_2306_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSizeOfFn___lam__6___boxed), 17, 10);
lean_closure_set(v___f_2306_, 0, v_levelParams_2304_);
lean_closure_set(v___f_2306_, 1, v_numParams_2300_);
lean_closure_set(v___f_2306_, 2, v_numMotives_2302_);
lean_closure_set(v___f_2306_, 3, v_a_2298_);
lean_closure_set(v___f_2306_, 4, v_numMinors_2303_);
lean_closure_set(v___f_2306_, 5, v_numIndices_2301_);
lean_closure_set(v___f_2306_, 6, v___x_2291_);
lean_closure_set(v___f_2306_, 7, v_recName_2281_);
lean_closure_set(v___f_2306_, 8, v_cls_2288_);
lean_closure_set(v___f_2306_, 9, v_declName_2282_);
v___x_2307_ = 0;
v___x_2308_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__0___redArg(v_type_2305_, v___f_2306_, v___x_2307_, v___x_2307_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
return v___x_2308_;
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
lean_dec(v_declName_2282_);
lean_dec(v_recName_2281_);
v_a_2309_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___x_2297_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2297_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2309_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFn___boxed(lean_object* v_recName_2322_, lean_object* v_declName_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l_Lean_Meta_mkSizeOfFn(v_recName_2322_, v_declName_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_);
lean_dec(v_a_2327_);
lean_dec_ref(v_a_2326_);
lean_dec(v_a_2325_);
lean_dec_ref(v_a_2324_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__0(lean_object* v_00_u03b1_2330_, lean_object* v_msg_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__0___redArg(v_msg_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2338_, lean_object* v_msg_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__0(v_00_u03b1_2338_, v_msg_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkSizeOfFns_spec__2___redArg(lean_object* v_upperBound_2346_, lean_object* v___x_2347_, lean_object* v___x_2348_, lean_object* v_a_2349_, lean_object* v_b_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
uint8_t v___x_2356_; 
v___x_2356_ = lean_nat_dec_lt(v_a_2349_, v_upperBound_2346_);
if (v___x_2356_ == 0)
{
lean_object* v___x_2357_; 
lean_dec(v_a_2349_);
lean_dec(v___x_2348_);
lean_dec(v___x_2347_);
v___x_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2357_, 0, v_b_2350_);
return v___x_2357_;
}
else
{
lean_object* v_snd_2358_; lean_object* v_fst_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2393_; 
v_snd_2358_ = lean_ctor_get(v_b_2350_, 1);
v_fst_2359_ = lean_ctor_get(v_b_2350_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v_b_2350_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2361_ = v_b_2350_;
v_isShared_2362_ = v_isSharedCheck_2393_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_snd_2358_);
lean_inc(v_fst_2359_);
lean_dec(v_b_2350_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2393_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v_fst_2363_; lean_object* v_snd_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2392_; 
v_fst_2363_ = lean_ctor_get(v_snd_2358_, 0);
v_snd_2364_ = lean_ctor_get(v_snd_2358_, 1);
v_isSharedCheck_2392_ = !lean_is_exclusive(v_snd_2358_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2366_ = v_snd_2358_;
v_isShared_2367_ = v_isSharedCheck_2392_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_snd_2364_);
lean_inc(v_fst_2363_);
lean_dec(v_snd_2358_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2392_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2368_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2347_);
v___x_2369_ = l_Lean_mkRecName(v___x_2347_);
v___x_2370_ = lean_nat_add(v_a_2349_, v___x_2368_);
lean_dec(v_a_2349_);
lean_inc(v___x_2370_);
v___x_2371_ = lean_name_append_index_after(v___x_2369_, v___x_2370_);
lean_inc(v_fst_2363_);
lean_inc(v___x_2348_);
v___x_2372_ = lean_name_append_index_after(v___x_2348_, v_fst_2363_);
lean_inc(v___x_2372_);
lean_inc(v___x_2371_);
v___x_2373_ = l_Lean_Meta_mkSizeOfFn(v___x_2371_, v___x_2372_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2378_; 
lean_dec_ref(v___x_2373_);
lean_inc(v___x_2372_);
v___x_2374_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2371_, v___x_2372_, v_snd_2364_);
v___x_2375_ = lean_array_push(v_fst_2359_, v___x_2372_);
v___x_2376_ = lean_nat_add(v_fst_2363_, v___x_2368_);
lean_dec(v_fst_2363_);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 1, v___x_2374_);
lean_ctor_set(v___x_2366_, 0, v___x_2376_);
v___x_2378_ = v___x_2366_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v___x_2376_);
lean_ctor_set(v_reuseFailAlloc_2383_, 1, v___x_2374_);
v___x_2378_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
lean_object* v___x_2380_; 
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 1, v___x_2378_);
lean_ctor_set(v___x_2361_, 0, v___x_2375_);
v___x_2380_ = v___x_2361_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v___x_2375_);
lean_ctor_set(v_reuseFailAlloc_2382_, 1, v___x_2378_);
v___x_2380_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
v_a_2349_ = v___x_2370_;
v_b_2350_ = v___x_2380_;
goto _start;
}
}
}
else
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2391_; 
lean_dec(v___x_2372_);
lean_dec(v___x_2371_);
lean_dec(v___x_2370_);
lean_del_object(v___x_2366_);
lean_dec(v_snd_2364_);
lean_dec(v_fst_2363_);
lean_del_object(v___x_2361_);
lean_dec(v_fst_2359_);
lean_dec(v___x_2348_);
lean_dec(v___x_2347_);
v_a_2384_ = lean_ctor_get(v___x_2373_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2386_ = v___x_2373_;
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2373_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
if (v_isShared_2387_ == 0)
{
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2384_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkSizeOfFns_spec__2___redArg___boxed(lean_object* v_upperBound_2394_, lean_object* v___x_2395_, lean_object* v___x_2396_, lean_object* v_a_2397_, lean_object* v_b_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkSizeOfFns_spec__2___redArg(v_upperBound_2394_, v___x_2395_, v___x_2396_, v_a_2397_, v_b_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v_upperBound_2394_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfFns_spec__1___redArg(lean_object* v___x_2405_, lean_object* v_as_x27_2406_, lean_object* v_b_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
if (lean_obj_tag(v_as_x27_2406_) == 0)
{
lean_object* v___x_2413_; 
lean_dec(v___x_2405_);
v___x_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2413_, 0, v_b_2407_);
return v___x_2413_;
}
else
{
lean_object* v_snd_2414_; lean_object* v_head_2415_; lean_object* v_tail_2416_; lean_object* v_fst_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2449_; 
v_snd_2414_ = lean_ctor_get(v_b_2407_, 1);
lean_inc(v_snd_2414_);
v_head_2415_ = lean_ctor_get(v_as_x27_2406_, 0);
lean_inc(v_head_2415_);
v_tail_2416_ = lean_ctor_get(v_as_x27_2406_, 1);
lean_inc(v_tail_2416_);
lean_dec_ref(v_as_x27_2406_);
v_fst_2417_ = lean_ctor_get(v_b_2407_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v_b_2407_);
if (v_isSharedCheck_2449_ == 0)
{
lean_object* v_unused_2450_; 
v_unused_2450_ = lean_ctor_get(v_b_2407_, 1);
lean_dec(v_unused_2450_);
v___x_2419_ = v_b_2407_;
v_isShared_2420_ = v_isSharedCheck_2449_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_fst_2417_);
lean_dec(v_b_2407_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2449_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v_fst_2421_; lean_object* v_snd_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2448_; 
v_fst_2421_ = lean_ctor_get(v_snd_2414_, 0);
v_snd_2422_ = lean_ctor_get(v_snd_2414_, 1);
v_isSharedCheck_2448_ = !lean_is_exclusive(v_snd_2414_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2424_ = v_snd_2414_;
v_isShared_2425_ = v_isSharedCheck_2448_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_snd_2422_);
lean_inc(v_fst_2421_);
lean_dec(v_snd_2414_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2448_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
lean_inc(v_fst_2421_);
lean_inc(v___x_2405_);
v___x_2426_ = lean_name_append_index_after(v___x_2405_, v_fst_2421_);
v___x_2427_ = l_Lean_mkRecName(v_head_2415_);
lean_inc(v___x_2426_);
lean_inc(v___x_2427_);
v___x_2428_ = l_Lean_Meta_mkSizeOfFn(v___x_2427_, v___x_2426_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2434_; 
lean_dec_ref(v___x_2428_);
v___x_2429_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2426_);
v___x_2430_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2427_, v___x_2426_, v_snd_2422_);
v___x_2431_ = lean_array_push(v_fst_2417_, v___x_2426_);
v___x_2432_ = lean_nat_add(v_fst_2421_, v___x_2429_);
lean_dec(v_fst_2421_);
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 1, v___x_2430_);
lean_ctor_set(v___x_2424_, 0, v___x_2432_);
v___x_2434_ = v___x_2424_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v___x_2432_);
lean_ctor_set(v_reuseFailAlloc_2439_, 1, v___x_2430_);
v___x_2434_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
lean_object* v___x_2436_; 
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 1, v___x_2434_);
lean_ctor_set(v___x_2419_, 0, v___x_2431_);
v___x_2436_ = v___x_2419_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v___x_2431_);
lean_ctor_set(v_reuseFailAlloc_2438_, 1, v___x_2434_);
v___x_2436_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
v_as_x27_2406_ = v_tail_2416_;
v_b_2407_ = v___x_2436_;
goto _start;
}
}
}
else
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
lean_dec(v___x_2427_);
lean_dec(v___x_2426_);
lean_del_object(v___x_2424_);
lean_dec(v_snd_2422_);
lean_dec(v_fst_2421_);
lean_del_object(v___x_2419_);
lean_dec(v_fst_2417_);
lean_dec(v_tail_2416_);
lean_dec(v___x_2405_);
v_a_2440_ = lean_ctor_get(v___x_2428_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v___x_2428_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2428_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2440_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfFns_spec__1___redArg___boxed(lean_object* v___x_2451_, lean_object* v_as_x27_2452_, lean_object* v_b_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfFns_spec__1___redArg(v___x_2451_, v_as_x27_2452_, v_b_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v___y_2455_);
lean_dec_ref(v___y_2454_);
return v_res_2459_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSizeOfFns_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2461_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSizeOfFns_spec__0___closed__0));
v___x_2462_ = l_Lean_stringToMessageData(v___x_2461_);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSizeOfFns_spec__0(lean_object* v_constName_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_){
_start:
{
lean_object* v___x_2469_; lean_object* v_env_2470_; lean_object* v___x_2471_; 
v___x_2469_ = lean_st_ref_get(v___y_2467_);
v_env_2470_ = lean_ctor_get(v___x_2469_, 0);
lean_inc_ref(v_env_2470_);
lean_dec(v___x_2469_);
lean_inc(v_constName_2463_);
v___x_2471_ = l_Lean_isInductiveCore_x3f(v_env_2470_, v_constName_2463_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v___x_2472_; uint8_t v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2472_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__1, &l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__1_once, _init_l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__1);
v___x_2473_ = 0;
v___x_2474_ = l_Lean_MessageData_ofConstName(v_constName_2463_, v___x_2473_);
v___x_2475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2472_);
lean_ctor_set(v___x_2475_, 1, v___x_2474_);
v___x_2476_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSizeOfFns_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSizeOfFns_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSizeOfFns_spec__0___closed__1);
v___x_2477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2475_);
lean_ctor_set(v___x_2477_, 1, v___x_2476_);
v___x_2478_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__0___redArg(v___x_2477_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_);
return v___x_2478_;
}
else
{
lean_object* v_val_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2486_; 
lean_dec(v_constName_2463_);
v_val_2479_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2481_ = v___x_2471_;
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_val_2479_);
lean_dec(v___x_2471_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2484_; 
if (v_isShared_2482_ == 0)
{
lean_ctor_set_tag(v___x_2481_, 0);
v___x_2484_ = v___x_2481_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_val_2479_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSizeOfFns_spec__0___boxed(lean_object* v_constName_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSizeOfFns_spec__0(v_constName_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFns(lean_object* v_typeName_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_){
_start:
{
lean_object* v___x_2511_; 
v___x_2511_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSizeOfFns_spec__0(v_typeName_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2512_; lean_object* v_all_2513_; lean_object* v_numNested_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_a_2512_);
lean_dec_ref(v___x_2511_);
v_all_2513_ = lean_ctor_get(v_a_2512_, 3);
lean_inc(v_all_2513_);
v_numNested_2514_ = lean_ctor_get(v_a_2512_, 5);
lean_inc(v_numNested_2514_);
lean_dec(v_a_2512_);
v___x_2515_ = lean_box(0);
v___x_2516_ = lean_unsigned_to_nat(0u);
v___x_2517_ = l_List_head_x21___redArg(v___x_2515_, v_all_2513_);
v___x_2518_ = ((lean_object*)(l_Lean_Meta_mkSizeOfFns___closed__2));
lean_inc(v___x_2517_);
v___x_2519_ = l_Lean_Name_append(v___x_2517_, v___x_2518_);
v___x_2520_ = ((lean_object*)(l_Lean_Meta_mkSizeOfFns___closed__4));
lean_inc(v___x_2519_);
v___x_2521_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfFns_spec__1___redArg(v___x_2519_, v_all_2513_, v___x_2520_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v_a_2522_; lean_object* v_snd_2523_; lean_object* v_fst_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2568_; 
v_a_2522_ = lean_ctor_get(v___x_2521_, 0);
lean_inc(v_a_2522_);
lean_dec_ref(v___x_2521_);
v_snd_2523_ = lean_ctor_get(v_a_2522_, 1);
v_fst_2524_ = lean_ctor_get(v_a_2522_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v_a_2522_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2526_ = v_a_2522_;
v_isShared_2527_ = v_isSharedCheck_2568_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_snd_2523_);
lean_inc(v_fst_2524_);
lean_dec(v_a_2522_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2568_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v_fst_2528_; lean_object* v_snd_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2567_; 
v_fst_2528_ = lean_ctor_get(v_snd_2523_, 0);
v_snd_2529_ = lean_ctor_get(v_snd_2523_, 1);
v_isSharedCheck_2567_ = !lean_is_exclusive(v_snd_2523_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2531_ = v_snd_2523_;
v_isShared_2532_ = v_isSharedCheck_2567_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_snd_2529_);
lean_inc(v_fst_2528_);
lean_dec(v_snd_2523_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2567_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2534_; 
if (v_isShared_2532_ == 0)
{
v___x_2534_ = v___x_2531_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_fst_2528_);
lean_ctor_set(v_reuseFailAlloc_2566_, 1, v_snd_2529_);
v___x_2534_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
lean_object* v___x_2536_; 
if (v_isShared_2527_ == 0)
{
lean_ctor_set(v___x_2526_, 1, v___x_2534_);
v___x_2536_ = v___x_2526_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_fst_2524_);
lean_ctor_set(v_reuseFailAlloc_2565_, 1, v___x_2534_);
v___x_2536_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
lean_object* v___x_2537_; 
v___x_2537_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkSizeOfFns_spec__2___redArg(v_numNested_2514_, v___x_2517_, v___x_2519_, v___x_2516_, v___x_2536_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
lean_dec(v_numNested_2514_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2556_; 
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2540_ = v___x_2537_;
v_isShared_2541_ = v_isSharedCheck_2556_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2537_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2556_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v_snd_2542_; lean_object* v_fst_2543_; lean_object* v_snd_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2554_; 
v_snd_2542_ = lean_ctor_get(v_a_2538_, 1);
lean_inc(v_snd_2542_);
v_fst_2543_ = lean_ctor_get(v_a_2538_, 0);
lean_inc(v_fst_2543_);
lean_dec(v_a_2538_);
v_snd_2544_ = lean_ctor_get(v_snd_2542_, 1);
v_isSharedCheck_2554_ = !lean_is_exclusive(v_snd_2542_);
if (v_isSharedCheck_2554_ == 0)
{
lean_object* v_unused_2555_; 
v_unused_2555_ = lean_ctor_get(v_snd_2542_, 0);
lean_dec(v_unused_2555_);
v___x_2546_ = v_snd_2542_;
v_isShared_2547_ = v_isSharedCheck_2554_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_snd_2544_);
lean_dec(v_snd_2542_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2554_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 0, v_fst_2543_);
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_fst_2543_);
lean_ctor_set(v_reuseFailAlloc_2553_, 1, v_snd_2544_);
v___x_2549_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
lean_object* v___x_2551_; 
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 0, v___x_2549_);
v___x_2551_ = v___x_2540_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2549_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
}
}
else
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2564_; 
v_a_2557_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2559_ = v___x_2537_;
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2537_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2560_ == 0)
{
v___x_2562_ = v___x_2559_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_a_2557_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2576_; 
lean_dec(v___x_2519_);
lean_dec(v___x_2517_);
lean_dec(v_numNested_2514_);
v_a_2569_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2571_ = v___x_2521_;
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2521_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2574_; 
if (v_isShared_2572_ == 0)
{
v___x_2574_ = v___x_2571_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
else
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2584_; 
v_a_2577_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2579_ = v___x_2511_;
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2511_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2580_ == 0)
{
v___x_2582_ = v___x_2579_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2577_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfFns___boxed(lean_object* v_typeName_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l_Lean_Meta_mkSizeOfFns(v_typeName_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_);
lean_dec(v_a_2589_);
lean_dec_ref(v_a_2588_);
lean_dec(v_a_2587_);
lean_dec_ref(v_a_2586_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfFns_spec__1(lean_object* v___x_2592_, lean_object* v_as_2593_, lean_object* v_as_x27_2594_, lean_object* v_b_2595_, lean_object* v_a_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
lean_object* v___x_2602_; 
v___x_2602_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfFns_spec__1___redArg(v___x_2592_, v_as_x27_2594_, v_b_2595_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfFns_spec__1___boxed(lean_object* v___x_2603_, lean_object* v_as_2604_, lean_object* v_as_x27_2605_, lean_object* v_b_2606_, lean_object* v_a_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfFns_spec__1(v___x_2603_, v_as_2604_, v_as_x27_2605_, v_b_2606_, v_a_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec(v_as_2604_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkSizeOfFns_spec__2(lean_object* v_upperBound_2614_, lean_object* v___x_2615_, lean_object* v___x_2616_, lean_object* v_inst_2617_, lean_object* v_R_2618_, lean_object* v_a_2619_, lean_object* v_b_2620_, lean_object* v_c_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_){
_start:
{
lean_object* v___x_2627_; 
v___x_2627_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkSizeOfFns_spec__2___redArg(v_upperBound_2614_, v___x_2615_, v___x_2616_, v_a_2619_, v_b_2620_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_);
return v___x_2627_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkSizeOfFns_spec__2___boxed(lean_object* v_upperBound_2628_, lean_object* v___x_2629_, lean_object* v___x_2630_, lean_object* v_inst_2631_, lean_object* v_R_2632_, lean_object* v_a_2633_, lean_object* v_b_2634_, lean_object* v_c_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkSizeOfFns_spec__2(v_upperBound_2628_, v___x_2629_, v___x_2630_, v_inst_2631_, v_R_2632_, v_a_2633_, v_b_2634_, v_c_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
lean_dec(v_upperBound_2628_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfSpecLemmaName(lean_object* v_ctorName_2645_){
_start:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2646_ = ((lean_object*)(l_Lean_Meta_mkSizeOfSpecLemmaName___closed__1));
v___x_2647_ = l_Lean_Name_append(v_ctorName_2645_, v___x_2646_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfSpecLemmaInstance___lam__0(lean_object* v_xs_2648_, lean_object* v_x_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_){
_start:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2655_ = lean_array_get_size(v_xs_2648_);
v___x_2656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2655_);
return v___x_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfSpecLemmaInstance___lam__0___boxed(lean_object* v_xs_2657_, lean_object* v_x_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l_Lean_Meta_mkSizeOfSpecLemmaInstance___lam__0(v_xs_2657_, v_x_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec_ref(v_x_2658_);
lean_dec_ref(v_xs_2657_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_2665_, lean_object* v_msg_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_){
_start:
{
lean_object* v_fileName_2672_; lean_object* v_fileMap_2673_; lean_object* v_options_2674_; lean_object* v_currRecDepth_2675_; lean_object* v_maxRecDepth_2676_; lean_object* v_ref_2677_; lean_object* v_currNamespace_2678_; lean_object* v_openDecls_2679_; lean_object* v_initHeartbeats_2680_; lean_object* v_maxHeartbeats_2681_; lean_object* v_quotContext_2682_; lean_object* v_currMacroScope_2683_; uint8_t v_diag_2684_; lean_object* v_cancelTk_x3f_2685_; uint8_t v_suppressElabErrors_2686_; lean_object* v_inheritedTraceOptions_2687_; lean_object* v_ref_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v_fileName_2672_ = lean_ctor_get(v___y_2669_, 0);
v_fileMap_2673_ = lean_ctor_get(v___y_2669_, 1);
v_options_2674_ = lean_ctor_get(v___y_2669_, 2);
v_currRecDepth_2675_ = lean_ctor_get(v___y_2669_, 3);
v_maxRecDepth_2676_ = lean_ctor_get(v___y_2669_, 4);
v_ref_2677_ = lean_ctor_get(v___y_2669_, 5);
v_currNamespace_2678_ = lean_ctor_get(v___y_2669_, 6);
v_openDecls_2679_ = lean_ctor_get(v___y_2669_, 7);
v_initHeartbeats_2680_ = lean_ctor_get(v___y_2669_, 8);
v_maxHeartbeats_2681_ = lean_ctor_get(v___y_2669_, 9);
v_quotContext_2682_ = lean_ctor_get(v___y_2669_, 10);
v_currMacroScope_2683_ = lean_ctor_get(v___y_2669_, 11);
v_diag_2684_ = lean_ctor_get_uint8(v___y_2669_, sizeof(void*)*14);
v_cancelTk_x3f_2685_ = lean_ctor_get(v___y_2669_, 12);
v_suppressElabErrors_2686_ = lean_ctor_get_uint8(v___y_2669_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2687_ = lean_ctor_get(v___y_2669_, 13);
v_ref_2688_ = l_Lean_replaceRef(v_ref_2665_, v_ref_2677_);
lean_inc_ref(v_inheritedTraceOptions_2687_);
lean_inc(v_cancelTk_x3f_2685_);
lean_inc(v_currMacroScope_2683_);
lean_inc(v_quotContext_2682_);
lean_inc(v_maxHeartbeats_2681_);
lean_inc(v_initHeartbeats_2680_);
lean_inc(v_openDecls_2679_);
lean_inc(v_currNamespace_2678_);
lean_inc(v_maxRecDepth_2676_);
lean_inc(v_currRecDepth_2675_);
lean_inc_ref(v_options_2674_);
lean_inc_ref(v_fileMap_2673_);
lean_inc_ref(v_fileName_2672_);
v___x_2689_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2689_, 0, v_fileName_2672_);
lean_ctor_set(v___x_2689_, 1, v_fileMap_2673_);
lean_ctor_set(v___x_2689_, 2, v_options_2674_);
lean_ctor_set(v___x_2689_, 3, v_currRecDepth_2675_);
lean_ctor_set(v___x_2689_, 4, v_maxRecDepth_2676_);
lean_ctor_set(v___x_2689_, 5, v_ref_2688_);
lean_ctor_set(v___x_2689_, 6, v_currNamespace_2678_);
lean_ctor_set(v___x_2689_, 7, v_openDecls_2679_);
lean_ctor_set(v___x_2689_, 8, v_initHeartbeats_2680_);
lean_ctor_set(v___x_2689_, 9, v_maxHeartbeats_2681_);
lean_ctor_set(v___x_2689_, 10, v_quotContext_2682_);
lean_ctor_set(v___x_2689_, 11, v_currMacroScope_2683_);
lean_ctor_set(v___x_2689_, 12, v_cancelTk_x3f_2685_);
lean_ctor_set(v___x_2689_, 13, v_inheritedTraceOptions_2687_);
lean_ctor_set_uint8(v___x_2689_, sizeof(void*)*14, v_diag_2684_);
lean_ctor_set_uint8(v___x_2689_, sizeof(void*)*14 + 1, v_suppressElabErrors_2686_);
v___x_2690_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__0___redArg(v_msg_2666_, v___y_2667_, v___y_2668_, v___x_2689_, v___y_2670_);
lean_dec_ref(v___x_2689_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_2691_, lean_object* v_msg_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
lean_object* v_res_2698_; 
v_res_2698_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_2691_, v_msg_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v_ref_2691_);
return v_res_2698_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2699_; 
v___x_2699_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2699_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2700_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_2701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2700_);
return v___x_2701_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2702_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_2703_ = lean_unsigned_to_nat(0u);
v___x_2704_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2703_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
lean_ctor_set(v___x_2704_, 2, v___x_2703_);
lean_ctor_set(v___x_2704_, 3, v___x_2702_);
lean_ctor_set(v___x_2704_, 4, v___x_2702_);
lean_ctor_set(v___x_2704_, 5, v___x_2702_);
lean_ctor_set(v___x_2704_, 6, v___x_2702_);
lean_ctor_set(v___x_2704_, 7, v___x_2702_);
lean_ctor_set(v___x_2704_, 8, v___x_2702_);
return v___x_2704_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2705_ = lean_unsigned_to_nat(32u);
v___x_2706_ = lean_mk_empty_array_with_capacity(v___x_2705_);
v___x_2707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2706_);
return v___x_2707_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2708_ = ((size_t)5ULL);
v___x_2709_ = lean_unsigned_to_nat(0u);
v___x_2710_ = lean_unsigned_to_nat(32u);
v___x_2711_ = lean_mk_empty_array_with_capacity(v___x_2710_);
v___x_2712_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_2713_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2713_, 0, v___x_2712_);
lean_ctor_set(v___x_2713_, 1, v___x_2711_);
lean_ctor_set(v___x_2713_, 2, v___x_2709_);
lean_ctor_set(v___x_2713_, 3, v___x_2709_);
lean_ctor_set_usize(v___x_2713_, 4, v___x_2708_);
return v___x_2713_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2714_ = lean_box(1);
v___x_2715_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_2716_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_2717_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2716_);
lean_ctor_set(v___x_2717_, 1, v___x_2715_);
lean_ctor_set(v___x_2717_, 2, v___x_2714_);
return v___x_2717_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2719_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_2720_ = l_Lean_stringToMessageData(v___x_2719_);
return v___x_2720_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2722_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_2723_ = l_Lean_stringToMessageData(v___x_2722_);
return v___x_2723_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2725_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_2726_ = l_Lean_stringToMessageData(v___x_2725_);
return v___x_2726_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2728_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_2729_ = l_Lean_stringToMessageData(v___x_2728_);
return v___x_2729_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2731_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_2732_ = l_Lean_stringToMessageData(v___x_2731_);
return v___x_2732_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2734_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_2735_ = l_Lean_stringToMessageData(v___x_2734_);
return v___x_2735_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2737_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18));
v___x_2738_ = l_Lean_stringToMessageData(v___x_2737_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_2739_, lean_object* v_declHint_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v___x_2743_; lean_object* v_env_2744_; uint8_t v___x_2745_; 
v___x_2743_ = lean_st_ref_get(v___y_2741_);
v_env_2744_ = lean_ctor_get(v___x_2743_, 0);
lean_inc_ref(v_env_2744_);
lean_dec(v___x_2743_);
v___x_2745_ = l_Lean_Name_isAnonymous(v_declHint_2740_);
if (v___x_2745_ == 0)
{
uint8_t v_isExporting_2746_; 
v_isExporting_2746_ = lean_ctor_get_uint8(v_env_2744_, sizeof(void*)*8);
if (v_isExporting_2746_ == 0)
{
lean_object* v___x_2747_; 
lean_dec_ref(v_env_2744_);
lean_dec(v_declHint_2740_);
v___x_2747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2747_, 0, v_msg_2739_);
return v___x_2747_;
}
else
{
lean_object* v___x_2748_; uint8_t v___x_2749_; 
lean_inc_ref(v_env_2744_);
v___x_2748_ = l_Lean_Environment_setExporting(v_env_2744_, v___x_2745_);
lean_inc(v_declHint_2740_);
lean_inc_ref(v___x_2748_);
v___x_2749_ = l_Lean_Environment_contains(v___x_2748_, v_declHint_2740_, v_isExporting_2746_);
if (v___x_2749_ == 0)
{
lean_object* v___x_2750_; 
lean_dec_ref(v___x_2748_);
lean_dec_ref(v_env_2744_);
lean_dec(v_declHint_2740_);
v___x_2750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2750_, 0, v_msg_2739_);
return v___x_2750_;
}
else
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v_c_2756_; lean_object* v___x_2757_; 
v___x_2751_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_2752_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_2753_ = l_Lean_Options_empty;
v___x_2754_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2748_);
lean_ctor_set(v___x_2754_, 1, v___x_2751_);
lean_ctor_set(v___x_2754_, 2, v___x_2752_);
lean_ctor_set(v___x_2754_, 3, v___x_2753_);
lean_inc(v_declHint_2740_);
v___x_2755_ = l_Lean_MessageData_ofConstName(v_declHint_2740_, v___x_2745_);
v_c_2756_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2756_, 0, v___x_2754_);
lean_ctor_set(v_c_2756_, 1, v___x_2755_);
v___x_2757_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2744_, v_declHint_2740_);
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
lean_dec_ref(v_env_2744_);
lean_dec(v_declHint_2740_);
v___x_2758_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_2759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2758_);
lean_ctor_set(v___x_2759_, 1, v_c_2756_);
v___x_2760_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_2761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2759_);
lean_ctor_set(v___x_2761_, 1, v___x_2760_);
v___x_2762_ = l_Lean_MessageData_note(v___x_2761_);
v___x_2763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2763_, 0, v_msg_2739_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
v___x_2764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2763_);
return v___x_2764_;
}
else
{
lean_object* v_val_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2800_; 
v_val_2765_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2767_ = v___x_2757_;
v_isShared_2768_ = v_isSharedCheck_2800_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_val_2765_);
lean_dec(v___x_2757_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2800_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v_mod_2772_; uint8_t v___x_2773_; 
v___x_2769_ = lean_box(0);
v___x_2770_ = l_Lean_Environment_header(v_env_2744_);
lean_dec_ref(v_env_2744_);
v___x_2771_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2770_);
v_mod_2772_ = lean_array_get(v___x_2769_, v___x_2771_, v_val_2765_);
lean_dec(v_val_2765_);
lean_dec_ref(v___x_2771_);
v___x_2773_ = l_Lean_isPrivateName(v_declHint_2740_);
lean_dec(v_declHint_2740_);
if (v___x_2773_ == 0)
{
lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2785_; 
v___x_2774_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_2775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2774_);
lean_ctor_set(v___x_2775_, 1, v_c_2756_);
v___x_2776_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_2777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2775_);
lean_ctor_set(v___x_2777_, 1, v___x_2776_);
v___x_2778_ = l_Lean_MessageData_ofName(v_mod_2772_);
v___x_2779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2777_);
lean_ctor_set(v___x_2779_, 1, v___x_2778_);
v___x_2780_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_2781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2781_, 0, v___x_2779_);
lean_ctor_set(v___x_2781_, 1, v___x_2780_);
v___x_2782_ = l_Lean_MessageData_note(v___x_2781_);
v___x_2783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2783_, 0, v_msg_2739_);
lean_ctor_set(v___x_2783_, 1, v___x_2782_);
if (v_isShared_2768_ == 0)
{
lean_ctor_set_tag(v___x_2767_, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2783_);
v___x_2785_ = v___x_2767_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v___x_2783_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
else
{
lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2798_; 
v___x_2787_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_2788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2788_, 0, v___x_2787_);
lean_ctor_set(v___x_2788_, 1, v_c_2756_);
v___x_2789_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_2790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2788_);
lean_ctor_set(v___x_2790_, 1, v___x_2789_);
v___x_2791_ = l_Lean_MessageData_ofName(v_mod_2772_);
v___x_2792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2790_);
lean_ctor_set(v___x_2792_, 1, v___x_2791_);
v___x_2793_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_2794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2792_);
lean_ctor_set(v___x_2794_, 1, v___x_2793_);
v___x_2795_ = l_Lean_MessageData_note(v___x_2794_);
v___x_2796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2796_, 0, v_msg_2739_);
lean_ctor_set(v___x_2796_, 1, v___x_2795_);
if (v_isShared_2768_ == 0)
{
lean_ctor_set_tag(v___x_2767_, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2796_);
v___x_2798_ = v___x_2767_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v___x_2796_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2801_; 
lean_dec_ref(v_env_2744_);
lean_dec(v_declHint_2740_);
v___x_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2801_, 0, v_msg_2739_);
return v___x_2801_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_2802_, lean_object* v_declHint_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_2802_, v_declHint_2803_, v___y_2804_);
lean_dec(v___y_2804_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_2807_, lean_object* v_declHint_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_){
_start:
{
lean_object* v___x_2814_; lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2824_; 
v___x_2814_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_2807_, v_declHint_2808_, v___y_2812_);
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2817_ = v___x_2814_;
v_isShared_2818_ = v_isSharedCheck_2824_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2814_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2824_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2822_; 
v___x_2819_ = l_Lean_unknownIdentifierMessageTag;
v___x_2820_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2820_, 0, v___x_2819_);
lean_ctor_set(v___x_2820_, 1, v_a_2815_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 0, v___x_2820_);
v___x_2822_ = v___x_2817_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v___x_2820_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_2825_, lean_object* v_declHint_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_2825_, v_declHint_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_);
lean_dec(v___y_2830_);
lean_dec_ref(v___y_2829_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_2833_, lean_object* v_msg_2834_, lean_object* v_declHint_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
lean_object* v___x_2841_; lean_object* v_a_2842_; lean_object* v___x_2843_; 
v___x_2841_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_2834_, v_declHint_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_a_2842_);
lean_dec_ref(v___x_2841_);
v___x_2843_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_2833_, v_a_2842_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
return v___x_2843_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_2844_, lean_object* v_msg_2845_, lean_object* v_declHint_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_){
_start:
{
lean_object* v_res_2852_; 
v_res_2852_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_2844_, v_msg_2845_, v_declHint_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec(v_ref_2844_);
return v_res_2852_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; 
v___x_2854_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_2855_ = l_Lean_stringToMessageData(v___x_2854_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2856_, lean_object* v_constName_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
lean_object* v___x_2863_; uint8_t v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2863_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2864_ = 0;
lean_inc(v_constName_2857_);
v___x_2865_ = l_Lean_MessageData_ofConstName(v_constName_2857_, v___x_2864_);
v___x_2866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2863_);
lean_ctor_set(v___x_2866_, 1, v___x_2865_);
v___x_2867_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__1, &l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__1_once, _init_l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__1);
v___x_2868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2866_);
lean_ctor_set(v___x_2868_, 1, v___x_2867_);
v___x_2869_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_2856_, v___x_2868_, v_constName_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2870_, lean_object* v_constName_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v_res_2877_; 
v_res_2877_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1___redArg(v_ref_2870_, v_constName_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v_ref_2870_);
return v_res_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0___redArg(lean_object* v_constName_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
lean_object* v_ref_2884_; lean_object* v___x_2885_; 
v_ref_2884_ = lean_ctor_get(v___y_2881_, 5);
v___x_2885_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1___redArg(v_ref_2884_, v_constName_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0___redArg(v_constName_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0(lean_object* v_constName_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_){
_start:
{
lean_object* v___x_2899_; lean_object* v_env_2900_; uint8_t v___x_2901_; lean_object* v___x_2902_; 
v___x_2899_ = lean_st_ref_get(v___y_2897_);
v_env_2900_ = lean_ctor_get(v___x_2899_, 0);
lean_inc_ref(v_env_2900_);
lean_dec(v___x_2899_);
v___x_2901_ = 0;
lean_inc(v_constName_2893_);
v___x_2902_ = l_Lean_Environment_find_x3f(v_env_2900_, v_constName_2893_, v___x_2901_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_object* v___x_2903_; 
v___x_2903_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0___redArg(v_constName_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_);
return v___x_2903_;
}
else
{
lean_object* v_val_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
lean_dec(v_constName_2893_);
v_val_2904_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2902_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_val_2904_);
lean_dec(v___x_2902_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
lean_ctor_set_tag(v___x_2906_, 0);
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_val_2904_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0___boxed(lean_object* v_constName_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l_Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0(v_constName_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__1___redArg(lean_object* v_a_2919_, lean_object* v_b_2920_){
_start:
{
lean_object* v_array_2921_; lean_object* v_start_2922_; lean_object* v_stop_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2936_; 
v_array_2921_ = lean_ctor_get(v_a_2919_, 0);
v_start_2922_ = lean_ctor_get(v_a_2919_, 1);
v_stop_2923_ = lean_ctor_get(v_a_2919_, 2);
v_isSharedCheck_2936_ = !lean_is_exclusive(v_a_2919_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2925_ = v_a_2919_;
v_isShared_2926_ = v_isSharedCheck_2936_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_stop_2923_);
lean_inc(v_start_2922_);
lean_inc(v_array_2921_);
lean_dec(v_a_2919_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2936_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
uint8_t v___x_2927_; 
v___x_2927_ = lean_nat_dec_lt(v_start_2922_, v_stop_2923_);
if (v___x_2927_ == 0)
{
lean_del_object(v___x_2925_);
lean_dec(v_stop_2923_);
lean_dec(v_start_2922_);
lean_dec_ref(v_array_2921_);
return v_b_2920_;
}
else
{
lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2931_; 
v___x_2928_ = lean_unsigned_to_nat(1u);
v___x_2929_ = lean_nat_add(v_start_2922_, v___x_2928_);
lean_inc_ref(v_array_2921_);
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 1, v___x_2929_);
v___x_2931_ = v___x_2925_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_array_2921_);
lean_ctor_set(v_reuseFailAlloc_2935_, 1, v___x_2929_);
lean_ctor_set(v_reuseFailAlloc_2935_, 2, v_stop_2923_);
v___x_2931_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2932_ = lean_array_fget(v_array_2921_, v_start_2922_);
lean_dec(v_start_2922_);
lean_dec_ref(v_array_2921_);
v___x_2933_ = lean_array_push(v_b_2920_, v___x_2932_);
v_a_2919_ = v___x_2931_;
v_b_2920_ = v___x_2933_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__2(size_t v_sz_2937_, size_t v_i_2938_, lean_object* v_bs_2939_){
_start:
{
uint8_t v___x_2940_; 
v___x_2940_ = lean_usize_dec_lt(v_i_2938_, v_sz_2937_);
if (v___x_2940_ == 0)
{
return v_bs_2939_;
}
else
{
lean_object* v_v_2941_; lean_object* v___x_2942_; lean_object* v_bs_x27_2943_; lean_object* v___x_2944_; size_t v___x_2945_; size_t v___x_2946_; lean_object* v___x_2947_; 
v_v_2941_ = lean_array_uget(v_bs_2939_, v_i_2938_);
v___x_2942_ = lean_unsigned_to_nat(0u);
v_bs_x27_2943_ = lean_array_uset(v_bs_2939_, v_i_2938_, v___x_2942_);
v___x_2944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2944_, 0, v_v_2941_);
v___x_2945_ = ((size_t)1ULL);
v___x_2946_ = lean_usize_add(v_i_2938_, v___x_2945_);
v___x_2947_ = lean_array_uset(v_bs_x27_2943_, v_i_2938_, v___x_2944_);
v_i_2938_ = v___x_2946_;
v_bs_2939_ = v___x_2947_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__2___boxed(lean_object* v_sz_2949_, lean_object* v_i_2950_, lean_object* v_bs_2951_){
_start:
{
size_t v_sz_boxed_2952_; size_t v_i_boxed_2953_; lean_object* v_res_2954_; 
v_sz_boxed_2952_ = lean_unbox_usize(v_sz_2949_);
lean_dec(v_sz_2949_);
v_i_boxed_2953_ = lean_unbox_usize(v_i_2950_);
lean_dec(v_i_2950_);
v_res_2954_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__2(v_sz_boxed_2952_, v_i_boxed_2953_, v_bs_2951_);
return v_res_2954_;
}
}
static lean_object* _init_l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__1(void){
_start:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2956_ = ((lean_object*)(l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__0));
v___x_2957_ = l_Lean_stringToMessageData(v___x_2956_);
return v___x_2957_;
}
}
static lean_object* _init_l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__3(void){
_start:
{
lean_object* v___x_2959_; lean_object* v_dummy_2960_; 
v___x_2959_ = lean_box(0);
v_dummy_2960_ = l_Lean_Expr_sort___override(v___x_2959_);
return v_dummy_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfSpecLemmaInstance(lean_object* v_ctorApp_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_){
_start:
{
lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___x_2976_; 
v___x_2976_ = l_Lean_Expr_getAppFn(v_ctorApp_2961_);
if (lean_obj_tag(v___x_2976_) == 4)
{
lean_object* v_declName_2977_; lean_object* v___x_2978_; lean_object* v_env_2979_; uint8_t v___x_2980_; lean_object* v___x_2981_; 
v_declName_2977_ = lean_ctor_get(v___x_2976_, 0);
lean_inc(v_declName_2977_);
lean_dec_ref(v___x_2976_);
v___x_2978_ = lean_st_ref_get(v_a_2965_);
v_env_2979_ = lean_ctor_get(v___x_2978_, 0);
lean_inc_ref(v_env_2979_);
lean_dec(v___x_2978_);
v___x_2980_ = 0;
v___x_2981_ = l_Lean_Environment_find_x3f(v_env_2979_, v_declName_2977_, v___x_2980_);
if (lean_obj_tag(v___x_2981_) == 0)
{
v___y_2968_ = v_a_2962_;
v___y_2969_ = v_a_2963_;
v___y_2970_ = v_a_2964_;
v___y_2971_ = v_a_2965_;
goto v___jp_2967_;
}
else
{
lean_object* v_val_2982_; 
v_val_2982_ = lean_ctor_get(v___x_2981_, 0);
lean_inc(v_val_2982_);
lean_dec_ref(v___x_2981_);
if (lean_obj_tag(v_val_2982_) == 6)
{
lean_object* v_val_2983_; lean_object* v_toConstantVal_2984_; lean_object* v_numParams_2985_; lean_object* v_numFields_2986_; lean_object* v_nargs_2987_; lean_object* v___f_2988_; lean_object* v_dummy_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v_ctorArgs_2993_; lean_object* v___x_2994_; lean_object* v_ctorParams_2995_; lean_object* v___y_2997_; lean_object* v___x_3039_; uint8_t v___x_3040_; 
v_val_2983_ = lean_ctor_get(v_val_2982_, 0);
lean_inc_ref(v_val_2983_);
lean_dec_ref(v_val_2982_);
v_toConstantVal_2984_ = lean_ctor_get(v_val_2983_, 0);
lean_inc_ref(v_toConstantVal_2984_);
v_numParams_2985_ = lean_ctor_get(v_val_2983_, 3);
lean_inc(v_numParams_2985_);
v_numFields_2986_ = lean_ctor_get(v_val_2983_, 4);
lean_inc(v_numFields_2986_);
lean_dec_ref(v_val_2983_);
v_nargs_2987_ = l_Lean_Expr_getAppNumArgs(v_ctorApp_2961_);
v___f_2988_ = ((lean_object*)(l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__2));
v_dummy_2989_ = lean_obj_once(&l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__3, &l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__3_once, _init_l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__3);
lean_inc(v_nargs_2987_);
v___x_2990_ = lean_mk_array(v_nargs_2987_, v_dummy_2989_);
v___x_2991_ = lean_unsigned_to_nat(1u);
v___x_2992_ = lean_nat_sub(v_nargs_2987_, v___x_2991_);
lean_dec(v_nargs_2987_);
v_ctorArgs_2993_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_ctorApp_2961_, v___x_2990_, v___x_2992_);
v___x_2994_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2985_);
lean_inc_ref(v_ctorArgs_2993_);
v_ctorParams_2995_ = l_Array_toSubarray___redArg(v_ctorArgs_2993_, v___x_2994_, v_numParams_2985_);
v___x_3039_ = lean_array_get_size(v_ctorArgs_2993_);
v___x_3040_ = lean_nat_dec_le(v_numParams_2985_, v___x_2994_);
if (v___x_3040_ == 0)
{
lean_object* v___x_3041_; 
lean_inc(v_numParams_2985_);
v___x_3041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3041_, 0, v_numParams_2985_);
lean_ctor_set(v___x_3041_, 1, v___x_3039_);
v___y_2997_ = v___x_3041_;
goto v___jp_2996_;
}
else
{
lean_object* v___x_3042_; 
v___x_3042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3042_, 0, v___x_2994_);
lean_ctor_set(v___x_3042_, 1, v___x_3039_);
v___y_2997_ = v___x_3042_;
goto v___jp_2996_;
}
v___jp_2996_:
{
lean_object* v_name_2998_; lean_object* v_lemmaName_2999_; lean_object* v___x_3000_; 
v_name_2998_ = lean_ctor_get(v_toConstantVal_2984_, 0);
lean_inc(v_name_2998_);
lean_dec_ref(v_toConstantVal_2984_);
v_lemmaName_2999_ = l_Lean_Meta_mkSizeOfSpecLemmaName(v_name_2998_);
lean_inc(v_lemmaName_2999_);
v___x_3000_ = l_Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0(v_lemmaName_2999_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v_a_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
lean_inc(v_a_3001_);
lean_dec_ref(v___x_3000_);
v___x_3002_ = l_Lean_ConstantInfo_type(v_a_3001_);
lean_dec(v_a_3001_);
v___x_3003_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__0___redArg(v___x_3002_, v___f_2988_, v___x_2980_, v___x_2980_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v_a_3004_; lean_object* v_lower_3005_; lean_object* v_upper_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; size_t v_sz_3010_; size_t v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; size_t v_sz_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3004_);
lean_dec_ref(v___x_3003_);
v_lower_3005_ = lean_ctor_get(v___y_2997_, 0);
lean_inc(v_lower_3005_);
v_upper_3006_ = lean_ctor_get(v___y_2997_, 1);
lean_inc(v_upper_3006_);
lean_dec_ref(v___y_2997_);
v___x_3007_ = l_Array_toSubarray___redArg(v_ctorArgs_2993_, v_lower_3005_, v_upper_3006_);
v___x_3008_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances___redArg___closed__0));
v___x_3009_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__1___redArg(v_ctorParams_2995_, v___x_3008_);
v_sz_3010_ = lean_array_size(v___x_3009_);
v___x_3011_ = ((size_t)0ULL);
v___x_3012_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__2(v_sz_3010_, v___x_3011_, v___x_3009_);
v___x_3013_ = lean_nat_sub(v_a_3004_, v_numParams_2985_);
lean_dec(v_numParams_2985_);
lean_dec(v_a_3004_);
v___x_3014_ = lean_nat_sub(v___x_3013_, v_numFields_2986_);
lean_dec(v_numFields_2986_);
lean_dec(v___x_3013_);
v___x_3015_ = lean_box(0);
v___x_3016_ = lean_mk_array(v___x_3014_, v___x_3015_);
v___x_3017_ = l_Array_append___redArg(v___x_3012_, v___x_3016_);
lean_dec_ref(v___x_3016_);
v___x_3018_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__1___redArg(v___x_3007_, v___x_3008_);
v_sz_3019_ = lean_array_size(v___x_3018_);
v___x_3020_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__2(v_sz_3019_, v___x_3011_, v___x_3018_);
v___x_3021_ = l_Array_append___redArg(v___x_3017_, v___x_3020_);
lean_dec_ref(v___x_3020_);
v___x_3022_ = l_Lean_Meta_mkAppOptM(v_lemmaName_2999_, v___x_3021_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_);
return v___x_3022_;
}
else
{
lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3030_; 
lean_dec(v_lemmaName_2999_);
lean_dec_ref(v___y_2997_);
lean_dec_ref(v_ctorParams_2995_);
lean_dec_ref(v_ctorArgs_2993_);
lean_dec(v_numFields_2986_);
lean_dec(v_numParams_2985_);
v_a_3023_ = lean_ctor_get(v___x_3003_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3025_ = v___x_3003_;
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v___x_3003_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
if (v_isShared_3026_ == 0)
{
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3023_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
else
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3038_; 
lean_dec(v_lemmaName_2999_);
lean_dec_ref(v___y_2997_);
lean_dec_ref(v_ctorParams_2995_);
lean_dec_ref(v_ctorArgs_2993_);
lean_dec(v_numFields_2986_);
lean_dec(v_numParams_2985_);
v_a_3031_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3033_ = v___x_3000_;
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_3000_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3036_; 
if (v_isShared_3034_ == 0)
{
v___x_3036_ = v___x_3033_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3031_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
}
}
}
else
{
lean_dec(v_val_2982_);
v___y_2968_ = v_a_2962_;
v___y_2969_ = v_a_2963_;
v___y_2970_ = v_a_2964_;
v___y_2971_ = v_a_2965_;
goto v___jp_2967_;
}
}
}
else
{
lean_dec_ref(v___x_2976_);
v___y_2968_ = v_a_2962_;
v___y_2969_ = v_a_2963_;
v___y_2970_ = v_a_2964_;
v___y_2971_ = v_a_2965_;
goto v___jp_2967_;
}
v___jp_2967_:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2972_ = lean_obj_once(&l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__1, &l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__1_once, _init_l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__1);
v___x_2973_ = l_Lean_indentExpr(v_ctorApp_2961_);
v___x_2974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2972_);
lean_ctor_set(v___x_2974_, 1, v___x_2973_);
v___x_2975_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__0___redArg(v___x_2974_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_);
return v___x_2975_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfSpecLemmaInstance___boxed(lean_object* v_ctorApp_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l_Lean_Meta_mkSizeOfSpecLemmaInstance(v_ctorApp_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_);
lean_dec(v_a_3047_);
lean_dec_ref(v_a_3046_);
lean_dec(v_a_3045_);
lean_dec_ref(v_a_3044_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__1(lean_object* v_inst_3050_, lean_object* v_R_3051_, lean_object* v_a_3052_, lean_object* v_b_3053_){
_start:
{
lean_object* v___x_3054_; 
v___x_3054_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__1___redArg(v_a_3052_, v_b_3053_);
return v___x_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0(lean_object* v_00_u03b1_3055_, lean_object* v_constName_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_){
_start:
{
lean_object* v___x_3062_; 
v___x_3062_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0___redArg(v_constName_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3063_, lean_object* v_constName_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0(v_00_u03b1_3063_, v_constName_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3071_, lean_object* v_ref_3072_, lean_object* v_constName_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_){
_start:
{
lean_object* v___x_3079_; 
v___x_3079_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1___redArg(v_ref_3072_, v_constName_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_);
return v___x_3079_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3080_, lean_object* v_ref_3081_, lean_object* v_constName_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1(v_00_u03b1_3080_, v_ref_3081_, v_constName_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v_ref_3081_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_3089_, lean_object* v_ref_3090_, lean_object* v_msg_3091_, lean_object* v_declHint_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_){
_start:
{
lean_object* v___x_3098_; 
v___x_3098_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_3090_, v_msg_3091_, v_declHint_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
return v___x_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_3099_, lean_object* v_ref_3100_, lean_object* v_msg_3101_, lean_object* v_declHint_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_){
_start:
{
lean_object* v_res_3108_; 
v_res_3108_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_3099_, v_ref_3100_, v_msg_3101_, v_declHint_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
lean_dec(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec(v_ref_3100_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_3109_, lean_object* v_declHint_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_){
_start:
{
lean_object* v___x_3116_; 
v___x_3116_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_3109_, v_declHint_3110_, v___y_3114_);
return v___x_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_3117_, lean_object* v_declHint_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
lean_object* v_res_3124_; 
v_res_3124_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_3117_, v_declHint_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
lean_dec(v___y_3122_);
lean_dec_ref(v___y_3121_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_3125_, lean_object* v_ref_3126_, lean_object* v_msg_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_){
_start:
{
lean_object* v___x_3133_; 
v___x_3133_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_3126_, v_msg_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
return v___x_3133_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_3134_, lean_object* v_ref_3135_, lean_object* v_msg_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
lean_object* v_res_3142_; 
v_res_3142_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSizeOfSpecLemmaInstance_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_3134_, v_ref_3135_, v_msg_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v_ref_3135_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SizeOfSpecNested_throwUnexpected_spec__0___redArg(lean_object* v_msg_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_){
_start:
{
lean_object* v_ref_3149_; lean_object* v___x_3150_; lean_object* v_a_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3159_; 
v_ref_3149_ = lean_ctor_get(v___y_3146_, 5);
v___x_3150_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1_spec__1(v_msg_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_);
v_a_3151_ = lean_ctor_get(v___x_3150_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3153_ = v___x_3150_;
v_isShared_3154_ = v_isSharedCheck_3159_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_a_3151_);
lean_dec(v___x_3150_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3159_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v___x_3155_; lean_object* v___x_3157_; 
lean_inc(v_ref_3149_);
v___x_3155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3155_, 0, v_ref_3149_);
lean_ctor_set(v___x_3155_, 1, v_a_3151_);
if (v_isShared_3154_ == 0)
{
lean_ctor_set_tag(v___x_3153_, 1);
lean_ctor_set(v___x_3153_, 0, v___x_3155_);
v___x_3157_ = v___x_3153_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v___x_3155_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SizeOfSpecNested_throwUnexpected_spec__0___redArg___boxed(lean_object* v_msg_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
lean_object* v_res_3166_; 
v_res_3166_ = l_Lean_throwError___at___00Lean_Meta_SizeOfSpecNested_throwUnexpected_spec__0___redArg(v_msg_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
return v_res_3166_;
}
}
static lean_object* _init_l_Lean_Meta_SizeOfSpecNested_throwUnexpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3168_ = ((lean_object*)(l_Lean_Meta_SizeOfSpecNested_throwUnexpected___redArg___closed__0));
v___x_3169_ = l_Lean_stringToMessageData(v___x_3168_);
return v___x_3169_;
}
}
static lean_object* _init_l_Lean_Meta_SizeOfSpecNested_throwUnexpected___redArg___closed__3(void){
_start:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3171_ = ((lean_object*)(l_Lean_Meta_SizeOfSpecNested_throwUnexpected___redArg___closed__2));
v___x_3172_ = l_Lean_stringToMessageData(v___x_3171_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SizeOfSpecNested_throwUnexpected___redArg(lean_object* v_msg_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_){
_start:
{
lean_object* v_ctorName_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
v_ctorName_3180_ = lean_ctor_get(v_a_3174_, 2);
lean_inc(v_ctorName_3180_);
lean_dec_ref(v_a_3174_);
v___x_3181_ = lean_obj_once(&l_Lean_Meta_SizeOfSpecNested_throwUnexpected___redArg___closed__1, &l_Lean_Meta_SizeOfSpecNested_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_SizeOfSpecNested_throwUnexpected___redArg___closed__1);
v___x_3182_ = l_Lean_MessageData_ofName(v_ctorName_3180_);
v___x_3183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3181_);
lean_ctor_set(v___x_3183_, 1, v___x_3182_);
v___x_3184_ = lean_obj_once(&l_Lean_Meta_SizeOfSpecNested_throwUnexpected___redArg___closed__3, &l_Lean_Meta_SizeOfSpecNested_throwUnexpected___redArg___closed__3_once, _init_l_Lean_Meta_SizeOfSpecNested_throwUnexpected___redArg___closed__3);
v___x_3185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3183_);
lean_ctor_set(v___x_3185_, 1, v___x_3184_);
v___x_3186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3186_, 0, v___x_3185_);
lean_ctor_set(v___x_3186_, 1, v_msg_3173_);
v___x_3187_ = l_Lean_throwError___at___00Lean_Meta_SizeOfSpecNested_throwUnexpected_spec__0___redArg(v___x_3186_, v_a_3175_, v_a_3176_, v_a_3177_, v_a_3178_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SizeOfSpecNested_throwUnexpected___redArg___boxed(lean_object* v_msg_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_){
_start:
{
lean_object* v_res_3195_; 
v_res_3195_ = l_Lean_Meta_SizeOfSpecNested_throwUnexpected___redArg(v_msg_3188_, v_a_3189_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_);
lean_dec(v_a_3193_);
lean_dec_ref(v_a_3192_);
lean_dec(v_a_3191_);
lean_dec_ref(v_a_3190_);
return v_res_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SizeOfSpecNested_throwUnexpected(lean_object* v_00_u03b1_3196_, lean_object* v_msg_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_){
_start:
{
lean_object* v___x_3204_; 
lean_inc_ref(v_a_3198_);
v___x_3204_ = l_Lean_Meta_SizeOfSpecNested_throwUnexpected___redArg(v_msg_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_, v_a_3202_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SizeOfSpecNested_throwUnexpected___boxed(lean_object* v_00_u03b1_3205_, lean_object* v_msg_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l_Lean_Meta_SizeOfSpecNested_throwUnexpected(v_00_u03b1_3205_, v_msg_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_);
lean_dec(v_a_3211_);
lean_dec_ref(v_a_3210_);
lean_dec(v_a_3209_);
lean_dec_ref(v_a_3208_);
lean_dec_ref(v_a_3207_);
return v_res_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SizeOfSpecNested_throwUnexpected_spec__0(lean_object* v_00_u03b1_3214_, lean_object* v_msg_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_){
_start:
{
lean_object* v___x_3222_; 
v___x_3222_ = l_Lean_throwError___at___00Lean_Meta_SizeOfSpecNested_throwUnexpected_spec__0___redArg(v_msg_3215_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SizeOfSpecNested_throwUnexpected_spec__0___boxed(lean_object* v_00_u03b1_3223_, lean_object* v_msg_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_){
_start:
{
lean_object* v_res_3231_; 
v_res_3231_ = l_Lean_throwError___at___00Lean_Meta_SizeOfSpecNested_throwUnexpected_spec__0(v_00_u03b1_3223_, v_msg_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec_ref(v___y_3225_);
return v_res_3231_;
}
}
static lean_object* _init_l_Lean_Meta_SizeOfSpecNested_throwFailed___redArg___closed__1(void){
_start:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3233_ = ((lean_object*)(l_Lean_Meta_SizeOfSpecNested_throwFailed___redArg___closed__0));
v___x_3234_ = l_Lean_stringToMessageData(v___x_3233_);
return v___x_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SizeOfSpecNested_throwFailed___redArg(lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_){
_start:
{
lean_object* v_ctorName_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
v_ctorName_3241_ = lean_ctor_get(v_a_3235_, 2);
lean_inc(v_ctorName_3241_);
lean_dec_ref(v_a_3235_);
v___x_3242_ = lean_obj_once(&l_Lean_Meta_SizeOfSpecNested_throwUnexpected___redArg___closed__1, &l_Lean_Meta_SizeOfSpecNested_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_SizeOfSpecNested_throwUnexpected___redArg___closed__1);
v___x_3243_ = l_Lean_MessageData_ofName(v_ctorName_3241_);
v___x_3244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3242_);
lean_ctor_set(v___x_3244_, 1, v___x_3243_);
v___x_3245_ = lean_obj_once(&l_Lean_Meta_SizeOfSpecNested_throwFailed___redArg___closed__1, &l_Lean_Meta_SizeOfSpecNested_throwFailed___redArg___closed__1_once, _init_l_Lean_Meta_SizeOfSpecNested_throwFailed___redArg___closed__1);
v___x_3246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3244_);
lean_ctor_set(v___x_3246_, 1, v___x_3245_);
v___x_3247_ = l_Lean_throwError___at___00Lean_Meta_SizeOfSpecNested_throwUnexpected_spec__0___redArg(v___x_3246_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SizeOfSpecNested_throwFailed___redArg___boxed(lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_){
_start:
{
lean_object* v_res_3254_; 
v_res_3254_ = l_Lean_Meta_SizeOfSpecNested_throwFailed___redArg(v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_);
lean_dec(v_a_3252_);
lean_dec_ref(v_a_3251_);
lean_dec(v_a_3250_);
lean_dec_ref(v_a_3249_);
return v_res_3254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SizeOfSpecNested_throwFailed(lean_object* v_00_u03b1_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_){
_start:
{
lean_object* v___x_3262_; 
lean_inc_ref(v_a_3256_);
v___x_3262_ = l_Lean_Meta_SizeOfSpecNested_throwFailed___redArg(v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SizeOfSpecNested_throwFailed___boxed(lean_object* v_00_u03b1_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_){
_start:
{
lean_object* v_res_3270_; 
v_res_3270_ = l_Lean_Meta_SizeOfSpecNested_throwFailed(v_00_u03b1_3263_, v_a_3264_, v_a_3265_, v_a_3266_, v_a_3267_, v_a_3268_);
lean_dec(v_a_3268_);
lean_dec_ref(v_a_3267_);
lean_dec(v_a_3266_);
lean_dec_ref(v_a_3265_);
lean_dec_ref(v_a_3264_);
return v_res_3270_;
}
}
static lean_object* _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_recToSizeOf___closed__1(void){
_start:
{
lean_object* v___x_3272_; lean_object* v___x_3273_; 
v___x_3272_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_recToSizeOf___closed__0));
v___x_3273_ = l_Lean_stringToMessageData(v___x_3272_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_recToSizeOf(lean_object* v_e_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_){
_start:
{
lean_object* v___x_3281_; 
v___x_3281_ = l_Lean_Expr_getAppFn(v_e_3274_);
if (lean_obj_tag(v___x_3281_) == 4)
{
lean_object* v_declName_3282_; lean_object* v_us_3283_; lean_object* v___x_3284_; lean_object* v_env_3285_; uint8_t v___x_3286_; lean_object* v___x_3287_; 
v_declName_3282_ = lean_ctor_get(v___x_3281_, 0);
lean_inc(v_declName_3282_);
v_us_3283_ = lean_ctor_get(v___x_3281_, 1);
lean_inc(v_us_3283_);
lean_dec_ref(v___x_3281_);
v___x_3284_ = lean_st_ref_get(v_a_3279_);
v_env_3285_ = lean_ctor_get(v___x_3284_, 0);
lean_inc_ref(v_env_3285_);
lean_dec(v___x_3284_);
v___x_3286_ = 0;
v___x_3287_ = l_Lean_Environment_find_x3f(v_env_3285_, v_declName_3282_, v___x_3286_);
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_object* v___x_3288_; 
lean_dec(v_us_3283_);
lean_dec_ref(v_e_3274_);
v___x_3288_ = l_Lean_Meta_SizeOfSpecNested_throwFailed___redArg(v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_);
return v___x_3288_;
}
else
{
lean_object* v_val_3289_; 
v_val_3289_ = lean_ctor_get(v___x_3287_, 0);
lean_inc(v_val_3289_);
lean_dec_ref(v___x_3287_);
if (lean_obj_tag(v_val_3289_) == 7)
{
lean_object* v_val_3290_; lean_object* v_toConstantVal_3291_; lean_object* v_params_3292_; lean_object* v_localInsts_3293_; lean_object* v_recMap_3294_; lean_object* v_numIndices_3295_; lean_object* v_name_3296_; lean_object* v___x_3297_; 
v_val_3290_ = lean_ctor_get(v_val_3289_, 0);
lean_inc_ref(v_val_3290_);
lean_dec_ref(v_val_3289_);
v_toConstantVal_3291_ = lean_ctor_get(v_val_3290_, 0);
v_params_3292_ = lean_ctor_get(v_a_3275_, 3);
v_localInsts_3293_ = lean_ctor_get(v_a_3275_, 4);
v_recMap_3294_ = lean_ctor_get(v_a_3275_, 5);
v_numIndices_3295_ = lean_ctor_get(v_val_3290_, 3);
v_name_3296_ = lean_ctor_get(v_toConstantVal_3291_, 0);
v___x_3297_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_recMap_3294_, v_name_3296_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
lean_dec_ref(v_val_3290_);
lean_dec(v_us_3283_);
v___x_3298_ = lean_obj_once(&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_recToSizeOf___closed__1, &l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_recToSizeOf___closed__1_once, _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_recToSizeOf___closed__1);
v___x_3299_ = l_Lean_indentExpr(v_e_3274_);
v___x_3300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3298_);
lean_ctor_set(v___x_3300_, 1, v___x_3299_);
v___x_3301_ = l_Lean_Meta_SizeOfSpecNested_throwUnexpected___redArg(v___x_3300_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_);
return v___x_3301_;
}
else
{
lean_object* v_val_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3330_; 
lean_inc_ref(v_localInsts_3293_);
lean_inc_ref(v_params_3292_);
lean_dec_ref(v_a_3275_);
v_val_3302_ = lean_ctor_get(v___x_3297_, 0);
v_isSharedCheck_3330_ = !lean_is_exclusive(v___x_3297_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3304_ = v___x_3297_;
v_isShared_3305_ = v_isSharedCheck_3330_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_val_3302_);
lean_dec(v___x_3297_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3330_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3306_; lean_object* v_dummy_3307_; lean_object* v_nargs_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3328_; 
v___x_3306_ = l_Lean_instInhabitedExpr;
v_dummy_3307_ = lean_obj_once(&l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__3, &l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__3_once, _init_l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__3);
v_nargs_3308_ = l_Lean_Expr_getAppNumArgs(v_e_3274_);
lean_inc(v_nargs_3308_);
v___x_3309_ = lean_mk_array(v_nargs_3308_, v_dummy_3307_);
v___x_3310_ = lean_unsigned_to_nat(1u);
v___x_3311_ = lean_nat_sub(v_nargs_3308_, v___x_3310_);
lean_dec(v_nargs_3308_);
v___x_3312_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3274_, v___x_3309_, v___x_3311_);
v___x_3313_ = l_Lean_RecursorVal_getFirstIndexIdx(v_val_3290_);
v___x_3314_ = lean_nat_add(v___x_3313_, v_numIndices_3295_);
lean_inc_ref(v___x_3312_);
v___x_3315_ = l_Array_toSubarray___redArg(v___x_3312_, v___x_3313_, v___x_3314_);
v___x_3316_ = l_Lean_RecursorVal_getMajorIdx(v_val_3290_);
lean_dec_ref(v_val_3290_);
v___x_3317_ = lean_array_get(v___x_3306_, v___x_3312_, v___x_3316_);
lean_dec(v___x_3316_);
lean_dec_ref(v___x_3312_);
v___x_3318_ = l_List_tail_x21___redArg(v_us_3283_);
lean_dec(v_us_3283_);
v___x_3319_ = l_Lean_mkConst(v_val_3302_, v___x_3318_);
v___x_3320_ = l_Array_append___redArg(v_params_3292_, v_localInsts_3293_);
lean_dec_ref(v_localInsts_3293_);
v___x_3321_ = l_Subarray_copy___redArg(v___x_3315_);
v___x_3322_ = l_Array_append___redArg(v___x_3320_, v___x_3321_);
lean_dec_ref(v___x_3321_);
v___x_3323_ = lean_mk_empty_array_with_capacity(v___x_3310_);
v___x_3324_ = lean_array_push(v___x_3323_, v___x_3317_);
v___x_3325_ = l_Array_append___redArg(v___x_3322_, v___x_3324_);
lean_dec_ref(v___x_3324_);
v___x_3326_ = l_Lean_mkAppN(v___x_3319_, v___x_3325_);
lean_dec_ref(v___x_3325_);
if (v_isShared_3305_ == 0)
{
lean_ctor_set_tag(v___x_3304_, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3326_);
v___x_3328_ = v___x_3304_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v___x_3326_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
}
}
else
{
lean_object* v___x_3331_; 
lean_dec(v_val_3289_);
lean_dec(v_us_3283_);
lean_dec_ref(v_e_3274_);
v___x_3331_ = l_Lean_Meta_SizeOfSpecNested_throwFailed___redArg(v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_);
return v___x_3331_;
}
}
}
else
{
lean_object* v___x_3332_; 
lean_dec_ref(v___x_3281_);
lean_dec_ref(v_e_3274_);
v___x_3332_ = l_Lean_Meta_SizeOfSpecNested_throwFailed___redArg(v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_);
return v___x_3332_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_recToSizeOf___boxed(lean_object* v_e_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_recToSizeOf(v_e_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_);
lean_dec(v_a_3338_);
lean_dec_ref(v_a_3337_);
lean_dec(v_a_3336_);
lean_dec_ref(v_a_3335_);
return v_res_3340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_mkSizeOf_spec__0___redArg(lean_object* v_sizeOfLevels_3344_, lean_object* v_sizeOfBaseArgs_3345_, lean_object* v_ys_3346_, lean_object* v_as_3347_, size_t v_sz_3348_, size_t v_i_3349_, lean_object* v_b_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_){
_start:
{
uint8_t v___x_3356_; 
v___x_3356_ = lean_usize_dec_lt(v_i_3349_, v_sz_3348_);
if (v___x_3356_ == 0)
{
lean_object* v___x_3357_; 
lean_dec_ref(v_sizeOfBaseArgs_3345_);
lean_dec(v_sizeOfLevels_3344_);
v___x_3357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3357_, 0, v_b_3350_);
return v___x_3357_;
}
else
{
lean_object* v_a_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
lean_dec_ref(v_b_3350_);
v_a_3358_ = lean_array_uget_borrowed(v_as_3347_, v_i_3349_);
lean_inc(v_sizeOfLevels_3344_);
lean_inc(v_a_3358_);
v___x_3359_ = l_Lean_mkConst(v_a_3358_, v_sizeOfLevels_3344_);
lean_inc_ref(v_sizeOfBaseArgs_3345_);
v___x_3360_ = l_Subarray_copy___redArg(v_sizeOfBaseArgs_3345_);
v___x_3361_ = l_Lean_mkAppN(v___x_3359_, v___x_3360_);
lean_dec_ref(v___x_3360_);
v___x_3362_ = l_Lean_mkAppN(v___x_3361_, v_ys_3346_);
lean_inc_ref(v___x_3362_);
v___x_3363_ = l_Lean_Meta_isTypeCorrect(v___x_3362_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_object* v_a_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3379_; 
v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3379_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3366_ = v___x_3363_;
v_isShared_3367_ = v_isSharedCheck_3379_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_a_3364_);
lean_dec(v___x_3363_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3379_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3368_; uint8_t v___x_3369_; 
v___x_3368_ = lean_box(0);
v___x_3369_ = lean_unbox(v_a_3364_);
lean_dec(v_a_3364_);
if (v___x_3369_ == 0)
{
lean_object* v___x_3370_; size_t v___x_3371_; size_t v___x_3372_; 
lean_del_object(v___x_3366_);
lean_dec_ref(v___x_3362_);
v___x_3370_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_mkSizeOf_spec__0___redArg___closed__0));
v___x_3371_ = ((size_t)1ULL);
v___x_3372_ = lean_usize_add(v_i_3349_, v___x_3371_);
v_i_3349_ = v___x_3372_;
v_b_3350_ = v___x_3370_;
goto _start;
}
else
{
lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3377_; 
lean_dec_ref(v_sizeOfBaseArgs_3345_);
lean_dec(v_sizeOfLevels_3344_);
v___x_3374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3362_);
v___x_3375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3374_);
lean_ctor_set(v___x_3375_, 1, v___x_3368_);
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 0, v___x_3375_);
v___x_3377_ = v___x_3366_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3375_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
}
}
}
}
else
{
lean_object* v_a_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3387_; 
lean_dec_ref(v___x_3362_);
lean_dec_ref(v_sizeOfBaseArgs_3345_);
lean_dec(v_sizeOfLevels_3344_);
v_a_3380_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3382_ = v___x_3363_;
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_a_3380_);
lean_dec(v___x_3363_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3385_; 
if (v_isShared_3383_ == 0)
{
v___x_3385_ = v___x_3382_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_a_3380_);
v___x_3385_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
return v___x_3385_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_mkSizeOf_spec__0___redArg___boxed(lean_object* v_sizeOfLevels_3388_, lean_object* v_sizeOfBaseArgs_3389_, lean_object* v_ys_3390_, lean_object* v_as_3391_, lean_object* v_sz_3392_, lean_object* v_i_3393_, lean_object* v_b_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_){
_start:
{
size_t v_sz_boxed_3400_; size_t v_i_boxed_3401_; lean_object* v_res_3402_; 
v_sz_boxed_3400_ = lean_unbox_usize(v_sz_3392_);
lean_dec(v_sz_3392_);
v_i_boxed_3401_ = lean_unbox_usize(v_i_3393_);
lean_dec(v_i_3393_);
v_res_3402_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_mkSizeOf_spec__0___redArg(v_sizeOfLevels_3388_, v_sizeOfBaseArgs_3389_, v_ys_3390_, v_as_3391_, v_sz_boxed_3400_, v_i_boxed_3401_, v_b_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_);
lean_dec(v___y_3398_);
lean_dec_ref(v___y_3397_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3395_);
lean_dec_ref(v_as_3391_);
lean_dec_ref(v_ys_3390_);
return v_res_3402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_mkSizeOf(lean_object* v_sizeOfBaseArgs_3403_, lean_object* v_sizeOfLevels_3404_, lean_object* v_ys_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_){
_start:
{
lean_object* v_sizeOfFns_3412_; lean_object* v___x_3413_; size_t v_sz_3414_; size_t v___x_3415_; lean_object* v___x_3416_; 
v_sizeOfFns_3412_ = lean_ctor_get(v_a_3406_, 1);
v___x_3413_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_mkSizeOf_spec__0___redArg___closed__0));
v_sz_3414_ = lean_array_size(v_sizeOfFns_3412_);
v___x_3415_ = ((size_t)0ULL);
v___x_3416_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_mkSizeOf_spec__0___redArg(v_sizeOfLevels_3404_, v_sizeOfBaseArgs_3403_, v_ys_3405_, v_sizeOfFns_3412_, v_sz_3414_, v___x_3415_, v___x_3413_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3427_; 
v_a_3417_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3419_ = v___x_3416_;
v_isShared_3420_ = v_isSharedCheck_3427_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3416_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3427_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v_fst_3421_; 
v_fst_3421_ = lean_ctor_get(v_a_3417_, 0);
lean_inc(v_fst_3421_);
lean_dec(v_a_3417_);
if (lean_obj_tag(v_fst_3421_) == 0)
{
lean_object* v___x_3422_; 
lean_del_object(v___x_3419_);
lean_inc_ref(v_a_3406_);
v___x_3422_ = l_Lean_Meta_SizeOfSpecNested_throwFailed___redArg(v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
return v___x_3422_;
}
else
{
lean_object* v_val_3423_; lean_object* v___x_3425_; 
v_val_3423_ = lean_ctor_get(v_fst_3421_, 0);
lean_inc(v_val_3423_);
lean_dec_ref(v_fst_3421_);
if (v_isShared_3420_ == 0)
{
lean_ctor_set(v___x_3419_, 0, v_val_3423_);
v___x_3425_ = v___x_3419_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_val_3423_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
return v___x_3425_;
}
}
}
}
else
{
lean_object* v_a_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3435_; 
v_a_3428_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3430_ = v___x_3416_;
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_a_3428_);
lean_dec(v___x_3416_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3433_; 
if (v_isShared_3431_ == 0)
{
v___x_3433_ = v___x_3430_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_a_3428_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_mkSizeOf___boxed(lean_object* v_sizeOfBaseArgs_3436_, lean_object* v_sizeOfLevels_3437_, lean_object* v_ys_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_){
_start:
{
lean_object* v_res_3445_; 
v_res_3445_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_mkSizeOf(v_sizeOfBaseArgs_3436_, v_sizeOfLevels_3437_, v_ys_3438_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_);
lean_dec(v_a_3443_);
lean_dec_ref(v_a_3442_);
lean_dec(v_a_3441_);
lean_dec_ref(v_a_3440_);
lean_dec_ref(v_a_3439_);
lean_dec_ref(v_ys_3438_);
return v_res_3445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_mkSizeOf_spec__0(lean_object* v_sizeOfLevels_3446_, lean_object* v_sizeOfBaseArgs_3447_, lean_object* v_ys_3448_, lean_object* v_as_3449_, size_t v_sz_3450_, size_t v_i_3451_, lean_object* v_b_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
lean_object* v___x_3459_; 
v___x_3459_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_mkSizeOf_spec__0___redArg(v_sizeOfLevels_3446_, v_sizeOfBaseArgs_3447_, v_ys_3448_, v_as_3449_, v_sz_3450_, v_i_3451_, v_b_3452_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
return v___x_3459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_mkSizeOf_spec__0___boxed(lean_object* v_sizeOfLevels_3460_, lean_object* v_sizeOfBaseArgs_3461_, lean_object* v_ys_3462_, lean_object* v_as_3463_, lean_object* v_sz_3464_, lean_object* v_i_3465_, lean_object* v_b_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_){
_start:
{
size_t v_sz_boxed_3473_; size_t v_i_boxed_3474_; lean_object* v_res_3475_; 
v_sz_boxed_3473_ = lean_unbox_usize(v_sz_3464_);
lean_dec(v_sz_3464_);
v_i_boxed_3474_ = lean_unbox_usize(v_i_3465_);
lean_dec(v_i_3465_);
v_res_3475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_mkSizeOf_spec__0(v_sizeOfLevels_3460_, v_sizeOfBaseArgs_3461_, v_ys_3462_, v_as_3463_, v_sz_boxed_3473_, v_i_boxed_3474_, v_b_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
lean_dec(v___y_3471_);
lean_dec_ref(v___y_3470_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec_ref(v___y_3467_);
lean_dec_ref(v_as_3463_);
lean_dec_ref(v_ys_3462_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof_spec__0___redArg(lean_object* v_cls_3476_, lean_object* v___y_3477_){
_start:
{
lean_object* v_options_3479_; uint8_t v_hasTrace_3480_; 
v_options_3479_ = lean_ctor_get(v___y_3477_, 2);
v_hasTrace_3480_ = lean_ctor_get_uint8(v_options_3479_, sizeof(void*)*1);
if (v_hasTrace_3480_ == 0)
{
lean_object* v___x_3481_; lean_object* v___x_3482_; 
lean_dec(v_cls_3476_);
v___x_3481_ = lean_box(v_hasTrace_3480_);
v___x_3482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3482_, 0, v___x_3481_);
return v___x_3482_;
}
else
{
lean_object* v_inheritedTraceOptions_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; uint8_t v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
v_inheritedTraceOptions_3483_ = lean_ctor_get(v___y_3477_, 13);
v___x_3484_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__0___redArg___closed__1));
v___x_3485_ = l_Lean_Name_append(v___x_3484_, v_cls_3476_);
v___x_3486_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3483_, v_options_3479_, v___x_3485_);
lean_dec(v___x_3485_);
v___x_3487_ = lean_box(v___x_3486_);
v___x_3488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3487_);
return v___x_3488_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof_spec__0___redArg___boxed(lean_object* v_cls_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_){
_start:
{
lean_object* v_res_3492_; 
v_res_3492_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof_spec__0___redArg(v_cls_3489_, v___y_3490_);
lean_dec_ref(v___y_3490_);
return v_res_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof_spec__0(lean_object* v_cls_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_){
_start:
{
lean_object* v___x_3500_; 
v___x_3500_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof_spec__0___redArg(v_cls_3493_, v___y_3497_);
return v___x_3500_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof_spec__0___boxed(lean_object* v_cls_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_){
_start:
{
lean_object* v_res_3508_; 
v_res_3508_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof_spec__0(v_cls_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec_ref(v___y_3502_);
return v_res_3508_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof_spec__1___redArg(lean_object* v_cls_3509_, lean_object* v_msg_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_){
_start:
{
lean_object* v_ref_3516_; lean_object* v___x_3517_; lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3562_; 
v_ref_3516_ = lean_ctor_get(v___y_3513_, 5);
v___x_3517_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1_spec__1(v_msg_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_);
v_a_3518_ = lean_ctor_get(v___x_3517_, 0);
v_isSharedCheck_3562_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3520_ = v___x_3517_;
v_isShared_3521_ = v_isSharedCheck_3562_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3517_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3562_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3522_; lean_object* v_traceState_3523_; lean_object* v_env_3524_; lean_object* v_nextMacroScope_3525_; lean_object* v_ngen_3526_; lean_object* v_auxDeclNGen_3527_; lean_object* v_cache_3528_; lean_object* v_messages_3529_; lean_object* v_infoState_3530_; lean_object* v_snapshotTasks_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3561_; 
v___x_3522_ = lean_st_ref_take(v___y_3514_);
v_traceState_3523_ = lean_ctor_get(v___x_3522_, 4);
v_env_3524_ = lean_ctor_get(v___x_3522_, 0);
v_nextMacroScope_3525_ = lean_ctor_get(v___x_3522_, 1);
v_ngen_3526_ = lean_ctor_get(v___x_3522_, 2);
v_auxDeclNGen_3527_ = lean_ctor_get(v___x_3522_, 3);
v_cache_3528_ = lean_ctor_get(v___x_3522_, 5);
v_messages_3529_ = lean_ctor_get(v___x_3522_, 6);
v_infoState_3530_ = lean_ctor_get(v___x_3522_, 7);
v_snapshotTasks_3531_ = lean_ctor_get(v___x_3522_, 8);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3533_ = v___x_3522_;
v_isShared_3534_ = v_isSharedCheck_3561_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_snapshotTasks_3531_);
lean_inc(v_infoState_3530_);
lean_inc(v_messages_3529_);
lean_inc(v_cache_3528_);
lean_inc(v_traceState_3523_);
lean_inc(v_auxDeclNGen_3527_);
lean_inc(v_ngen_3526_);
lean_inc(v_nextMacroScope_3525_);
lean_inc(v_env_3524_);
lean_dec(v___x_3522_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3561_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
uint64_t v_tid_3535_; lean_object* v_traces_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3560_; 
v_tid_3535_ = lean_ctor_get_uint64(v_traceState_3523_, sizeof(void*)*1);
v_traces_3536_ = lean_ctor_get(v_traceState_3523_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v_traceState_3523_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3538_ = v_traceState_3523_;
v_isShared_3539_ = v_isSharedCheck_3560_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_traces_3536_);
lean_dec(v_traceState_3523_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3560_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3540_; double v___x_3541_; uint8_t v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3550_; 
v___x_3540_ = lean_box(0);
v___x_3541_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1___closed__0);
v___x_3542_ = 0;
v___x_3543_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1___closed__1));
v___x_3544_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3544_, 0, v_cls_3509_);
lean_ctor_set(v___x_3544_, 1, v___x_3540_);
lean_ctor_set(v___x_3544_, 2, v___x_3543_);
lean_ctor_set_float(v___x_3544_, sizeof(void*)*3, v___x_3541_);
lean_ctor_set_float(v___x_3544_, sizeof(void*)*3 + 8, v___x_3541_);
lean_ctor_set_uint8(v___x_3544_, sizeof(void*)*3 + 16, v___x_3542_);
v___x_3545_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1___closed__2));
v___x_3546_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3544_);
lean_ctor_set(v___x_3546_, 1, v_a_3518_);
lean_ctor_set(v___x_3546_, 2, v___x_3545_);
lean_inc(v_ref_3516_);
v___x_3547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3547_, 0, v_ref_3516_);
lean_ctor_set(v___x_3547_, 1, v___x_3546_);
v___x_3548_ = l_Lean_PersistentArray_push___redArg(v_traces_3536_, v___x_3547_);
if (v_isShared_3539_ == 0)
{
lean_ctor_set(v___x_3538_, 0, v___x_3548_);
v___x_3550_ = v___x_3538_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v___x_3548_);
lean_ctor_set_uint64(v_reuseFailAlloc_3559_, sizeof(void*)*1, v_tid_3535_);
v___x_3550_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
lean_object* v___x_3552_; 
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 4, v___x_3550_);
v___x_3552_ = v___x_3533_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_env_3524_);
lean_ctor_set(v_reuseFailAlloc_3558_, 1, v_nextMacroScope_3525_);
lean_ctor_set(v_reuseFailAlloc_3558_, 2, v_ngen_3526_);
lean_ctor_set(v_reuseFailAlloc_3558_, 3, v_auxDeclNGen_3527_);
lean_ctor_set(v_reuseFailAlloc_3558_, 4, v___x_3550_);
lean_ctor_set(v_reuseFailAlloc_3558_, 5, v_cache_3528_);
lean_ctor_set(v_reuseFailAlloc_3558_, 6, v_messages_3529_);
lean_ctor_set(v_reuseFailAlloc_3558_, 7, v_infoState_3530_);
lean_ctor_set(v_reuseFailAlloc_3558_, 8, v_snapshotTasks_3531_);
v___x_3552_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3556_; 
v___x_3553_ = lean_st_ref_set(v___y_3514_, v___x_3552_);
v___x_3554_ = lean_box(0);
if (v_isShared_3521_ == 0)
{
lean_ctor_set(v___x_3520_, 0, v___x_3554_);
v___x_3556_ = v___x_3520_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v___x_3554_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof_spec__1___redArg___boxed(lean_object* v_cls_3563_, lean_object* v_msg_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_){
_start:
{
lean_object* v_res_3570_; 
v_res_3570_ = l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof_spec__1___redArg(v_cls_3563_, v_msg_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
return v_res_3570_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep_spec__3___redArg(lean_object* v_a_3571_, lean_object* v_as_3572_, size_t v_sz_3573_, size_t v_i_3574_, lean_object* v_b_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
uint8_t v___x_3581_; 
v___x_3581_ = lean_usize_dec_lt(v_i_3574_, v_sz_3573_);
if (v___x_3581_ == 0)
{
lean_object* v___x_3582_; 
lean_dec_ref(v_a_3571_);
v___x_3582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3582_, 0, v_b_3575_);
return v___x_3582_;
}
else
{
lean_object* v_a_3583_; lean_object* v___x_3584_; 
lean_dec_ref(v_b_3575_);
v_a_3583_ = lean_array_uget_borrowed(v_as_3572_, v_i_3574_);
lean_inc(v___y_3579_);
lean_inc_ref(v___y_3578_);
lean_inc(v___y_3577_);
lean_inc_ref(v___y_3576_);
lean_inc(v_a_3583_);
v___x_3584_ = lean_infer_type(v_a_3583_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_);
if (lean_obj_tag(v___x_3584_) == 0)
{
lean_object* v_a_3585_; lean_object* v___x_3586_; 
v_a_3585_ = lean_ctor_get(v___x_3584_, 0);
lean_inc(v_a_3585_);
lean_dec_ref(v___x_3584_);
lean_inc_ref(v_a_3571_);
v___x_3586_ = l_Lean_Meta_isExprDefEq(v_a_3585_, v_a_3571_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_);
if (lean_obj_tag(v___x_3586_) == 0)
{
lean_object* v_a_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3602_; 
v_a_3587_ = lean_ctor_get(v___x_3586_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3586_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3589_ = v___x_3586_;
v_isShared_3590_ = v_isSharedCheck_3602_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_a_3587_);
lean_dec(v___x_3586_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3602_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v___x_3591_; uint8_t v___x_3592_; 
v___x_3591_ = lean_box(0);
v___x_3592_ = lean_unbox(v_a_3587_);
lean_dec(v_a_3587_);
if (v___x_3592_ == 0)
{
lean_object* v___x_3593_; size_t v___x_3594_; size_t v___x_3595_; 
lean_del_object(v___x_3589_);
v___x_3593_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_mkSizeOf_spec__0___redArg___closed__0));
v___x_3594_ = ((size_t)1ULL);
v___x_3595_ = lean_usize_add(v_i_3574_, v___x_3594_);
v_i_3574_ = v___x_3595_;
v_b_3575_ = v___x_3593_;
goto _start;
}
else
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3600_; 
lean_dec_ref(v_a_3571_);
lean_inc(v_a_3583_);
v___x_3597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3597_, 0, v_a_3583_);
v___x_3598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3597_);
lean_ctor_set(v___x_3598_, 1, v___x_3591_);
if (v_isShared_3590_ == 0)
{
lean_ctor_set(v___x_3589_, 0, v___x_3598_);
v___x_3600_ = v___x_3589_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v___x_3598_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
}
else
{
lean_object* v_a_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3610_; 
lean_dec_ref(v_a_3571_);
v_a_3603_ = lean_ctor_get(v___x_3586_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3586_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3605_ = v___x_3586_;
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_a_3603_);
lean_dec(v___x_3586_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3608_; 
if (v_isShared_3606_ == 0)
{
v___x_3608_ = v___x_3605_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_a_3603_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
}
else
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
lean_dec_ref(v_a_3571_);
v_a_3611_ = lean_ctor_get(v___x_3584_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3584_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v___x_3584_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3584_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
if (v_isShared_3614_ == 0)
{
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3611_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep_spec__3___redArg___boxed(lean_object* v_a_3619_, lean_object* v_as_3620_, lean_object* v_sz_3621_, lean_object* v_i_3622_, lean_object* v_b_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_){
_start:
{
size_t v_sz_boxed_3629_; size_t v_i_boxed_3630_; lean_object* v_res_3631_; 
v_sz_boxed_3629_ = lean_unbox_usize(v_sz_3621_);
lean_dec(v_sz_3621_);
v_i_boxed_3630_ = lean_unbox_usize(v_i_3622_);
lean_dec(v_i_3622_);
v_res_3631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep_spec__3___redArg(v_a_3619_, v_as_3620_, v_sz_boxed_3629_, v_i_boxed_3630_, v_b_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_);
lean_dec(v___y_3627_);
lean_dec_ref(v___y_3626_);
lean_dec(v___y_3625_);
lean_dec_ref(v___y_3624_);
lean_dec_ref(v_as_3620_);
return v_res_3631_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_3637_; lean_object* v___x_3638_; 
v___x_3637_ = l_Lean_maxRecDepthErrorMessage;
v___x_3638_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3638_, 0, v___x_3637_);
return v___x_3638_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___closed__4(void){
_start:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; 
v___x_3639_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___closed__3);
v___x_3640_ = l_Lean_MessageData_ofFormat(v___x_3639_);
return v___x_3640_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; 
v___x_3641_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___closed__4);
v___x_3642_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___closed__2));
v___x_3643_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3642_);
lean_ctor_set(v___x_3643_, 1, v___x_3641_);
return v___x_3643_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg(lean_object* v_ref_3644_){
_start:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; 
v___x_3646_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___closed__5);
v___x_3647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3647_, 0, v_ref_3644_);
lean_ctor_set(v___x_3647_, 1, v___x_3646_);
v___x_3648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3647_);
return v___x_3648_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg___boxed(lean_object* v_ref_3649_, lean_object* v___y_3650_){
_start:
{
lean_object* v_res_3651_; 
v_res_3651_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg(v_ref_3649_);
return v_res_3651_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__5(lean_object* v_x_3652_, lean_object* v_x_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_){
_start:
{
if (lean_obj_tag(v_x_3652_) == 0)
{
lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3660_ = l_List_reverse___redArg(v_x_3653_);
v___x_3661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3660_);
return v___x_3661_;
}
else
{
lean_object* v_head_3662_; lean_object* v_tail_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3683_; 
v_head_3662_ = lean_ctor_get(v_x_3652_, 0);
v_tail_3663_ = lean_ctor_get(v_x_3652_, 1);
v_isSharedCheck_3683_ = !lean_is_exclusive(v_x_3652_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3665_ = v_x_3652_;
v_isShared_3666_ = v_isSharedCheck_3683_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_tail_3663_);
lean_inc(v_head_3662_);
lean_dec(v_x_3652_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3683_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v_a_3668_; 
if (lean_obj_tag(v_head_3662_) == 4)
{
lean_object* v_a_3673_; 
v_a_3673_ = lean_ctor_get(v_head_3662_, 0);
lean_inc(v_a_3673_);
lean_dec_ref(v_head_3662_);
v_a_3668_ = v_a_3673_;
goto v___jp_3667_;
}
else
{
lean_object* v___x_3674_; lean_object* v_a_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3682_; 
lean_del_object(v___x_3665_);
lean_dec(v_tail_3663_);
lean_dec(v_head_3662_);
lean_dec(v_x_3653_);
lean_inc_ref(v___y_3654_);
v___x_3674_ = l_Lean_Meta_SizeOfSpecNested_throwFailed___redArg(v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_);
v_a_3675_ = lean_ctor_get(v___x_3674_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3674_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3677_ = v___x_3674_;
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_a_3675_);
lean_dec(v___x_3674_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v___x_3680_; 
if (v_isShared_3678_ == 0)
{
v___x_3680_ = v___x_3677_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_a_3675_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
v___jp_3667_:
{
lean_object* v___x_3670_; 
if (v_isShared_3666_ == 0)
{
lean_ctor_set(v___x_3665_, 1, v_x_3653_);
lean_ctor_set(v___x_3665_, 0, v_a_3668_);
v___x_3670_ = v___x_3665_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v_a_3668_);
lean_ctor_set(v_reuseFailAlloc_3672_, 1, v_x_3653_);
v___x_3670_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
v_x_3652_ = v_tail_3663_;
v_x_3653_ = v___x_3670_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__5___boxed(lean_object* v_x_3684_, lean_object* v_x_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_){
_start:
{
lean_object* v_res_3692_; 
v_res_3692_ = l_List_mapM_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__5(v_x_3684_, v_x_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_);
lean_dec(v___y_3690_);
lean_dec_ref(v___y_3689_);
lean_dec(v___y_3688_);
lean_dec_ref(v___y_3687_);
lean_dec_ref(v___y_3686_);
return v_res_3692_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__10_spec__11(lean_object* v_msg_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_){
_start:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v_toApplicative_3702_; lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3764_; 
v___x_3700_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__0);
v___x_3701_ = l_StateRefT_x27_instMonad___redArg(v___x_3700_);
v_toApplicative_3702_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3764_ == 0)
{
lean_object* v_unused_3765_; 
v_unused_3765_ = lean_ctor_get(v___x_3701_, 1);
lean_dec(v_unused_3765_);
v___x_3704_ = v___x_3701_;
v_isShared_3705_ = v_isSharedCheck_3764_;
goto v_resetjp_3703_;
}
else
{
lean_inc(v_toApplicative_3702_);
lean_dec(v___x_3701_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3764_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v_toFunctor_3706_; lean_object* v_toSeq_3707_; lean_object* v_toSeqLeft_3708_; lean_object* v_toSeqRight_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3762_; 
v_toFunctor_3706_ = lean_ctor_get(v_toApplicative_3702_, 0);
v_toSeq_3707_ = lean_ctor_get(v_toApplicative_3702_, 2);
v_toSeqLeft_3708_ = lean_ctor_get(v_toApplicative_3702_, 3);
v_toSeqRight_3709_ = lean_ctor_get(v_toApplicative_3702_, 4);
v_isSharedCheck_3762_ = !lean_is_exclusive(v_toApplicative_3702_);
if (v_isSharedCheck_3762_ == 0)
{
lean_object* v_unused_3763_; 
v_unused_3763_ = lean_ctor_get(v_toApplicative_3702_, 1);
lean_dec(v_unused_3763_);
v___x_3711_ = v_toApplicative_3702_;
v_isShared_3712_ = v_isSharedCheck_3762_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_toSeqRight_3709_);
lean_inc(v_toSeqLeft_3708_);
lean_inc(v_toSeq_3707_);
lean_inc(v_toFunctor_3706_);
lean_dec(v_toApplicative_3702_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3762_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___f_3713_; lean_object* v___f_3714_; lean_object* v___f_3715_; lean_object* v___f_3716_; lean_object* v___x_3717_; lean_object* v___f_3718_; lean_object* v___f_3719_; lean_object* v___f_3720_; lean_object* v___x_3722_; 
v___f_3713_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__1));
v___f_3714_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_3706_);
v___f_3715_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3715_, 0, v_toFunctor_3706_);
v___f_3716_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3716_, 0, v_toFunctor_3706_);
v___x_3717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3717_, 0, v___f_3715_);
lean_ctor_set(v___x_3717_, 1, v___f_3716_);
v___f_3718_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3718_, 0, v_toSeqRight_3709_);
v___f_3719_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3719_, 0, v_toSeqLeft_3708_);
v___f_3720_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3720_, 0, v_toSeq_3707_);
if (v_isShared_3712_ == 0)
{
lean_ctor_set(v___x_3711_, 4, v___f_3718_);
lean_ctor_set(v___x_3711_, 3, v___f_3719_);
lean_ctor_set(v___x_3711_, 2, v___f_3720_);
lean_ctor_set(v___x_3711_, 1, v___f_3713_);
lean_ctor_set(v___x_3711_, 0, v___x_3717_);
v___x_3722_ = v___x_3711_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v___x_3717_);
lean_ctor_set(v_reuseFailAlloc_3761_, 1, v___f_3713_);
lean_ctor_set(v_reuseFailAlloc_3761_, 2, v___f_3720_);
lean_ctor_set(v_reuseFailAlloc_3761_, 3, v___f_3719_);
lean_ctor_set(v_reuseFailAlloc_3761_, 4, v___f_3718_);
v___x_3722_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
lean_object* v___x_3724_; 
if (v_isShared_3705_ == 0)
{
lean_ctor_set(v___x_3704_, 1, v___f_3714_);
lean_ctor_set(v___x_3704_, 0, v___x_3722_);
v___x_3724_ = v___x_3704_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v___x_3722_);
lean_ctor_set(v_reuseFailAlloc_3760_, 1, v___f_3714_);
v___x_3724_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
lean_object* v___x_3725_; lean_object* v_toApplicative_3726_; lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3758_; 
v___x_3725_ = l_StateRefT_x27_instMonad___redArg(v___x_3724_);
v_toApplicative_3726_ = lean_ctor_get(v___x_3725_, 0);
v_isSharedCheck_3758_ = !lean_is_exclusive(v___x_3725_);
if (v_isSharedCheck_3758_ == 0)
{
lean_object* v_unused_3759_; 
v_unused_3759_ = lean_ctor_get(v___x_3725_, 1);
lean_dec(v_unused_3759_);
v___x_3728_ = v___x_3725_;
v_isShared_3729_ = v_isSharedCheck_3758_;
goto v_resetjp_3727_;
}
else
{
lean_inc(v_toApplicative_3726_);
lean_dec(v___x_3725_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3758_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
lean_object* v_toFunctor_3730_; lean_object* v_toSeq_3731_; lean_object* v_toSeqLeft_3732_; lean_object* v_toSeqRight_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3756_; 
v_toFunctor_3730_ = lean_ctor_get(v_toApplicative_3726_, 0);
v_toSeq_3731_ = lean_ctor_get(v_toApplicative_3726_, 2);
v_toSeqLeft_3732_ = lean_ctor_get(v_toApplicative_3726_, 3);
v_toSeqRight_3733_ = lean_ctor_get(v_toApplicative_3726_, 4);
v_isSharedCheck_3756_ = !lean_is_exclusive(v_toApplicative_3726_);
if (v_isSharedCheck_3756_ == 0)
{
lean_object* v_unused_3757_; 
v_unused_3757_ = lean_ctor_get(v_toApplicative_3726_, 1);
lean_dec(v_unused_3757_);
v___x_3735_ = v_toApplicative_3726_;
v_isShared_3736_ = v_isSharedCheck_3756_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_toSeqRight_3733_);
lean_inc(v_toSeqLeft_3732_);
lean_inc(v_toSeq_3731_);
lean_inc(v_toFunctor_3730_);
lean_dec(v_toApplicative_3726_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3756_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___f_3737_; lean_object* v___f_3738_; lean_object* v___f_3739_; lean_object* v___f_3740_; lean_object* v___x_3741_; lean_object* v___f_3742_; lean_object* v___f_3743_; lean_object* v___f_3744_; lean_object* v___x_3746_; 
v___f_3737_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__3));
v___f_3738_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_3730_);
v___f_3739_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3739_, 0, v_toFunctor_3730_);
v___f_3740_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3740_, 0, v_toFunctor_3730_);
v___x_3741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3741_, 0, v___f_3739_);
lean_ctor_set(v___x_3741_, 1, v___f_3740_);
v___f_3742_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3742_, 0, v_toSeqRight_3733_);
v___f_3743_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3743_, 0, v_toSeqLeft_3732_);
v___f_3744_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3744_, 0, v_toSeq_3731_);
if (v_isShared_3736_ == 0)
{
lean_ctor_set(v___x_3735_, 4, v___f_3742_);
lean_ctor_set(v___x_3735_, 3, v___f_3743_);
lean_ctor_set(v___x_3735_, 2, v___f_3744_);
lean_ctor_set(v___x_3735_, 1, v___f_3737_);
lean_ctor_set(v___x_3735_, 0, v___x_3741_);
v___x_3746_ = v___x_3735_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v___x_3741_);
lean_ctor_set(v_reuseFailAlloc_3755_, 1, v___f_3737_);
lean_ctor_set(v_reuseFailAlloc_3755_, 2, v___f_3744_);
lean_ctor_set(v_reuseFailAlloc_3755_, 3, v___f_3743_);
lean_ctor_set(v_reuseFailAlloc_3755_, 4, v___f_3742_);
v___x_3746_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
lean_object* v___x_3748_; 
if (v_isShared_3729_ == 0)
{
lean_ctor_set(v___x_3728_, 1, v___f_3738_);
lean_ctor_set(v___x_3728_, 0, v___x_3746_);
v___x_3748_ = v___x_3728_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v___x_3746_);
lean_ctor_set(v_reuseFailAlloc_3754_, 1, v___f_3738_);
v___x_3748_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_43217__overap_3752_; lean_object* v___x_3753_; 
v___x_3749_ = l_ReaderT_instMonad___redArg(v___x_3748_);
v___x_3750_ = lean_box(0);
v___x_3751_ = l_instInhabitedOfMonad___redArg(v___x_3749_, v___x_3750_);
v___x_43217__overap_3752_ = lean_panic_fn(v___x_3751_, v_msg_3693_);
lean_inc(v___y_3698_);
lean_inc_ref(v___y_3697_);
lean_inc(v___y_3696_);
lean_inc_ref(v___y_3695_);
lean_inc_ref(v___y_3694_);
v___x_3753_ = lean_apply_6(v___x_43217__overap_3752_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, lean_box(0));
return v___x_3753_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__10_spec__11___boxed(lean_object* v_msg_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_){
_start:
{
lean_object* v_res_3773_; 
v_res_3773_ = l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__10_spec__11(v_msg_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_);
lean_dec(v___y_3771_);
lean_dec_ref(v___y_3770_);
lean_dec(v___y_3769_);
lean_dec_ref(v___y_3768_);
lean_dec_ref(v___y_3767_);
return v_res_3773_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__10(lean_object* v_constName_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_){
_start:
{
lean_object* v___x_3789_; lean_object* v_env_3790_; uint8_t v___x_3791_; lean_object* v___x_3792_; 
v___x_3789_ = lean_st_ref_get(v___y_3779_);
v_env_3790_ = lean_ctor_get(v___x_3789_, 0);
lean_inc_ref(v_env_3790_);
lean_dec(v___x_3789_);
v___x_3791_ = 0;
lean_inc(v_constName_3774_);
v___x_3792_ = l_Lean_Environment_findAsync_x3f(v_env_3790_, v_constName_3774_, v___x_3791_);
if (lean_obj_tag(v___x_3792_) == 1)
{
lean_object* v_val_3793_; uint8_t v_kind_3794_; 
v_val_3793_ = lean_ctor_get(v___x_3792_, 0);
lean_inc(v_val_3793_);
lean_dec_ref(v___x_3792_);
v_kind_3794_ = lean_ctor_get_uint8(v_val_3793_, sizeof(void*)*3);
if (v_kind_3794_ == 7)
{
lean_object* v___x_3795_; 
v___x_3795_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_3793_);
if (lean_obj_tag(v___x_3795_) == 7)
{
lean_object* v_val_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3803_; 
lean_dec(v_constName_3774_);
v_val_3796_ = lean_ctor_get(v___x_3795_, 0);
v_isSharedCheck_3803_ = !lean_is_exclusive(v___x_3795_);
if (v_isSharedCheck_3803_ == 0)
{
v___x_3798_ = v___x_3795_;
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_val_3796_);
lean_dec(v___x_3795_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
lean_object* v___x_3801_; 
if (v_isShared_3799_ == 0)
{
lean_ctor_set_tag(v___x_3798_, 0);
v___x_3801_ = v___x_3798_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_val_3796_);
v___x_3801_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
return v___x_3801_;
}
}
}
else
{
lean_object* v___x_3804_; lean_object* v___x_3805_; 
lean_dec_ref(v___x_3795_);
v___x_3804_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__7, &l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__7_once, _init_l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__7);
v___x_3805_ = l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__10_spec__11(v___x_3804_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_);
if (lean_obj_tag(v___x_3805_) == 0)
{
lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3814_; 
v_a_3806_ = lean_ctor_get(v___x_3805_, 0);
v_isSharedCheck_3814_ = !lean_is_exclusive(v___x_3805_);
if (v_isSharedCheck_3814_ == 0)
{
v___x_3808_ = v___x_3805_;
v_isShared_3809_ = v_isSharedCheck_3814_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_dec(v___x_3805_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3814_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
if (lean_obj_tag(v_a_3806_) == 0)
{
lean_del_object(v___x_3808_);
goto v___jp_3781_;
}
else
{
lean_object* v_val_3810_; lean_object* v___x_3812_; 
lean_dec(v_constName_3774_);
v_val_3810_ = lean_ctor_get(v_a_3806_, 0);
lean_inc(v_val_3810_);
lean_dec_ref(v_a_3806_);
if (v_isShared_3809_ == 0)
{
lean_ctor_set(v___x_3808_, 0, v_val_3810_);
v___x_3812_ = v___x_3808_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_val_3810_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
return v___x_3812_;
}
}
}
}
else
{
lean_object* v_a_3815_; lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3822_; 
lean_dec(v_constName_3774_);
v_a_3815_ = lean_ctor_get(v___x_3805_, 0);
v_isSharedCheck_3822_ = !lean_is_exclusive(v___x_3805_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3817_ = v___x_3805_;
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
else
{
lean_inc(v_a_3815_);
lean_dec(v___x_3805_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
lean_object* v___x_3820_; 
if (v_isShared_3818_ == 0)
{
v___x_3820_ = v___x_3817_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_a_3815_);
v___x_3820_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
return v___x_3820_;
}
}
}
}
}
else
{
lean_dec(v_val_3793_);
goto v___jp_3781_;
}
}
else
{
lean_dec(v___x_3792_);
goto v___jp_3781_;
}
v___jp_3781_:
{
lean_object* v___x_3782_; uint8_t v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; 
v___x_3782_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__1, &l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__1_once, _init_l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__1);
v___x_3783_ = 0;
v___x_3784_ = l_Lean_MessageData_ofConstName(v_constName_3774_, v___x_3783_);
v___x_3785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3785_, 0, v___x_3782_);
lean_ctor_set(v___x_3785_, 1, v___x_3784_);
v___x_3786_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__3, &l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__3_once, _init_l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__3);
v___x_3787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3787_, 0, v___x_3785_);
lean_ctor_set(v___x_3787_, 1, v___x_3786_);
v___x_3788_ = l_Lean_throwError___at___00Lean_Meta_SizeOfSpecNested_throwUnexpected_spec__0___redArg(v___x_3787_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_);
return v___x_3788_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__10___boxed(lean_object* v_constName_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_){
_start:
{
lean_object* v_res_3830_; 
v_res_3830_ = l_Lean_getConstInfoRec___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__10(v_constName_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
lean_dec(v___y_3828_);
lean_dec_ref(v___y_3827_);
lean_dec(v___y_3826_);
lean_dec_ref(v___y_3825_);
lean_dec_ref(v___y_3824_);
return v_res_3830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__7___redArg___lam__0(lean_object* v_k_3831_, lean_object* v___y_3832_, lean_object* v_b_3833_, lean_object* v_c_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
lean_object* v___x_3840_; 
lean_inc(v___y_3838_);
lean_inc_ref(v___y_3837_);
lean_inc(v___y_3836_);
lean_inc_ref(v___y_3835_);
lean_inc_ref(v___y_3832_);
v___x_3840_ = lean_apply_8(v_k_3831_, v_b_3833_, v_c_3834_, v___y_3832_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, lean_box(0));
return v___x_3840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__7___redArg___lam__0___boxed(lean_object* v_k_3841_, lean_object* v___y_3842_, lean_object* v_b_3843_, lean_object* v_c_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_){
_start:
{
lean_object* v_res_3850_; 
v_res_3850_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__7___redArg___lam__0(v_k_3841_, v___y_3842_, v_b_3843_, v_c_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
lean_dec(v___y_3848_);
lean_dec_ref(v___y_3847_);
lean_dec(v___y_3846_);
lean_dec_ref(v___y_3845_);
lean_dec_ref(v___y_3842_);
return v_res_3850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__13___redArg(lean_object* v_type_3851_, lean_object* v_maxFVars_x3f_3852_, lean_object* v_k_3853_, uint8_t v_cleanupAnnotations_3854_, uint8_t v_whnfType_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_){
_start:
{
lean_object* v___f_3862_; lean_object* v___x_3863_; 
lean_inc_ref(v___y_3856_);
v___f_3862_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__7___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3862_, 0, v_k_3853_);
lean_closure_set(v___f_3862_, 1, v___y_3856_);
v___x_3863_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_3851_, v_maxFVars_x3f_3852_, v___f_3862_, v_cleanupAnnotations_3854_, v_whnfType_3855_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_);
if (lean_obj_tag(v___x_3863_) == 0)
{
return v___x_3863_;
}
else
{
lean_object* v_a_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3871_; 
v_a_3864_ = lean_ctor_get(v___x_3863_, 0);
v_isSharedCheck_3871_ = !lean_is_exclusive(v___x_3863_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3866_ = v___x_3863_;
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_a_3864_);
lean_dec(v___x_3863_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3869_; 
if (v_isShared_3867_ == 0)
{
v___x_3869_ = v___x_3866_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_a_3864_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
return v___x_3869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__13___redArg___boxed(lean_object* v_type_3872_, lean_object* v_maxFVars_x3f_3873_, lean_object* v_k_3874_, lean_object* v_cleanupAnnotations_3875_, lean_object* v_whnfType_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3883_; uint8_t v_whnfType_boxed_3884_; lean_object* v_res_3885_; 
v_cleanupAnnotations_boxed_3883_ = lean_unbox(v_cleanupAnnotations_3875_);
v_whnfType_boxed_3884_ = lean_unbox(v_whnfType_3876_);
v_res_3885_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__13___redArg(v_type_3872_, v_maxFVars_x3f_3873_, v_k_3874_, v_cleanupAnnotations_boxed_3883_, v_whnfType_boxed_3884_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
lean_dec(v___y_3881_);
lean_dec_ref(v___y_3880_);
lean_dec(v___y_3879_);
lean_dec_ref(v___y_3878_);
lean_dec_ref(v___y_3877_);
return v_res_3885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__11___lam__0(lean_object* v_sizeOfBaseArgs_3886_, lean_object* v_sizeOfLevels_3887_, lean_object* v___x_3888_, uint8_t v___x_3889_, lean_object* v_ys_3890_, lean_object* v_x_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_){
_start:
{
lean_object* v___x_3898_; 
v___x_3898_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_mkSizeOf(v_sizeOfBaseArgs_3886_, v_sizeOfLevels_3887_, v_ys_3890_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_);
if (lean_obj_tag(v___x_3898_) == 0)
{
lean_object* v_a_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; 
v_a_3899_ = lean_ctor_get(v___x_3898_, 0);
lean_inc(v_a_3899_);
lean_dec_ref(v___x_3898_);
v___x_3900_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop_spec__0___closed__0));
v___x_3901_ = lean_array_get_size(v_ys_3890_);
v___x_3902_ = lean_unsigned_to_nat(1u);
v___x_3903_ = lean_nat_sub(v___x_3901_, v___x_3902_);
v___x_3904_ = lean_array_get_borrowed(v___x_3888_, v_ys_3890_, v___x_3903_);
lean_dec(v___x_3903_);
v___x_3905_ = lean_mk_empty_array_with_capacity(v___x_3902_);
lean_inc(v___x_3904_);
v___x_3906_ = lean_array_push(v___x_3905_, v___x_3904_);
v___x_3907_ = l_Lean_Meta_mkAppM(v___x_3900_, v___x_3906_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_);
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_object* v_a_3908_; lean_object* v___x_3909_; 
v_a_3908_ = lean_ctor_get(v___x_3907_, 0);
lean_inc(v_a_3908_);
lean_dec_ref(v___x_3907_);
v___x_3909_ = l_Lean_Meta_mkEq(v_a_3899_, v_a_3908_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v_a_3910_; uint8_t v___x_3911_; uint8_t v___x_3912_; lean_object* v___x_3913_; 
v_a_3910_ = lean_ctor_get(v___x_3909_, 0);
lean_inc(v_a_3910_);
lean_dec_ref(v___x_3909_);
v___x_3911_ = 0;
v___x_3912_ = 1;
v___x_3913_ = l_Lean_Meta_mkLambdaFVars(v_ys_3890_, v_a_3910_, v___x_3911_, v___x_3889_, v___x_3911_, v___x_3889_, v___x_3912_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_);
return v___x_3913_;
}
else
{
return v___x_3909_;
}
}
else
{
lean_dec(v_a_3899_);
return v___x_3907_;
}
}
else
{
lean_dec_ref(v___x_3888_);
return v___x_3898_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__11___lam__0___boxed(lean_object* v_sizeOfBaseArgs_3914_, lean_object* v_sizeOfLevels_3915_, lean_object* v___x_3916_, lean_object* v___x_3917_, lean_object* v_ys_3918_, lean_object* v_x_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_){
_start:
{
uint8_t v___x_44368__boxed_3926_; lean_object* v_res_3927_; 
v___x_44368__boxed_3926_ = lean_unbox(v___x_3917_);
v_res_3927_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__11___lam__0(v_sizeOfBaseArgs_3914_, v_sizeOfLevels_3915_, v___x_3916_, v___x_44368__boxed_3926_, v_ys_3918_, v_x_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_);
lean_dec(v___y_3924_);
lean_dec_ref(v___y_3923_);
lean_dec(v___y_3922_);
lean_dec_ref(v___y_3921_);
lean_dec_ref(v___y_3920_);
lean_dec_ref(v_x_3919_);
lean_dec_ref(v_ys_3918_);
return v_res_3927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__7___redArg(lean_object* v_type_3928_, lean_object* v_k_3929_, uint8_t v_cleanupAnnotations_3930_, uint8_t v_whnfType_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_){
_start:
{
lean_object* v___f_3938_; lean_object* v___x_3939_; 
lean_inc_ref(v___y_3932_);
v___f_3938_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__7___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3938_, 0, v_k_3929_);
lean_closure_set(v___f_3938_, 1, v___y_3932_);
v___x_3939_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_3928_, v___f_3938_, v_cleanupAnnotations_3930_, v_whnfType_3931_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_);
if (lean_obj_tag(v___x_3939_) == 0)
{
return v___x_3939_;
}
else
{
lean_object* v_a_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3947_; 
v_a_3940_ = lean_ctor_get(v___x_3939_, 0);
v_isSharedCheck_3947_ = !lean_is_exclusive(v___x_3939_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3942_ = v___x_3939_;
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_a_3940_);
lean_dec(v___x_3939_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v___x_3945_; 
if (v_isShared_3943_ == 0)
{
v___x_3945_ = v___x_3942_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_a_3940_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
return v___x_3945_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__7___redArg___boxed(lean_object* v_type_3948_, lean_object* v_k_3949_, lean_object* v_cleanupAnnotations_3950_, lean_object* v_whnfType_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3958_; uint8_t v_whnfType_boxed_3959_; lean_object* v_res_3960_; 
v_cleanupAnnotations_boxed_3958_ = lean_unbox(v_cleanupAnnotations_3950_);
v_whnfType_boxed_3959_ = lean_unbox(v_whnfType_3951_);
v_res_3960_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__7___redArg(v_type_3948_, v_k_3949_, v_cleanupAnnotations_boxed_3958_, v_whnfType_boxed_3959_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
lean_dec(v___y_3954_);
lean_dec_ref(v___y_3953_);
lean_dec_ref(v___y_3952_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__11(lean_object* v_sizeOfBaseArgs_3961_, lean_object* v_sizeOfLevels_3962_, lean_object* v_as_3963_, size_t v_sz_3964_, size_t v_i_3965_, lean_object* v_b_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_){
_start:
{
uint8_t v___x_3973_; 
v___x_3973_ = lean_usize_dec_lt(v_i_3965_, v_sz_3964_);
if (v___x_3973_ == 0)
{
lean_object* v___x_3974_; 
lean_dec(v_sizeOfLevels_3962_);
lean_dec_ref(v_sizeOfBaseArgs_3961_);
v___x_3974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3974_, 0, v_b_3966_);
return v___x_3974_;
}
else
{
lean_object* v_a_3975_; lean_object* v___x_3976_; 
v_a_3975_ = lean_array_uget_borrowed(v_as_3963_, v_i_3965_);
lean_inc(v___y_3971_);
lean_inc_ref(v___y_3970_);
lean_inc(v___y_3969_);
lean_inc_ref(v___y_3968_);
lean_inc(v_a_3975_);
v___x_3976_ = lean_infer_type(v_a_3975_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_);
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v_a_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___f_3980_; uint8_t v___x_3981_; lean_object* v___x_3982_; 
v_a_3977_ = lean_ctor_get(v___x_3976_, 0);
lean_inc(v_a_3977_);
lean_dec_ref(v___x_3976_);
v___x_3978_ = l_Lean_instInhabitedExpr;
v___x_3979_ = lean_box(v___x_3973_);
lean_inc(v_sizeOfLevels_3962_);
lean_inc_ref(v_sizeOfBaseArgs_3961_);
v___f_3980_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__11___lam__0___boxed), 12, 4);
lean_closure_set(v___f_3980_, 0, v_sizeOfBaseArgs_3961_);
lean_closure_set(v___f_3980_, 1, v_sizeOfLevels_3962_);
lean_closure_set(v___f_3980_, 2, v___x_3978_);
lean_closure_set(v___f_3980_, 3, v___x_3979_);
v___x_3981_ = 0;
v___x_3982_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__7___redArg(v_a_3977_, v___f_3980_, v___x_3981_, v___x_3981_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_);
if (lean_obj_tag(v___x_3982_) == 0)
{
lean_object* v_a_3983_; lean_object* v___x_3984_; size_t v___x_3985_; size_t v___x_3986_; 
v_a_3983_ = lean_ctor_get(v___x_3982_, 0);
lean_inc(v_a_3983_);
lean_dec_ref(v___x_3982_);
v___x_3984_ = l_Lean_Expr_app___override(v_b_3966_, v_a_3983_);
v___x_3985_ = ((size_t)1ULL);
v___x_3986_ = lean_usize_add(v_i_3965_, v___x_3985_);
v_i_3965_ = v___x_3986_;
v_b_3966_ = v___x_3984_;
goto _start;
}
else
{
lean_dec_ref(v_b_3966_);
lean_dec(v_sizeOfLevels_3962_);
lean_dec_ref(v_sizeOfBaseArgs_3961_);
return v___x_3982_;
}
}
else
{
lean_dec_ref(v_b_3966_);
lean_dec(v_sizeOfLevels_3962_);
lean_dec_ref(v_sizeOfBaseArgs_3961_);
return v___x_3976_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__11___boxed(lean_object* v_sizeOfBaseArgs_3988_, lean_object* v_sizeOfLevels_3989_, lean_object* v_as_3990_, lean_object* v_sz_3991_, lean_object* v_i_3992_, lean_object* v_b_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_){
_start:
{
size_t v_sz_boxed_4000_; size_t v_i_boxed_4001_; lean_object* v_res_4002_; 
v_sz_boxed_4000_ = lean_unbox_usize(v_sz_3991_);
lean_dec(v_sz_3991_);
v_i_boxed_4001_ = lean_unbox_usize(v_i_3992_);
lean_dec(v_i_3992_);
v_res_4002_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__11(v_sizeOfBaseArgs_3988_, v_sizeOfLevels_3989_, v_as_3990_, v_sz_boxed_4000_, v_i_boxed_4001_, v_b_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_);
lean_dec(v___y_3998_);
lean_dec_ref(v___y_3997_);
lean_dec(v___y_3996_);
lean_dec_ref(v___y_3995_);
lean_dec_ref(v___y_3994_);
lean_dec_ref(v_as_3990_);
return v_res_4002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__6_spec__6___redArg___lam__0(lean_object* v_k_4003_, lean_object* v___y_4004_, lean_object* v_b_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_){
_start:
{
lean_object* v___x_4011_; 
lean_inc(v___y_4009_);
lean_inc_ref(v___y_4008_);
lean_inc(v___y_4007_);
lean_inc_ref(v___y_4006_);
lean_inc_ref(v___y_4004_);
v___x_4011_ = lean_apply_7(v_k_4003_, v_b_4005_, v___y_4004_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, lean_box(0));
return v___x_4011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__6_spec__6___redArg___lam__0___boxed(lean_object* v_k_4012_, lean_object* v___y_4013_, lean_object* v_b_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_){
_start:
{
lean_object* v_res_4020_; 
v_res_4020_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__6_spec__6___redArg___lam__0(v_k_4012_, v___y_4013_, v_b_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_);
lean_dec(v___y_4018_);
lean_dec_ref(v___y_4017_);
lean_dec(v___y_4016_);
lean_dec_ref(v___y_4015_);
lean_dec_ref(v___y_4013_);
return v_res_4020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__6_spec__6___redArg(lean_object* v_name_4021_, uint8_t v_bi_4022_, lean_object* v_type_4023_, lean_object* v_k_4024_, uint8_t v_kind_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_){
_start:
{
lean_object* v___f_4032_; lean_object* v___x_4033_; 
lean_inc_ref(v___y_4026_);
v___f_4032_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__6_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4032_, 0, v_k_4024_);
lean_closure_set(v___f_4032_, 1, v___y_4026_);
v___x_4033_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4021_, v_bi_4022_, v_type_4023_, v___f_4032_, v_kind_4025_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_);
if (lean_obj_tag(v___x_4033_) == 0)
{
return v___x_4033_;
}
else
{
lean_object* v_a_4034_; lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4041_; 
v_a_4034_ = lean_ctor_get(v___x_4033_, 0);
v_isSharedCheck_4041_ = !lean_is_exclusive(v___x_4033_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_4036_ = v___x_4033_;
v_isShared_4037_ = v_isSharedCheck_4041_;
goto v_resetjp_4035_;
}
else
{
lean_inc(v_a_4034_);
lean_dec(v___x_4033_);
v___x_4036_ = lean_box(0);
v_isShared_4037_ = v_isSharedCheck_4041_;
goto v_resetjp_4035_;
}
v_resetjp_4035_:
{
lean_object* v___x_4039_; 
if (v_isShared_4037_ == 0)
{
v___x_4039_ = v___x_4036_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v_a_4034_);
v___x_4039_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
return v___x_4039_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__6_spec__6___redArg___boxed(lean_object* v_name_4042_, lean_object* v_bi_4043_, lean_object* v_type_4044_, lean_object* v_k_4045_, lean_object* v_kind_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_){
_start:
{
uint8_t v_bi_boxed_4053_; uint8_t v_kind_boxed_4054_; lean_object* v_res_4055_; 
v_bi_boxed_4053_ = lean_unbox(v_bi_4043_);
v_kind_boxed_4054_ = lean_unbox(v_kind_4046_);
v_res_4055_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__6_spec__6___redArg(v_name_4042_, v_bi_boxed_4053_, v_type_4044_, v_k_4045_, v_kind_boxed_4054_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_);
lean_dec(v___y_4051_);
lean_dec_ref(v___y_4050_);
lean_dec(v___y_4049_);
lean_dec_ref(v___y_4048_);
lean_dec_ref(v___y_4047_);
return v_res_4055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__6___redArg(lean_object* v_name_4056_, lean_object* v_type_4057_, lean_object* v_k_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_){
_start:
{
uint8_t v___x_4065_; uint8_t v___x_4066_; lean_object* v___x_4067_; 
v___x_4065_ = 0;
v___x_4066_ = 0;
v___x_4067_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__6_spec__6___redArg(v_name_4056_, v___x_4065_, v_type_4057_, v_k_4058_, v___x_4066_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_);
return v___x_4067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__6___redArg___boxed(lean_object* v_name_4068_, lean_object* v_type_4069_, lean_object* v_k_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_){
_start:
{
lean_object* v_res_4077_; 
v_res_4077_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__6___redArg(v_name_4068_, v_type_4069_, v_k_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_);
lean_dec(v___y_4075_);
lean_dec_ref(v___y_4074_);
lean_dec(v___y_4073_);
lean_dec_ref(v___y_4072_);
lean_dec_ref(v___y_4071_);
return v_res_4077_;
}
}
static lean_object* _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__1(void){
_start:
{
lean_object* v___x_4087_; lean_object* v___x_4088_; 
v___x_4087_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__0));
v___x_4088_ = l_Lean_stringToMessageData(v___x_4087_);
return v___x_4088_;
}
}
static lean_object* _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__3(void){
_start:
{
lean_object* v___x_4090_; lean_object* v___x_4091_; 
v___x_4090_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__2));
v___x_4091_ = l_Lean_stringToMessageData(v___x_4090_);
return v___x_4091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___lam__1___boxed(lean_object** _args){
lean_object* v_lhs_4093_ = _args[0];
lean_object* v_dummy_4094_ = _args[1];
lean_object* v___x_4095_ = _args[2];
lean_object* v___x_4096_ = _args[3];
lean_object* v___x_4097_ = _args[4];
lean_object* v___x_4098_ = _args[5];
lean_object* v___x_4099_ = _args[6];
lean_object* v___x_4100_ = _args[7];
lean_object* v_val_4101_ = _args[8];
lean_object* v___x_4102_ = _args[9];
lean_object* v___x_4103_ = _args[10];
lean_object* v_a_4104_ = _args[11];
lean_object* v___x_4105_ = _args[12];
lean_object* v_us_4106_ = _args[13];
lean_object* v___x_4107_ = _args[14];
lean_object* v_indices_4108_ = _args[15];
lean_object* v_x_4109_ = _args[16];
lean_object* v___y_4110_ = _args[17];
lean_object* v___y_4111_ = _args[18];
lean_object* v___y_4112_ = _args[19];
lean_object* v___y_4113_ = _args[20];
lean_object* v___y_4114_ = _args[21];
lean_object* v___y_4115_ = _args[22];
_start:
{
uint8_t v___x_44671__boxed_4116_; uint8_t v___x_44672__boxed_4117_; lean_object* v_res_4118_; 
v___x_44671__boxed_4116_ = lean_unbox(v___x_4099_);
v___x_44672__boxed_4117_ = lean_unbox(v___x_4100_);
v_res_4118_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___lam__1(v_lhs_4093_, v_dummy_4094_, v___x_4095_, v___x_4096_, v___x_4097_, v___x_4098_, v___x_44671__boxed_4116_, v___x_44672__boxed_4117_, v_val_4101_, v___x_4102_, v___x_4103_, v_a_4104_, v___x_4105_, v_us_4106_, v___x_4107_, v_indices_4108_, v_x_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
lean_dec(v___y_4112_);
lean_dec_ref(v___y_4111_);
lean_dec_ref(v___y_4110_);
lean_dec_ref(v_x_4109_);
return v_res_4118_;
}
}
static lean_object* _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__4(void){
_start:
{
lean_object* v___x_4125_; lean_object* v___x_4126_; 
v___x_4125_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__3));
v___x_4126_ = l_Lean_stringToMessageData(v___x_4125_);
return v___x_4126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma(lean_object* v_lhs_4127_, lean_object* v_rhs_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_){
_start:
{
lean_object* v_fileName_4135_; lean_object* v_fileMap_4136_; lean_object* v_options_4137_; lean_object* v_currRecDepth_4138_; lean_object* v_maxRecDepth_4139_; lean_object* v_ref_4140_; lean_object* v_currNamespace_4141_; lean_object* v_openDecls_4142_; lean_object* v_initHeartbeats_4143_; lean_object* v_maxHeartbeats_4144_; lean_object* v_quotContext_4145_; lean_object* v_currMacroScope_4146_; uint8_t v_diag_4147_; lean_object* v_cancelTk_x3f_4148_; uint8_t v_suppressElabErrors_4149_; lean_object* v_inheritedTraceOptions_4150_; uint8_t v___x_4151_; 
v_fileName_4135_ = lean_ctor_get(v_a_4132_, 0);
lean_inc_ref(v_fileName_4135_);
v_fileMap_4136_ = lean_ctor_get(v_a_4132_, 1);
lean_inc_ref(v_fileMap_4136_);
v_options_4137_ = lean_ctor_get(v_a_4132_, 2);
lean_inc_ref(v_options_4137_);
v_currRecDepth_4138_ = lean_ctor_get(v_a_4132_, 3);
lean_inc(v_currRecDepth_4138_);
v_maxRecDepth_4139_ = lean_ctor_get(v_a_4132_, 4);
lean_inc(v_maxRecDepth_4139_);
v_ref_4140_ = lean_ctor_get(v_a_4132_, 5);
lean_inc(v_ref_4140_);
v_currNamespace_4141_ = lean_ctor_get(v_a_4132_, 6);
lean_inc(v_currNamespace_4141_);
v_openDecls_4142_ = lean_ctor_get(v_a_4132_, 7);
lean_inc(v_openDecls_4142_);
v_initHeartbeats_4143_ = lean_ctor_get(v_a_4132_, 8);
lean_inc(v_initHeartbeats_4143_);
v_maxHeartbeats_4144_ = lean_ctor_get(v_a_4132_, 9);
lean_inc(v_maxHeartbeats_4144_);
v_quotContext_4145_ = lean_ctor_get(v_a_4132_, 10);
lean_inc(v_quotContext_4145_);
v_currMacroScope_4146_ = lean_ctor_get(v_a_4132_, 11);
lean_inc(v_currMacroScope_4146_);
v_diag_4147_ = lean_ctor_get_uint8(v_a_4132_, sizeof(void*)*14);
v_cancelTk_x3f_4148_ = lean_ctor_get(v_a_4132_, 12);
lean_inc(v_cancelTk_x3f_4148_);
v_suppressElabErrors_4149_ = lean_ctor_get_uint8(v_a_4132_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4150_ = lean_ctor_get(v_a_4132_, 13);
lean_inc_ref(v_inheritedTraceOptions_4150_);
lean_dec_ref(v_a_4132_);
v___x_4151_ = lean_nat_dec_eq(v_currRecDepth_4138_, v_maxRecDepth_4139_);
if (v___x_4151_ == 0)
{
lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v___y_4159_; lean_object* v_cls_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; 
v___x_4152_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__0));
v___x_4153_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__1));
v_cls_4228_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___closed__2));
v___x_4229_ = lean_unsigned_to_nat(1u);
v___x_4230_ = lean_nat_add(v_currRecDepth_4138_, v___x_4229_);
lean_dec(v_currRecDepth_4138_);
v___x_4231_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4231_, 0, v_fileName_4135_);
lean_ctor_set(v___x_4231_, 1, v_fileMap_4136_);
lean_ctor_set(v___x_4231_, 2, v_options_4137_);
lean_ctor_set(v___x_4231_, 3, v___x_4230_);
lean_ctor_set(v___x_4231_, 4, v_maxRecDepth_4139_);
lean_ctor_set(v___x_4231_, 5, v_ref_4140_);
lean_ctor_set(v___x_4231_, 6, v_currNamespace_4141_);
lean_ctor_set(v___x_4231_, 7, v_openDecls_4142_);
lean_ctor_set(v___x_4231_, 8, v_initHeartbeats_4143_);
lean_ctor_set(v___x_4231_, 9, v_maxHeartbeats_4144_);
lean_ctor_set(v___x_4231_, 10, v_quotContext_4145_);
lean_ctor_set(v___x_4231_, 11, v_currMacroScope_4146_);
lean_ctor_set(v___x_4231_, 12, v_cancelTk_x3f_4148_);
lean_ctor_set(v___x_4231_, 13, v_inheritedTraceOptions_4150_);
lean_ctor_set_uint8(v___x_4231_, sizeof(void*)*14, v_diag_4147_);
lean_ctor_set_uint8(v___x_4231_, sizeof(void*)*14 + 1, v_suppressElabErrors_4149_);
v___x_4232_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof_spec__0___redArg(v_cls_4228_, v___x_4231_);
if (lean_obj_tag(v___x_4232_) == 0)
{
lean_object* v_a_4233_; uint8_t v___x_4234_; 
v_a_4233_ = lean_ctor_get(v___x_4232_, 0);
lean_inc(v_a_4233_);
lean_dec_ref(v___x_4232_);
v___x_4234_ = lean_unbox(v_a_4233_);
lean_dec(v_a_4233_);
if (v___x_4234_ == 0)
{
lean_dec_ref(v_rhs_4128_);
v___y_4155_ = v_a_4129_;
v___y_4156_ = v_a_4130_;
v___y_4157_ = v_a_4131_;
v___y_4158_ = v___x_4231_;
v___y_4159_ = v_a_4133_;
goto v___jp_4154_;
}
else
{
lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; 
lean_inc_ref(v_lhs_4127_);
v___x_4235_ = l_Lean_MessageData_ofExpr(v_lhs_4127_);
v___x_4236_ = lean_obj_once(&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__4, &l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__4_once, _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__4);
v___x_4237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4237_, 0, v___x_4235_);
lean_ctor_set(v___x_4237_, 1, v___x_4236_);
v___x_4238_ = l_Lean_MessageData_ofExpr(v_rhs_4128_);
v___x_4239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4239_, 0, v___x_4237_);
lean_ctor_set(v___x_4239_, 1, v___x_4238_);
v___x_4240_ = l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof_spec__1___redArg(v_cls_4228_, v___x_4239_, v_a_4130_, v_a_4131_, v___x_4231_, v_a_4133_);
if (lean_obj_tag(v___x_4240_) == 0)
{
lean_dec_ref(v___x_4240_);
v___y_4155_ = v_a_4129_;
v___y_4156_ = v_a_4130_;
v___y_4157_ = v_a_4131_;
v___y_4158_ = v___x_4231_;
v___y_4159_ = v_a_4133_;
goto v___jp_4154_;
}
else
{
lean_object* v_a_4241_; lean_object* v___x_4243_; uint8_t v_isShared_4244_; uint8_t v_isSharedCheck_4248_; 
lean_dec_ref(v___x_4231_);
lean_dec_ref(v_lhs_4127_);
v_a_4241_ = lean_ctor_get(v___x_4240_, 0);
v_isSharedCheck_4248_ = !lean_is_exclusive(v___x_4240_);
if (v_isSharedCheck_4248_ == 0)
{
v___x_4243_ = v___x_4240_;
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
else
{
lean_inc(v_a_4241_);
lean_dec(v___x_4240_);
v___x_4243_ = lean_box(0);
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
v_resetjp_4242_:
{
lean_object* v___x_4246_; 
if (v_isShared_4244_ == 0)
{
v___x_4246_ = v___x_4243_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v_a_4241_);
v___x_4246_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
return v___x_4246_;
}
}
}
}
}
else
{
lean_object* v_a_4249_; lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4256_; 
lean_dec_ref(v___x_4231_);
lean_dec_ref(v_rhs_4128_);
lean_dec_ref(v_lhs_4127_);
v_a_4249_ = lean_ctor_get(v___x_4232_, 0);
v_isSharedCheck_4256_ = !lean_is_exclusive(v___x_4232_);
if (v_isSharedCheck_4256_ == 0)
{
v___x_4251_ = v___x_4232_;
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
else
{
lean_inc(v_a_4249_);
lean_dec(v___x_4232_);
v___x_4251_ = lean_box(0);
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
v_resetjp_4250_:
{
lean_object* v___x_4254_; 
if (v_isShared_4252_ == 0)
{
v___x_4254_ = v___x_4251_;
goto v_reusejp_4253_;
}
else
{
lean_object* v_reuseFailAlloc_4255_; 
v_reuseFailAlloc_4255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4255_, 0, v_a_4249_);
v___x_4254_ = v_reuseFailAlloc_4255_;
goto v_reusejp_4253_;
}
v_reusejp_4253_:
{
return v___x_4254_;
}
}
}
v___jp_4154_:
{
lean_object* v___x_4160_; 
v___x_4160_ = l_Lean_Expr_getAppFn(v_lhs_4127_);
if (lean_obj_tag(v___x_4160_) == 4)
{
lean_object* v_declName_4161_; lean_object* v_us_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; 
v_declName_4161_ = lean_ctor_get(v___x_4160_, 0);
lean_inc(v_declName_4161_);
v_us_4162_ = lean_ctor_get(v___x_4160_, 1);
lean_inc(v_us_4162_);
v___x_4163_ = lean_box(0);
lean_inc(v_us_4162_);
v___x_4164_ = l_List_mapM_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__5(v_us_4162_, v___x_4163_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_);
if (lean_obj_tag(v___x_4164_) == 0)
{
lean_object* v_a_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4218_; 
v_a_4165_ = lean_ctor_get(v___x_4164_, 0);
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_4164_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4167_ = v___x_4164_;
v_isShared_4168_ = v_isSharedCheck_4218_;
goto v_resetjp_4166_;
}
else
{
lean_inc(v_a_4165_);
lean_dec(v___x_4164_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4218_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v___x_4169_; lean_object* v_env_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; uint8_t v___x_4173_; uint8_t v___x_4174_; 
v___x_4169_ = lean_st_ref_get(v___y_4159_);
v_env_4170_ = lean_ctor_get(v___x_4169_, 0);
lean_inc_ref(v_env_4170_);
lean_dec(v___x_4169_);
v___x_4171_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___closed__0));
v___x_4172_ = lean_name_append_after(v_declName_4161_, v___x_4171_);
v___x_4173_ = 1;
lean_inc(v___x_4172_);
v___x_4174_ = l_Lean_Environment_contains(v_env_4170_, v___x_4172_, v___x_4173_);
if (v___x_4174_ == 0)
{
lean_object* v___x_4175_; lean_object* v___x_4176_; 
lean_del_object(v___x_4167_);
v___x_4175_ = l_Lean_Expr_appArg_x21(v_lhs_4127_);
lean_inc(v___y_4159_);
lean_inc_ref(v___y_4158_);
lean_inc(v___y_4157_);
lean_inc_ref(v___y_4156_);
v___x_4176_ = lean_infer_type(v___x_4175_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_);
if (lean_obj_tag(v___x_4176_) == 0)
{
lean_object* v_a_4177_; lean_object* v___x_4178_; 
v_a_4177_ = lean_ctor_get(v___x_4176_, 0);
lean_inc(v_a_4177_);
lean_dec_ref(v___x_4176_);
lean_inc(v___y_4159_);
lean_inc_ref(v___y_4158_);
lean_inc(v___y_4157_);
lean_inc_ref(v___y_4156_);
v___x_4178_ = lean_whnf(v_a_4177_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_);
if (lean_obj_tag(v___x_4178_) == 0)
{
lean_object* v_a_4179_; lean_object* v___x_4180_; 
v_a_4179_ = lean_ctor_get(v___x_4178_, 0);
lean_inc(v_a_4179_);
lean_dec_ref(v___x_4178_);
v___x_4180_ = l_Lean_Expr_getAppFn(v_a_4179_);
if (lean_obj_tag(v___x_4180_) == 4)
{
lean_object* v_declName_4181_; lean_object* v___x_4182_; lean_object* v_env_4183_; lean_object* v___x_4184_; 
v_declName_4181_ = lean_ctor_get(v___x_4180_, 0);
lean_inc(v_declName_4181_);
v___x_4182_ = lean_st_ref_get(v___y_4159_);
v_env_4183_ = lean_ctor_get(v___x_4182_, 0);
lean_inc_ref(v_env_4183_);
lean_dec(v___x_4182_);
v___x_4184_ = l_Lean_Environment_find_x3f(v_env_4183_, v_declName_4181_, v___x_4151_);
if (lean_obj_tag(v___x_4184_) == 0)
{
lean_object* v___x_4185_; 
lean_dec_ref(v___x_4180_);
lean_dec(v_a_4179_);
lean_dec(v___x_4172_);
lean_dec(v_a_4165_);
lean_dec(v_us_4162_);
lean_dec_ref(v___x_4160_);
lean_dec_ref(v_lhs_4127_);
lean_inc_ref(v___y_4155_);
v___x_4185_ = l_Lean_Meta_SizeOfSpecNested_throwFailed___redArg(v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_);
lean_dec_ref(v___y_4158_);
return v___x_4185_;
}
else
{
lean_object* v_val_4186_; 
v_val_4186_ = lean_ctor_get(v___x_4184_, 0);
lean_inc(v_val_4186_);
lean_dec_ref(v___x_4184_);
if (lean_obj_tag(v_val_4186_) == 5)
{
lean_object* v_val_4187_; lean_object* v_numParams_4188_; lean_object* v_nargs_4189_; lean_object* v_dummy_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; 
v_val_4187_ = lean_ctor_get(v_val_4186_, 0);
lean_inc_ref(v_val_4187_);
lean_dec_ref(v_val_4186_);
v_numParams_4188_ = lean_ctor_get(v_val_4187_, 1);
v_nargs_4189_ = l_Lean_Expr_getAppNumArgs(v_a_4179_);
v_dummy_4190_ = lean_obj_once(&l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__3, &l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__3_once, _init_l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__3);
lean_inc(v_nargs_4189_);
v___x_4191_ = lean_mk_array(v_nargs_4189_, v_dummy_4190_);
v___x_4192_ = lean_unsigned_to_nat(1u);
v___x_4193_ = lean_nat_sub(v_nargs_4189_, v___x_4192_);
lean_dec(v_nargs_4189_);
v___x_4194_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_4179_, v___x_4191_, v___x_4193_);
v___x_4195_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_4188_);
v___x_4196_ = l_Array_toSubarray___redArg(v___x_4194_, v___x_4195_, v_numParams_4188_);
v___x_4197_ = l_Subarray_copy___redArg(v___x_4196_);
v___x_4198_ = l_Lean_mkAppN(v___x_4180_, v___x_4197_);
lean_dec_ref(v___x_4197_);
lean_inc(v___y_4159_);
lean_inc_ref(v___y_4158_);
lean_inc(v___y_4157_);
lean_inc_ref(v___y_4156_);
lean_inc_ref(v___x_4198_);
v___x_4199_ = lean_infer_type(v___x_4198_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_);
if (lean_obj_tag(v___x_4199_) == 0)
{
lean_object* v_a_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___f_4203_; lean_object* v___x_4204_; 
v_a_4200_ = lean_ctor_get(v___x_4199_, 0);
lean_inc(v_a_4200_);
lean_dec_ref(v___x_4199_);
v___x_4201_ = lean_box(v___x_4151_);
v___x_4202_ = lean_box(v___x_4173_);
v___f_4203_ = lean_alloc_closure((void*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___lam__1___boxed), 23, 15);
lean_closure_set(v___f_4203_, 0, v_lhs_4127_);
lean_closure_set(v___f_4203_, 1, v_dummy_4190_);
lean_closure_set(v___f_4203_, 2, v___x_4192_);
lean_closure_set(v___f_4203_, 3, v___x_4195_);
lean_closure_set(v___f_4203_, 4, v___x_4153_);
lean_closure_set(v___f_4203_, 5, v___x_4160_);
lean_closure_set(v___f_4203_, 6, v___x_4201_);
lean_closure_set(v___f_4203_, 7, v___x_4202_);
lean_closure_set(v___f_4203_, 8, v_val_4187_);
lean_closure_set(v___f_4203_, 9, v___x_4152_);
lean_closure_set(v___f_4203_, 10, v___x_4172_);
lean_closure_set(v___f_4203_, 11, v_a_4165_);
lean_closure_set(v___f_4203_, 12, v___x_4163_);
lean_closure_set(v___f_4203_, 13, v_us_4162_);
lean_closure_set(v___f_4203_, 14, v___x_4198_);
v___x_4204_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__7___redArg(v_a_4200_, v___f_4203_, v___x_4151_, v___x_4151_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_);
lean_dec_ref(v___y_4158_);
return v___x_4204_;
}
else
{
lean_dec_ref(v___x_4198_);
lean_dec_ref(v_val_4187_);
lean_dec(v___x_4172_);
lean_dec(v_a_4165_);
lean_dec(v_us_4162_);
lean_dec_ref(v___x_4160_);
lean_dec_ref(v___y_4158_);
lean_dec_ref(v_lhs_4127_);
return v___x_4199_;
}
}
else
{
lean_object* v___x_4205_; 
lean_dec(v_val_4186_);
lean_dec_ref(v___x_4180_);
lean_dec(v_a_4179_);
lean_dec(v___x_4172_);
lean_dec(v_a_4165_);
lean_dec(v_us_4162_);
lean_dec_ref(v___x_4160_);
lean_dec_ref(v_lhs_4127_);
lean_inc_ref(v___y_4155_);
v___x_4205_ = l_Lean_Meta_SizeOfSpecNested_throwFailed___redArg(v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_);
lean_dec_ref(v___y_4158_);
return v___x_4205_;
}
}
}
else
{
lean_object* v___x_4206_; 
lean_dec_ref(v___x_4180_);
lean_dec(v_a_4179_);
lean_dec(v___x_4172_);
lean_dec(v_a_4165_);
lean_dec(v_us_4162_);
lean_dec_ref(v___x_4160_);
lean_dec_ref(v_lhs_4127_);
lean_inc_ref(v___y_4155_);
v___x_4206_ = l_Lean_Meta_SizeOfSpecNested_throwFailed___redArg(v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_);
lean_dec_ref(v___y_4158_);
return v___x_4206_;
}
}
else
{
lean_dec(v___x_4172_);
lean_dec(v_a_4165_);
lean_dec(v_us_4162_);
lean_dec_ref(v___x_4160_);
lean_dec_ref(v___y_4158_);
lean_dec_ref(v_lhs_4127_);
return v___x_4178_;
}
}
else
{
lean_dec(v___x_4172_);
lean_dec(v_a_4165_);
lean_dec(v_us_4162_);
lean_dec_ref(v___x_4160_);
lean_dec_ref(v___y_4158_);
lean_dec_ref(v_lhs_4127_);
return v___x_4176_;
}
}
else
{
lean_object* v___x_4207_; lean_object* v_dummy_4208_; lean_object* v_nargs_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4216_; 
lean_dec(v_a_4165_);
lean_dec_ref(v___x_4160_);
lean_dec_ref(v___y_4158_);
v___x_4207_ = l_Lean_mkConst(v___x_4172_, v_us_4162_);
v_dummy_4208_ = lean_obj_once(&l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__3, &l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__3_once, _init_l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__3);
v_nargs_4209_ = l_Lean_Expr_getAppNumArgs(v_lhs_4127_);
lean_inc(v_nargs_4209_);
v___x_4210_ = lean_mk_array(v_nargs_4209_, v_dummy_4208_);
v___x_4211_ = lean_unsigned_to_nat(1u);
v___x_4212_ = lean_nat_sub(v_nargs_4209_, v___x_4211_);
lean_dec(v_nargs_4209_);
v___x_4213_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_lhs_4127_, v___x_4210_, v___x_4212_);
v___x_4214_ = l_Lean_mkAppN(v___x_4207_, v___x_4213_);
lean_dec_ref(v___x_4213_);
if (v_isShared_4168_ == 0)
{
lean_ctor_set(v___x_4167_, 0, v___x_4214_);
v___x_4216_ = v___x_4167_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v___x_4214_);
v___x_4216_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
return v___x_4216_;
}
}
}
}
else
{
lean_object* v_a_4219_; lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4226_; 
lean_dec(v_us_4162_);
lean_dec(v_declName_4161_);
lean_dec_ref(v___x_4160_);
lean_dec_ref(v___y_4158_);
lean_dec_ref(v_lhs_4127_);
v_a_4219_ = lean_ctor_get(v___x_4164_, 0);
v_isSharedCheck_4226_ = !lean_is_exclusive(v___x_4164_);
if (v_isSharedCheck_4226_ == 0)
{
v___x_4221_ = v___x_4164_;
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
else
{
lean_inc(v_a_4219_);
lean_dec(v___x_4164_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
lean_object* v___x_4224_; 
if (v_isShared_4222_ == 0)
{
v___x_4224_ = v___x_4221_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v_a_4219_);
v___x_4224_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
return v___x_4224_;
}
}
}
}
else
{
lean_object* v___x_4227_; 
lean_dec_ref(v___x_4160_);
lean_dec_ref(v_lhs_4127_);
lean_inc_ref(v___y_4155_);
v___x_4227_ = l_Lean_Meta_SizeOfSpecNested_throwFailed___redArg(v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_);
lean_dec_ref(v___y_4158_);
return v___x_4227_;
}
}
}
else
{
lean_object* v___x_4257_; 
lean_dec_ref(v_inheritedTraceOptions_4150_);
lean_dec(v_cancelTk_x3f_4148_);
lean_dec(v_currMacroScope_4146_);
lean_dec(v_quotContext_4145_);
lean_dec(v_maxHeartbeats_4144_);
lean_dec(v_initHeartbeats_4143_);
lean_dec(v_openDecls_4142_);
lean_dec(v_currNamespace_4141_);
lean_dec(v_maxRecDepth_4139_);
lean_dec(v_currRecDepth_4138_);
lean_dec_ref(v_options_4137_);
lean_dec_ref(v_fileMap_4136_);
lean_dec_ref(v_fileName_4135_);
lean_dec_ref(v_rhs_4128_);
lean_dec_ref(v_lhs_4127_);
v___x_4257_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg(v_ref_4140_);
return v___x_4257_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep(lean_object* v_ys_4265_, lean_object* v_lhs_4266_, lean_object* v_rhs_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_){
_start:
{
lean_object* v___x_4274_; 
lean_inc_ref(v_rhs_4267_);
lean_inc_ref(v_lhs_4266_);
v___x_4274_ = l_Lean_Meta_isExprDefEq(v_lhs_4266_, v_rhs_4267_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_);
if (lean_obj_tag(v___x_4274_) == 0)
{
lean_object* v_a_4275_; uint8_t v___x_4276_; 
v_a_4275_ = lean_ctor_get(v___x_4274_, 0);
lean_inc(v_a_4275_);
lean_dec_ref(v___x_4274_);
v___x_4276_ = lean_unbox(v_a_4275_);
lean_dec(v_a_4275_);
if (v___x_4276_ == 0)
{
lean_object* v___x_4277_; 
lean_inc_ref(v_a_4268_);
v___x_4277_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_recToSizeOf(v_lhs_4266_, v_a_4268_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_);
if (lean_obj_tag(v___x_4277_) == 0)
{
lean_object* v_a_4278_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___x_4310_; lean_object* v___x_4311_; 
v_a_4278_ = lean_ctor_get(v___x_4277_, 0);
lean_inc(v_a_4278_);
lean_dec_ref(v___x_4277_);
v___x_4310_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__2));
v___x_4311_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof_spec__0___redArg(v___x_4310_, v_a_4271_);
if (lean_obj_tag(v___x_4311_) == 0)
{
lean_object* v_a_4312_; uint8_t v___x_4313_; 
v_a_4312_ = lean_ctor_get(v___x_4311_, 0);
lean_inc(v_a_4312_);
lean_dec_ref(v___x_4311_);
v___x_4313_ = lean_unbox(v_a_4312_);
lean_dec(v_a_4312_);
if (v___x_4313_ == 0)
{
v___y_4280_ = v_a_4268_;
v___y_4281_ = v_a_4269_;
v___y_4282_ = v_a_4270_;
v___y_4283_ = v_a_4271_;
v___y_4284_ = v_a_4272_;
goto v___jp_4279_;
}
else
{
lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; 
lean_inc(v_a_4278_);
v___x_4314_ = l_Lean_MessageData_ofExpr(v_a_4278_);
v___x_4315_ = lean_obj_once(&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__4, &l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__4_once, _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__4);
v___x_4316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4316_, 0, v___x_4314_);
lean_ctor_set(v___x_4316_, 1, v___x_4315_);
lean_inc_ref(v_rhs_4267_);
v___x_4317_ = l_Lean_MessageData_ofExpr(v_rhs_4267_);
v___x_4318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4318_, 0, v___x_4316_);
lean_ctor_set(v___x_4318_, 1, v___x_4317_);
v___x_4319_ = l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof_spec__1___redArg(v___x_4310_, v___x_4318_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_);
if (lean_obj_tag(v___x_4319_) == 0)
{
lean_dec_ref(v___x_4319_);
v___y_4280_ = v_a_4268_;
v___y_4281_ = v_a_4269_;
v___y_4282_ = v_a_4270_;
v___y_4283_ = v_a_4271_;
v___y_4284_ = v_a_4272_;
goto v___jp_4279_;
}
else
{
lean_object* v_a_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4327_; 
lean_dec(v_a_4278_);
lean_dec_ref(v_rhs_4267_);
v_a_4320_ = lean_ctor_get(v___x_4319_, 0);
v_isSharedCheck_4327_ = !lean_is_exclusive(v___x_4319_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4322_ = v___x_4319_;
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_a_4320_);
lean_dec(v___x_4319_);
v___x_4322_ = lean_box(0);
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
v_resetjp_4321_:
{
lean_object* v___x_4325_; 
if (v_isShared_4323_ == 0)
{
v___x_4325_ = v___x_4322_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_a_4320_);
v___x_4325_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
return v___x_4325_;
}
}
}
}
}
else
{
lean_object* v_a_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4335_; 
lean_dec(v_a_4278_);
lean_dec_ref(v_rhs_4267_);
v_a_4328_ = lean_ctor_get(v___x_4311_, 0);
v_isSharedCheck_4335_ = !lean_is_exclusive(v___x_4311_);
if (v_isSharedCheck_4335_ == 0)
{
v___x_4330_ = v___x_4311_;
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_a_4328_);
lean_dec(v___x_4311_);
v___x_4330_ = lean_box(0);
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
v_resetjp_4329_:
{
lean_object* v___x_4333_; 
if (v_isShared_4331_ == 0)
{
v___x_4333_ = v___x_4330_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4334_; 
v_reuseFailAlloc_4334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4334_, 0, v_a_4328_);
v___x_4333_ = v_reuseFailAlloc_4334_;
goto v_reusejp_4332_;
}
v_reusejp_4332_:
{
return v___x_4333_;
}
}
}
v___jp_4279_:
{
lean_object* v___x_4285_; 
lean_inc_ref(v_rhs_4267_);
lean_inc(v_a_4278_);
v___x_4285_ = l_Lean_Meta_mkEq(v_a_4278_, v_rhs_4267_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
if (lean_obj_tag(v___x_4285_) == 0)
{
lean_object* v_a_4286_; lean_object* v___x_4287_; size_t v_sz_4288_; size_t v___x_4289_; lean_object* v___x_4290_; 
v_a_4286_ = lean_ctor_get(v___x_4285_, 0);
lean_inc(v_a_4286_);
lean_dec_ref(v___x_4285_);
v___x_4287_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_mkSizeOf_spec__0___redArg___closed__0));
v_sz_4288_ = lean_array_size(v_ys_4265_);
v___x_4289_ = ((size_t)0ULL);
v___x_4290_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep_spec__3___redArg(v_a_4286_, v_ys_4265_, v_sz_4288_, v___x_4289_, v___x_4287_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
if (lean_obj_tag(v___x_4290_) == 0)
{
lean_object* v_a_4291_; lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4301_; 
v_a_4291_ = lean_ctor_get(v___x_4290_, 0);
v_isSharedCheck_4301_ = !lean_is_exclusive(v___x_4290_);
if (v_isSharedCheck_4301_ == 0)
{
v___x_4293_ = v___x_4290_;
v_isShared_4294_ = v_isSharedCheck_4301_;
goto v_resetjp_4292_;
}
else
{
lean_inc(v_a_4291_);
lean_dec(v___x_4290_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4301_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
lean_object* v_fst_4295_; 
v_fst_4295_ = lean_ctor_get(v_a_4291_, 0);
lean_inc(v_fst_4295_);
lean_dec(v_a_4291_);
if (lean_obj_tag(v_fst_4295_) == 0)
{
lean_object* v___x_4296_; 
lean_del_object(v___x_4293_);
lean_inc_ref(v___y_4283_);
v___x_4296_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma(v_a_4278_, v_rhs_4267_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
return v___x_4296_;
}
else
{
lean_object* v_val_4297_; lean_object* v___x_4299_; 
lean_dec(v_a_4278_);
lean_dec_ref(v_rhs_4267_);
v_val_4297_ = lean_ctor_get(v_fst_4295_, 0);
lean_inc(v_val_4297_);
lean_dec_ref(v_fst_4295_);
if (v_isShared_4294_ == 0)
{
lean_ctor_set(v___x_4293_, 0, v_val_4297_);
v___x_4299_ = v___x_4293_;
goto v_reusejp_4298_;
}
else
{
lean_object* v_reuseFailAlloc_4300_; 
v_reuseFailAlloc_4300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4300_, 0, v_val_4297_);
v___x_4299_ = v_reuseFailAlloc_4300_;
goto v_reusejp_4298_;
}
v_reusejp_4298_:
{
return v___x_4299_;
}
}
}
}
else
{
lean_object* v_a_4302_; lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4309_; 
lean_dec(v_a_4278_);
lean_dec_ref(v_rhs_4267_);
v_a_4302_ = lean_ctor_get(v___x_4290_, 0);
v_isSharedCheck_4309_ = !lean_is_exclusive(v___x_4290_);
if (v_isSharedCheck_4309_ == 0)
{
v___x_4304_ = v___x_4290_;
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
else
{
lean_inc(v_a_4302_);
lean_dec(v___x_4290_);
v___x_4304_ = lean_box(0);
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
v_resetjp_4303_:
{
lean_object* v___x_4307_; 
if (v_isShared_4305_ == 0)
{
v___x_4307_ = v___x_4304_;
goto v_reusejp_4306_;
}
else
{
lean_object* v_reuseFailAlloc_4308_; 
v_reuseFailAlloc_4308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_a_4302_);
v___x_4307_ = v_reuseFailAlloc_4308_;
goto v_reusejp_4306_;
}
v_reusejp_4306_:
{
return v___x_4307_;
}
}
}
}
else
{
lean_dec(v_a_4278_);
lean_dec_ref(v_rhs_4267_);
return v___x_4285_;
}
}
}
else
{
lean_dec_ref(v_rhs_4267_);
return v___x_4277_;
}
}
else
{
lean_object* v___x_4336_; 
lean_dec_ref(v_lhs_4266_);
v___x_4336_ = l_Lean_Meta_mkEqRefl(v_rhs_4267_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_);
return v___x_4336_;
}
}
else
{
lean_object* v_a_4337_; lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4344_; 
lean_dec_ref(v_rhs_4267_);
lean_dec_ref(v_lhs_4266_);
v_a_4337_ = lean_ctor_get(v___x_4274_, 0);
v_isSharedCheck_4344_ = !lean_is_exclusive(v___x_4274_);
if (v_isSharedCheck_4344_ == 0)
{
v___x_4339_ = v___x_4274_;
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
else
{
lean_inc(v_a_4337_);
lean_dec(v___x_4274_);
v___x_4339_ = lean_box(0);
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
v_resetjp_4338_:
{
lean_object* v___x_4342_; 
if (v_isShared_4340_ == 0)
{
v___x_4342_ = v___x_4339_;
goto v_reusejp_4341_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_a_4337_);
v___x_4342_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4341_;
}
v_reusejp_4341_:
{
return v___x_4342_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__6(void){
_start:
{
lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; 
v___x_4349_ = lean_box(0);
v___x_4350_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__5));
v___x_4351_ = l_Lean_mkConst(v___x_4350_, v___x_4349_);
return v___x_4351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof(lean_object* v_ys_4356_, lean_object* v_lhs_4357_, lean_object* v_rhs_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_){
_start:
{
lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4369_; lean_object* v___y_4370_; lean_object* v___y_4380_; lean_object* v___y_4381_; lean_object* v___y_4382_; lean_object* v___y_4383_; lean_object* v___y_4384_; lean_object* v_cls_4417_; lean_object* v___x_4418_; 
v_cls_4417_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__7));
v___x_4418_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof_spec__0___redArg(v_cls_4417_, v_a_4362_);
if (lean_obj_tag(v___x_4418_) == 0)
{
lean_object* v_a_4419_; uint8_t v___x_4420_; 
v_a_4419_ = lean_ctor_get(v___x_4418_, 0);
lean_inc(v_a_4419_);
lean_dec_ref(v___x_4418_);
v___x_4420_ = lean_unbox(v_a_4419_);
lean_dec(v_a_4419_);
if (v___x_4420_ == 0)
{
v___y_4380_ = v_a_4359_;
v___y_4381_ = v_a_4360_;
v___y_4382_ = v_a_4361_;
v___y_4383_ = v_a_4362_;
v___y_4384_ = v_a_4363_;
goto v___jp_4379_;
}
else
{
lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; 
lean_inc_ref(v_lhs_4357_);
v___x_4421_ = l_Lean_MessageData_ofExpr(v_lhs_4357_);
v___x_4422_ = lean_obj_once(&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__4, &l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__4_once, _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__4);
v___x_4423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4423_, 0, v___x_4421_);
lean_ctor_set(v___x_4423_, 1, v___x_4422_);
lean_inc_ref(v_rhs_4358_);
v___x_4424_ = l_Lean_MessageData_ofExpr(v_rhs_4358_);
v___x_4425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4425_, 0, v___x_4423_);
lean_ctor_set(v___x_4425_, 1, v___x_4424_);
v___x_4426_ = l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof_spec__1___redArg(v_cls_4417_, v___x_4425_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_);
if (lean_obj_tag(v___x_4426_) == 0)
{
lean_dec_ref(v___x_4426_);
v___y_4380_ = v_a_4359_;
v___y_4381_ = v_a_4360_;
v___y_4382_ = v_a_4361_;
v___y_4383_ = v_a_4362_;
v___y_4384_ = v_a_4363_;
goto v___jp_4379_;
}
else
{
lean_object* v_a_4427_; lean_object* v___x_4429_; uint8_t v_isShared_4430_; uint8_t v_isSharedCheck_4434_; 
lean_dec_ref(v_rhs_4358_);
lean_dec_ref(v_lhs_4357_);
v_a_4427_ = lean_ctor_get(v___x_4426_, 0);
v_isSharedCheck_4434_ = !lean_is_exclusive(v___x_4426_);
if (v_isSharedCheck_4434_ == 0)
{
v___x_4429_ = v___x_4426_;
v_isShared_4430_ = v_isSharedCheck_4434_;
goto v_resetjp_4428_;
}
else
{
lean_inc(v_a_4427_);
lean_dec(v___x_4426_);
v___x_4429_ = lean_box(0);
v_isShared_4430_ = v_isSharedCheck_4434_;
goto v_resetjp_4428_;
}
v_resetjp_4428_:
{
lean_object* v___x_4432_; 
if (v_isShared_4430_ == 0)
{
v___x_4432_ = v___x_4429_;
goto v_reusejp_4431_;
}
else
{
lean_object* v_reuseFailAlloc_4433_; 
v_reuseFailAlloc_4433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4433_, 0, v_a_4427_);
v___x_4432_ = v_reuseFailAlloc_4433_;
goto v_reusejp_4431_;
}
v_reusejp_4431_:
{
return v___x_4432_;
}
}
}
}
}
else
{
lean_object* v_a_4435_; lean_object* v___x_4437_; uint8_t v_isShared_4438_; uint8_t v_isSharedCheck_4442_; 
lean_dec_ref(v_rhs_4358_);
lean_dec_ref(v_lhs_4357_);
v_a_4435_ = lean_ctor_get(v___x_4418_, 0);
v_isSharedCheck_4442_ = !lean_is_exclusive(v___x_4418_);
if (v_isSharedCheck_4442_ == 0)
{
v___x_4437_ = v___x_4418_;
v_isShared_4438_ = v_isSharedCheck_4442_;
goto v_resetjp_4436_;
}
else
{
lean_inc(v_a_4435_);
lean_dec(v___x_4418_);
v___x_4437_ = lean_box(0);
v_isShared_4438_ = v_isSharedCheck_4442_;
goto v_resetjp_4436_;
}
v_resetjp_4436_:
{
lean_object* v___x_4440_; 
if (v_isShared_4438_ == 0)
{
v___x_4440_ = v___x_4437_;
goto v_reusejp_4439_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v_a_4435_);
v___x_4440_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4439_;
}
v_reusejp_4439_:
{
return v___x_4440_;
}
}
}
v___jp_4365_:
{
lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; 
v___x_4371_ = lean_obj_once(&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__1, &l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__1_once, _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__1);
v___x_4372_ = l_Lean_indentExpr(v_lhs_4357_);
v___x_4373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4373_, 0, v___x_4371_);
lean_ctor_set(v___x_4373_, 1, v___x_4372_);
v___x_4374_ = lean_obj_once(&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__3, &l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__3_once, _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__3);
v___x_4375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4375_, 0, v___x_4373_);
lean_ctor_set(v___x_4375_, 1, v___x_4374_);
v___x_4376_ = l_Lean_indentExpr(v_rhs_4358_);
v___x_4377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4377_, 0, v___x_4375_);
lean_ctor_set(v___x_4377_, 1, v___x_4376_);
lean_inc_ref(v___y_4366_);
v___x_4378_ = l_Lean_Meta_SizeOfSpecNested_throwUnexpected___redArg(v___x_4377_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_);
return v___x_4378_;
}
v___jp_4379_:
{
lean_object* v___x_4385_; 
lean_inc_ref(v_rhs_4358_);
lean_inc_ref(v_lhs_4357_);
v___x_4385_ = l_Lean_Meta_isExprDefEq(v_lhs_4357_, v_rhs_4358_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
if (lean_obj_tag(v___x_4385_) == 0)
{
lean_object* v_a_4386_; uint8_t v___x_4387_; 
v_a_4386_ = lean_ctor_get(v___x_4385_, 0);
lean_inc(v_a_4386_);
lean_dec_ref(v___x_4385_);
v___x_4387_ = lean_unbox(v_a_4386_);
lean_dec(v_a_4386_);
if (v___x_4387_ == 0)
{
lean_object* v___x_4388_; 
lean_inc_ref(v_lhs_4357_);
v___x_4388_ = l_Lean_Meta_whnfI(v_lhs_4357_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
if (lean_obj_tag(v___x_4388_) == 0)
{
lean_object* v_a_4389_; lean_object* v___x_4390_; 
v_a_4389_ = lean_ctor_get(v___x_4388_, 0);
lean_inc(v_a_4389_);
lean_dec_ref(v___x_4388_);
lean_inc_ref(v_rhs_4358_);
v___x_4390_ = l_Lean_Meta_whnfI(v_rhs_4358_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
if (lean_obj_tag(v___x_4390_) == 0)
{
lean_object* v_a_4391_; lean_object* v___x_4392_; 
v_a_4391_ = lean_ctor_get(v___x_4390_, 0);
lean_inc(v_a_4391_);
lean_dec_ref(v___x_4390_);
v___x_4392_ = l_Lean_Expr_natAdd_x3f(v_a_4389_);
lean_dec(v_a_4389_);
if (lean_obj_tag(v___x_4392_) == 1)
{
lean_object* v_val_4393_; lean_object* v_fst_4394_; lean_object* v_snd_4395_; lean_object* v___x_4396_; 
v_val_4393_ = lean_ctor_get(v___x_4392_, 0);
lean_inc(v_val_4393_);
lean_dec_ref(v___x_4392_);
v_fst_4394_ = lean_ctor_get(v_val_4393_, 0);
lean_inc(v_fst_4394_);
v_snd_4395_ = lean_ctor_get(v_val_4393_, 1);
lean_inc(v_snd_4395_);
lean_dec(v_val_4393_);
v___x_4396_ = l_Lean_Expr_natAdd_x3f(v_a_4391_);
lean_dec(v_a_4391_);
if (lean_obj_tag(v___x_4396_) == 1)
{
lean_object* v_val_4397_; lean_object* v_fst_4398_; lean_object* v_snd_4399_; lean_object* v___x_4400_; 
lean_dec_ref(v_rhs_4358_);
lean_dec_ref(v_lhs_4357_);
v_val_4397_ = lean_ctor_get(v___x_4396_, 0);
lean_inc(v_val_4397_);
lean_dec_ref(v___x_4396_);
v_fst_4398_ = lean_ctor_get(v_val_4397_, 0);
lean_inc(v_fst_4398_);
v_snd_4399_ = lean_ctor_get(v_val_4397_, 1);
lean_inc(v_snd_4399_);
lean_dec(v_val_4397_);
v___x_4400_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof(v_ys_4356_, v_fst_4394_, v_fst_4398_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
if (lean_obj_tag(v___x_4400_) == 0)
{
lean_object* v_a_4401_; lean_object* v___x_4402_; 
v_a_4401_ = lean_ctor_get(v___x_4400_, 0);
lean_inc(v_a_4401_);
lean_dec_ref(v___x_4400_);
v___x_4402_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep(v_ys_4356_, v_snd_4395_, v_snd_4399_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
if (lean_obj_tag(v___x_4402_) == 0)
{
lean_object* v_a_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; 
v_a_4403_ = lean_ctor_get(v___x_4402_, 0);
lean_inc(v_a_4403_);
lean_dec_ref(v___x_4402_);
v___x_4404_ = lean_obj_once(&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__6, &l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__6_once, _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__6);
v___x_4405_ = l_Lean_Meta_mkCongrArg(v___x_4404_, v_a_4401_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
if (lean_obj_tag(v___x_4405_) == 0)
{
lean_object* v_a_4406_; lean_object* v___x_4407_; 
v_a_4406_ = lean_ctor_get(v___x_4405_, 0);
lean_inc(v_a_4406_);
lean_dec_ref(v___x_4405_);
v___x_4407_ = l_Lean_Meta_mkCongr(v_a_4406_, v_a_4403_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
return v___x_4407_;
}
else
{
lean_dec(v_a_4403_);
return v___x_4405_;
}
}
else
{
lean_dec(v_a_4401_);
return v___x_4402_;
}
}
else
{
lean_dec(v_snd_4399_);
lean_dec(v_snd_4395_);
return v___x_4400_;
}
}
else
{
lean_dec(v___x_4396_);
lean_dec(v_snd_4395_);
lean_dec(v_fst_4394_);
v___y_4366_ = v___y_4380_;
v___y_4367_ = v___y_4381_;
v___y_4368_ = v___y_4382_;
v___y_4369_ = v___y_4383_;
v___y_4370_ = v___y_4384_;
goto v___jp_4365_;
}
}
else
{
lean_dec(v___x_4392_);
lean_dec(v_a_4391_);
v___y_4366_ = v___y_4380_;
v___y_4367_ = v___y_4381_;
v___y_4368_ = v___y_4382_;
v___y_4369_ = v___y_4383_;
v___y_4370_ = v___y_4384_;
goto v___jp_4365_;
}
}
else
{
lean_dec(v_a_4389_);
lean_dec_ref(v_rhs_4358_);
lean_dec_ref(v_lhs_4357_);
return v___x_4390_;
}
}
else
{
lean_dec_ref(v_rhs_4358_);
lean_dec_ref(v_lhs_4357_);
return v___x_4388_;
}
}
else
{
lean_object* v___x_4408_; 
lean_dec_ref(v_lhs_4357_);
v___x_4408_ = l_Lean_Meta_mkEqRefl(v_rhs_4358_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
return v___x_4408_;
}
}
else
{
lean_object* v_a_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4416_; 
lean_dec_ref(v_rhs_4358_);
lean_dec_ref(v_lhs_4357_);
v_a_4409_ = lean_ctor_get(v___x_4385_, 0);
v_isSharedCheck_4416_ = !lean_is_exclusive(v___x_4385_);
if (v_isSharedCheck_4416_ == 0)
{
v___x_4411_ = v___x_4385_;
v_isShared_4412_ = v_isSharedCheck_4416_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_a_4409_);
lean_dec(v___x_4385_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4416_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
lean_object* v___x_4414_; 
if (v_isShared_4412_ == 0)
{
v___x_4414_ = v___x_4411_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v_a_4409_);
v___x_4414_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
return v___x_4414_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__12___lam__0(lean_object* v_ys_4443_, lean_object* v_target_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_){
_start:
{
lean_object* v___x_4451_; 
lean_inc(v___y_4449_);
lean_inc_ref(v___y_4448_);
lean_inc(v___y_4447_);
lean_inc_ref(v___y_4446_);
v___x_4451_ = lean_whnf(v_target_4444_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
if (lean_obj_tag(v___x_4451_) == 0)
{
lean_object* v_a_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; uint8_t v___x_4455_; 
v_a_4452_ = lean_ctor_get(v___x_4451_, 0);
lean_inc(v_a_4452_);
lean_dec_ref(v___x_4451_);
v___x_4453_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__12___lam__0___closed__1));
v___x_4454_ = lean_unsigned_to_nat(3u);
v___x_4455_ = l_Lean_Expr_isAppOfArity(v_a_4452_, v___x_4453_, v___x_4454_);
if (v___x_4455_ == 0)
{
lean_object* v___x_4456_; 
lean_dec(v_a_4452_);
lean_inc_ref(v___y_4445_);
v___x_4456_ = l_Lean_Meta_SizeOfSpecNested_throwFailed___redArg(v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
return v___x_4456_;
}
else
{
lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; 
v___x_4457_ = l_Lean_Expr_appFn_x21(v_a_4452_);
v___x_4458_ = l_Lean_Expr_appArg_x21(v___x_4457_);
lean_dec_ref(v___x_4457_);
v___x_4459_ = l_Lean_Expr_appArg_x21(v_a_4452_);
lean_dec(v_a_4452_);
lean_inc_ref(v___x_4459_);
lean_inc_ref(v___x_4458_);
v___x_4460_ = l_Lean_Meta_isExprDefEq(v___x_4458_, v___x_4459_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
if (lean_obj_tag(v___x_4460_) == 0)
{
lean_object* v_a_4461_; uint8_t v___x_4462_; 
v_a_4461_ = lean_ctor_get(v___x_4460_, 0);
lean_inc(v_a_4461_);
lean_dec_ref(v___x_4460_);
v___x_4462_ = lean_unbox(v_a_4461_);
if (v___x_4462_ == 0)
{
lean_object* v___x_4463_; 
v___x_4463_ = l_Lean_Meta_unfoldDefinition(v___x_4458_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
if (lean_obj_tag(v___x_4463_) == 0)
{
lean_object* v_a_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; 
v_a_4464_ = lean_ctor_get(v___x_4463_, 0);
lean_inc(v_a_4464_);
lean_dec_ref(v___x_4463_);
v___x_4465_ = l_Lean_Expr_appArg_x21(v___x_4459_);
lean_dec_ref(v___x_4459_);
v___x_4466_ = l_Lean_Meta_mkSizeOfSpecLemmaInstance(v___x_4465_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
if (lean_obj_tag(v___x_4466_) == 0)
{
lean_object* v_a_4467_; lean_object* v___x_4468_; 
v_a_4467_ = lean_ctor_get(v___x_4466_, 0);
lean_inc(v_a_4467_);
lean_dec_ref(v___x_4466_);
lean_inc(v___y_4449_);
lean_inc_ref(v___y_4448_);
lean_inc(v___y_4447_);
lean_inc_ref(v___y_4446_);
lean_inc(v_a_4467_);
v___x_4468_ = lean_infer_type(v_a_4467_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
if (lean_obj_tag(v___x_4468_) == 0)
{
lean_object* v_a_4469_; lean_object* v___x_4470_; 
v_a_4469_ = lean_ctor_get(v___x_4468_, 0);
lean_inc(v_a_4469_);
lean_dec_ref(v___x_4468_);
lean_inc(v___y_4449_);
lean_inc_ref(v___y_4448_);
lean_inc(v___y_4447_);
lean_inc_ref(v___y_4446_);
v___x_4470_ = lean_whnf(v_a_4469_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
if (lean_obj_tag(v___x_4470_) == 0)
{
lean_object* v_a_4471_; uint8_t v___x_4472_; 
v_a_4471_ = lean_ctor_get(v___x_4470_, 0);
lean_inc(v_a_4471_);
lean_dec_ref(v___x_4470_);
v___x_4472_ = l_Lean_Expr_isAppOfArity(v_a_4471_, v___x_4453_, v___x_4454_);
if (v___x_4472_ == 0)
{
lean_object* v___x_4473_; 
lean_dec(v_a_4471_);
lean_dec(v_a_4467_);
lean_dec(v_a_4464_);
lean_dec(v_a_4461_);
lean_inc_ref(v___y_4445_);
v___x_4473_ = l_Lean_Meta_SizeOfSpecNested_throwFailed___redArg(v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
return v___x_4473_;
}
else
{
lean_object* v___x_4474_; lean_object* v___x_4475_; 
v___x_4474_ = l_Lean_Expr_appArg_x21(v_a_4471_);
lean_dec(v_a_4471_);
v___x_4475_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof(v_ys_4443_, v_a_4464_, v___x_4474_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
if (lean_obj_tag(v___x_4475_) == 0)
{
lean_object* v_a_4476_; lean_object* v___x_4477_; 
v_a_4476_ = lean_ctor_get(v___x_4475_, 0);
lean_inc(v_a_4476_);
lean_dec_ref(v___x_4475_);
v___x_4477_ = l_Lean_Meta_mkEqSymm(v_a_4467_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
if (lean_obj_tag(v___x_4477_) == 0)
{
lean_object* v_a_4478_; lean_object* v___x_4479_; 
v_a_4478_ = lean_ctor_get(v___x_4477_, 0);
lean_inc(v_a_4478_);
lean_dec_ref(v___x_4477_);
v___x_4479_ = l_Lean_Meta_mkEqTrans(v_a_4476_, v_a_4478_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
if (lean_obj_tag(v___x_4479_) == 0)
{
lean_object* v_a_4480_; uint8_t v___x_4481_; uint8_t v___x_4482_; uint8_t v___x_4483_; lean_object* v___x_4484_; 
v_a_4480_ = lean_ctor_get(v___x_4479_, 0);
lean_inc(v_a_4480_);
lean_dec_ref(v___x_4479_);
v___x_4481_ = 1;
v___x_4482_ = lean_unbox(v_a_4461_);
v___x_4483_ = lean_unbox(v_a_4461_);
lean_dec(v_a_4461_);
v___x_4484_ = l_Lean_Meta_mkLambdaFVars(v_ys_4443_, v_a_4480_, v___x_4482_, v___x_4455_, v___x_4483_, v___x_4455_, v___x_4481_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
return v___x_4484_;
}
else
{
lean_dec(v_a_4461_);
return v___x_4479_;
}
}
else
{
lean_dec(v_a_4476_);
lean_dec(v_a_4461_);
return v___x_4477_;
}
}
else
{
lean_dec(v_a_4467_);
lean_dec(v_a_4461_);
return v___x_4475_;
}
}
}
else
{
lean_dec(v_a_4467_);
lean_dec(v_a_4464_);
lean_dec(v_a_4461_);
return v___x_4470_;
}
}
else
{
lean_dec(v_a_4467_);
lean_dec(v_a_4464_);
lean_dec(v_a_4461_);
return v___x_4468_;
}
}
else
{
lean_dec(v_a_4464_);
lean_dec(v_a_4461_);
return v___x_4466_;
}
}
else
{
lean_dec(v_a_4461_);
lean_dec_ref(v___x_4459_);
return v___x_4463_;
}
}
else
{
lean_object* v___x_4485_; 
lean_dec(v_a_4461_);
lean_dec_ref(v___x_4458_);
v___x_4485_ = l_Lean_Meta_mkEqRefl(v___x_4459_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
if (lean_obj_tag(v___x_4485_) == 0)
{
lean_object* v_a_4486_; uint8_t v___x_4487_; uint8_t v___x_4488_; lean_object* v___x_4489_; 
v_a_4486_ = lean_ctor_get(v___x_4485_, 0);
lean_inc(v_a_4486_);
lean_dec_ref(v___x_4485_);
v___x_4487_ = 0;
v___x_4488_ = 1;
v___x_4489_ = l_Lean_Meta_mkLambdaFVars(v_ys_4443_, v_a_4486_, v___x_4487_, v___x_4455_, v___x_4487_, v___x_4455_, v___x_4488_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
return v___x_4489_;
}
else
{
return v___x_4485_;
}
}
}
else
{
lean_object* v_a_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4497_; 
lean_dec_ref(v___x_4459_);
lean_dec_ref(v___x_4458_);
v_a_4490_ = lean_ctor_get(v___x_4460_, 0);
v_isSharedCheck_4497_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4497_ == 0)
{
v___x_4492_ = v___x_4460_;
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_a_4490_);
lean_dec(v___x_4460_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
lean_object* v___x_4495_; 
if (v_isShared_4493_ == 0)
{
v___x_4495_ = v___x_4492_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v_a_4490_);
v___x_4495_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
return v___x_4495_;
}
}
}
}
}
else
{
return v___x_4451_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__12___lam__0___boxed(lean_object* v_ys_4498_, lean_object* v_target_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_){
_start:
{
lean_object* v_res_4506_; 
v_res_4506_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__12___lam__0(v_ys_4498_, v_target_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_);
lean_dec(v___y_4504_);
lean_dec_ref(v___y_4503_);
lean_dec(v___y_4502_);
lean_dec_ref(v___y_4501_);
lean_dec_ref(v___y_4500_);
lean_dec_ref(v_ys_4498_);
return v_res_4506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__12(lean_object* v_as_4507_, size_t v_sz_4508_, size_t v_i_4509_, lean_object* v_b_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_){
_start:
{
uint8_t v___x_4517_; 
v___x_4517_ = lean_usize_dec_lt(v_i_4509_, v_sz_4508_);
if (v___x_4517_ == 0)
{
lean_object* v___x_4518_; 
v___x_4518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4518_, 0, v_b_4510_);
return v___x_4518_;
}
else
{
lean_object* v_a_4519_; lean_object* v___x_4520_; 
v_a_4519_ = lean_array_uget_borrowed(v_as_4507_, v_i_4509_);
lean_inc(v___y_4515_);
lean_inc_ref(v___y_4514_);
lean_inc(v___y_4513_);
lean_inc_ref(v___y_4512_);
lean_inc(v_a_4519_);
v___x_4520_ = lean_infer_type(v_a_4519_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
if (lean_obj_tag(v___x_4520_) == 0)
{
lean_object* v_a_4521_; lean_object* v___f_4522_; uint8_t v___x_4523_; lean_object* v___x_4524_; 
v_a_4521_ = lean_ctor_get(v___x_4520_, 0);
lean_inc(v_a_4521_);
lean_dec_ref(v___x_4520_);
v___f_4522_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__12___lam__0___boxed), 8, 0);
v___x_4523_ = 0;
v___x_4524_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__7___redArg(v_a_4521_, v___f_4522_, v___x_4523_, v___x_4523_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
if (lean_obj_tag(v___x_4524_) == 0)
{
lean_object* v_a_4525_; lean_object* v___x_4526_; size_t v___x_4527_; size_t v___x_4528_; 
v_a_4525_ = lean_ctor_get(v___x_4524_, 0);
lean_inc(v_a_4525_);
lean_dec_ref(v___x_4524_);
v___x_4526_ = l_Lean_Expr_app___override(v_b_4510_, v_a_4525_);
v___x_4527_ = ((size_t)1ULL);
v___x_4528_ = lean_usize_add(v_i_4509_, v___x_4527_);
v_i_4509_ = v___x_4528_;
v_b_4510_ = v___x_4526_;
goto _start;
}
else
{
lean_dec_ref(v_b_4510_);
return v___x_4524_;
}
}
else
{
lean_dec_ref(v_b_4510_);
return v___x_4520_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof___lam__0(size_t v___x_4530_, lean_object* v_a_4531_, lean_object* v___x_4532_, lean_object* v_minorFVars_4533_, lean_object* v_x_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_){
_start:
{
size_t v_sz_4541_; lean_object* v___x_4542_; 
v_sz_4541_ = lean_array_size(v_minorFVars_4533_);
v___x_4542_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__12(v_minorFVars_4533_, v_sz_4541_, v___x_4530_, v_a_4531_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_);
if (lean_obj_tag(v___x_4542_) == 0)
{
lean_object* v_a_4543_; lean_object* v___x_4545_; uint8_t v_isShared_4546_; uint8_t v_isSharedCheck_4552_; 
v_a_4543_ = lean_ctor_get(v___x_4542_, 0);
v_isSharedCheck_4552_ = !lean_is_exclusive(v___x_4542_);
if (v_isSharedCheck_4552_ == 0)
{
v___x_4545_ = v___x_4542_;
v_isShared_4546_ = v_isSharedCheck_4552_;
goto v_resetjp_4544_;
}
else
{
lean_inc(v_a_4543_);
lean_dec(v___x_4542_);
v___x_4545_ = lean_box(0);
v_isShared_4546_ = v_isSharedCheck_4552_;
goto v_resetjp_4544_;
}
v_resetjp_4544_:
{
lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4550_; 
v___x_4547_ = l_Subarray_copy___redArg(v___x_4532_);
v___x_4548_ = l_Lean_mkAppN(v_a_4543_, v___x_4547_);
lean_dec_ref(v___x_4547_);
if (v_isShared_4546_ == 0)
{
lean_ctor_set(v___x_4545_, 0, v___x_4548_);
v___x_4550_ = v___x_4545_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4551_; 
v_reuseFailAlloc_4551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4551_, 0, v___x_4548_);
v___x_4550_ = v_reuseFailAlloc_4551_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
return v___x_4550_;
}
}
}
else
{
lean_dec_ref(v___x_4532_);
return v___x_4542_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof___lam__0___boxed(lean_object* v___x_4553_, lean_object* v_a_4554_, lean_object* v___x_4555_, lean_object* v_minorFVars_4556_, lean_object* v_x_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_){
_start:
{
size_t v___x_44691__boxed_4564_; lean_object* v_res_4565_; 
v___x_44691__boxed_4564_ = lean_unbox_usize(v___x_4553_);
lean_dec(v___x_4553_);
v_res_4565_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof___lam__0(v___x_44691__boxed_4564_, v_a_4554_, v___x_4555_, v_minorFVars_4556_, v_x_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_);
lean_dec(v___y_4562_);
lean_dec_ref(v___y_4561_);
lean_dec(v___y_4560_);
lean_dec_ref(v___y_4559_);
lean_dec_ref(v___y_4558_);
lean_dec_ref(v_x_4557_);
lean_dec_ref(v_minorFVars_4556_);
return v_res_4565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof___lam__1(lean_object* v_sizeOfBaseArgs_4566_, lean_object* v_sizeOfLevels_4567_, lean_object* v___x_4568_, lean_object* v___x_4569_, lean_object* v_numMinors_4570_, lean_object* v_motiveFVars_4571_, lean_object* v_x_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_){
_start:
{
size_t v_sz_4579_; size_t v___x_4580_; lean_object* v___x_4581_; 
v_sz_4579_ = lean_array_size(v_motiveFVars_4571_);
v___x_4580_ = ((size_t)0ULL);
v___x_4581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__11(v_sizeOfBaseArgs_4566_, v_sizeOfLevels_4567_, v_motiveFVars_4571_, v_sz_4579_, v___x_4580_, v___x_4568_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_);
if (lean_obj_tag(v___x_4581_) == 0)
{
lean_object* v_a_4582_; lean_object* v___x_4583_; 
v_a_4582_ = lean_ctor_get(v___x_4581_, 0);
lean_inc(v_a_4582_);
lean_dec_ref(v___x_4581_);
lean_inc(v___y_4577_);
lean_inc_ref(v___y_4576_);
lean_inc(v___y_4575_);
lean_inc_ref(v___y_4574_);
lean_inc(v_a_4582_);
v___x_4583_ = lean_infer_type(v_a_4582_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_);
if (lean_obj_tag(v___x_4583_) == 0)
{
lean_object* v_a_4584_; lean_object* v___x_4586_; uint8_t v_isShared_4587_; uint8_t v_isSharedCheck_4595_; 
v_a_4584_ = lean_ctor_get(v___x_4583_, 0);
v_isSharedCheck_4595_ = !lean_is_exclusive(v___x_4583_);
if (v_isSharedCheck_4595_ == 0)
{
v___x_4586_ = v___x_4583_;
v_isShared_4587_ = v_isSharedCheck_4595_;
goto v_resetjp_4585_;
}
else
{
lean_inc(v_a_4584_);
lean_dec(v___x_4583_);
v___x_4586_ = lean_box(0);
v_isShared_4587_ = v_isSharedCheck_4595_;
goto v_resetjp_4585_;
}
v_resetjp_4585_:
{
lean_object* v___x_4588_; lean_object* v___f_4589_; lean_object* v___x_4591_; 
v___x_4588_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof___lam__1___boxed__const__1));
v___f_4589_ = lean_alloc_closure((void*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof___lam__0___boxed), 11, 3);
lean_closure_set(v___f_4589_, 0, v___x_4588_);
lean_closure_set(v___f_4589_, 1, v_a_4582_);
lean_closure_set(v___f_4589_, 2, v___x_4569_);
if (v_isShared_4587_ == 0)
{
lean_ctor_set_tag(v___x_4586_, 1);
lean_ctor_set(v___x_4586_, 0, v_numMinors_4570_);
v___x_4591_ = v___x_4586_;
goto v_reusejp_4590_;
}
else
{
lean_object* v_reuseFailAlloc_4594_; 
v_reuseFailAlloc_4594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4594_, 0, v_numMinors_4570_);
v___x_4591_ = v_reuseFailAlloc_4594_;
goto v_reusejp_4590_;
}
v_reusejp_4590_:
{
uint8_t v___x_4592_; lean_object* v___x_4593_; 
v___x_4592_ = 0;
v___x_4593_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__13___redArg(v_a_4584_, v___x_4591_, v___f_4589_, v___x_4592_, v___x_4592_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_);
return v___x_4593_;
}
}
}
else
{
lean_dec(v_a_4582_);
lean_dec(v_numMinors_4570_);
lean_dec_ref(v___x_4569_);
return v___x_4583_;
}
}
else
{
lean_dec(v_numMinors_4570_);
lean_dec_ref(v___x_4569_);
return v___x_4581_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof___lam__1___boxed(lean_object* v_sizeOfBaseArgs_4596_, lean_object* v_sizeOfLevels_4597_, lean_object* v___x_4598_, lean_object* v___x_4599_, lean_object* v_numMinors_4600_, lean_object* v_motiveFVars_4601_, lean_object* v_x_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_){
_start:
{
lean_object* v_res_4609_; 
v_res_4609_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof___lam__1(v_sizeOfBaseArgs_4596_, v_sizeOfLevels_4597_, v___x_4598_, v___x_4599_, v_numMinors_4600_, v_motiveFVars_4601_, v_x_4602_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_);
lean_dec(v___y_4607_);
lean_dec_ref(v___y_4606_);
lean_dec(v___y_4605_);
lean_dec_ref(v___y_4604_);
lean_dec_ref(v___y_4603_);
lean_dec_ref(v_x_4602_);
lean_dec_ref(v_motiveFVars_4601_);
return v_res_4609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof(lean_object* v_info_4610_, lean_object* v_lhs_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_){
_start:
{
lean_object* v_toConstantVal_4618_; lean_object* v_numParams_4619_; lean_object* v_numIndices_4620_; lean_object* v_nargs_4621_; lean_object* v___x_4622_; lean_object* v_dummy_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v_lhsArgs_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v_sizeOfBaseArgs_4632_; lean_object* v___y_4634_; uint8_t v___x_4683_; 
v_toConstantVal_4618_ = lean_ctor_get(v_info_4610_, 0);
lean_inc_ref(v_toConstantVal_4618_);
v_numParams_4619_ = lean_ctor_get(v_info_4610_, 1);
lean_inc(v_numParams_4619_);
v_numIndices_4620_ = lean_ctor_get(v_info_4610_, 2);
lean_inc(v_numIndices_4620_);
lean_dec_ref(v_info_4610_);
v_nargs_4621_ = l_Lean_Expr_getAppNumArgs(v_lhs_4611_);
v___x_4622_ = lean_box(0);
v_dummy_4623_ = lean_obj_once(&l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__3, &l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__3_once, _init_l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__3);
lean_inc(v_nargs_4621_);
v___x_4624_ = lean_mk_array(v_nargs_4621_, v_dummy_4623_);
v___x_4625_ = lean_unsigned_to_nat(1u);
v___x_4626_ = lean_nat_sub(v_nargs_4621_, v___x_4625_);
lean_dec(v_nargs_4621_);
lean_inc_ref(v_lhs_4611_);
v_lhsArgs_4627_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_lhs_4611_, v___x_4624_, v___x_4626_);
v___x_4628_ = lean_array_get_size(v_lhsArgs_4627_);
v___x_4629_ = lean_nat_sub(v___x_4628_, v_numIndices_4620_);
lean_dec(v_numIndices_4620_);
v___x_4630_ = lean_nat_sub(v___x_4629_, v___x_4625_);
lean_dec(v___x_4629_);
v___x_4631_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_4630_);
lean_inc_ref(v_lhsArgs_4627_);
v_sizeOfBaseArgs_4632_ = l_Array_toSubarray___redArg(v_lhsArgs_4627_, v___x_4631_, v___x_4630_);
v___x_4683_ = lean_nat_dec_le(v___x_4630_, v___x_4631_);
if (v___x_4683_ == 0)
{
lean_object* v___x_4684_; 
v___x_4684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4684_, 0, v___x_4630_);
lean_ctor_set(v___x_4684_, 1, v___x_4628_);
v___y_4634_ = v___x_4684_;
goto v___jp_4633_;
}
else
{
lean_object* v___x_4685_; 
lean_dec(v___x_4630_);
v___x_4685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4685_, 0, v___x_4631_);
lean_ctor_set(v___x_4685_, 1, v___x_4628_);
v___y_4634_ = v___x_4685_;
goto v___jp_4633_;
}
v___jp_4633_:
{
lean_object* v_major_4635_; lean_object* v___x_4636_; 
v_major_4635_ = l_Lean_Expr_appArg_x21(v_lhs_4611_);
lean_inc(v_a_4616_);
lean_inc_ref(v_a_4615_);
lean_inc(v_a_4614_);
lean_inc_ref(v_a_4613_);
v___x_4636_ = lean_infer_type(v_major_4635_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_);
if (lean_obj_tag(v___x_4636_) == 0)
{
lean_object* v_a_4637_; lean_object* v___x_4638_; 
v_a_4637_ = lean_ctor_get(v___x_4636_, 0);
lean_inc(v_a_4637_);
lean_dec_ref(v___x_4636_);
lean_inc(v_a_4616_);
lean_inc_ref(v_a_4615_);
lean_inc(v_a_4614_);
lean_inc_ref(v_a_4613_);
v___x_4638_ = lean_whnf(v_a_4637_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_);
if (lean_obj_tag(v___x_4638_) == 0)
{
lean_object* v_a_4639_; lean_object* v___x_4640_; 
v_a_4639_ = lean_ctor_get(v___x_4638_, 0);
lean_inc(v_a_4639_);
lean_dec_ref(v___x_4638_);
v___x_4640_ = l_Lean_Expr_getAppFn(v_a_4639_);
if (lean_obj_tag(v___x_4640_) == 4)
{
lean_object* v_us_4641_; lean_object* v_name_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; 
v_us_4641_ = lean_ctor_get(v___x_4640_, 1);
lean_inc(v_us_4641_);
lean_dec_ref(v___x_4640_);
v_name_4642_ = lean_ctor_get(v_toConstantVal_4618_, 0);
lean_inc(v_name_4642_);
lean_dec_ref(v_toConstantVal_4618_);
v___x_4643_ = l_Lean_mkRecName(v_name_4642_);
lean_inc(v___x_4643_);
v___x_4644_ = l_Lean_getConstInfoRec___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__10(v___x_4643_, v_a_4612_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_);
if (lean_obj_tag(v___x_4644_) == 0)
{
lean_object* v_a_4645_; lean_object* v_nargs_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; 
v_a_4645_ = lean_ctor_get(v___x_4644_, 0);
lean_inc(v_a_4645_);
lean_dec_ref(v___x_4644_);
v_nargs_4646_ = l_Lean_Expr_getAppNumArgs(v_a_4639_);
lean_inc(v_nargs_4646_);
v___x_4647_ = lean_mk_array(v_nargs_4646_, v_dummy_4623_);
v___x_4648_ = lean_nat_sub(v_nargs_4646_, v___x_4625_);
lean_dec(v_nargs_4646_);
v___x_4649_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_4639_, v___x_4647_, v___x_4648_);
v___x_4650_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4650_, 0, v___x_4622_);
lean_ctor_set(v___x_4650_, 1, v_us_4641_);
v___x_4651_ = l_Lean_mkConst(v___x_4643_, v___x_4650_);
v___x_4652_ = l_Array_toSubarray___redArg(v___x_4649_, v___x_4631_, v_numParams_4619_);
v___x_4653_ = l_Subarray_copy___redArg(v___x_4652_);
v___x_4654_ = l_Lean_mkAppN(v___x_4651_, v___x_4653_);
lean_dec_ref(v___x_4653_);
lean_inc(v_a_4616_);
lean_inc_ref(v_a_4615_);
lean_inc(v_a_4614_);
lean_inc_ref(v_a_4613_);
lean_inc_ref(v___x_4654_);
v___x_4655_ = lean_infer_type(v___x_4654_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_);
if (lean_obj_tag(v___x_4655_) == 0)
{
lean_object* v_a_4656_; lean_object* v___x_4658_; uint8_t v_isShared_4659_; uint8_t v_isSharedCheck_4673_; 
v_a_4656_ = lean_ctor_get(v___x_4655_, 0);
v_isSharedCheck_4673_ = !lean_is_exclusive(v___x_4655_);
if (v_isSharedCheck_4673_ == 0)
{
v___x_4658_ = v___x_4655_;
v_isShared_4659_ = v_isSharedCheck_4673_;
goto v_resetjp_4657_;
}
else
{
lean_inc(v_a_4656_);
lean_dec(v___x_4655_);
v___x_4658_ = lean_box(0);
v_isShared_4659_ = v_isSharedCheck_4673_;
goto v_resetjp_4657_;
}
v_resetjp_4657_:
{
lean_object* v_lower_4660_; lean_object* v_upper_4661_; lean_object* v_numMotives_4662_; lean_object* v_numMinors_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v_sizeOfLevels_4666_; lean_object* v___f_4667_; lean_object* v___x_4669_; 
v_lower_4660_ = lean_ctor_get(v___y_4634_, 0);
lean_inc(v_lower_4660_);
v_upper_4661_ = lean_ctor_get(v___y_4634_, 1);
lean_inc(v_upper_4661_);
lean_dec_ref(v___y_4634_);
v_numMotives_4662_ = lean_ctor_get(v_a_4645_, 4);
lean_inc(v_numMotives_4662_);
v_numMinors_4663_ = lean_ctor_get(v_a_4645_, 5);
lean_inc(v_numMinors_4663_);
lean_dec(v_a_4645_);
v___x_4664_ = l_Array_toSubarray___redArg(v_lhsArgs_4627_, v_lower_4660_, v_upper_4661_);
v___x_4665_ = l_Lean_Expr_getAppFn(v_lhs_4611_);
lean_dec_ref(v_lhs_4611_);
v_sizeOfLevels_4666_ = l_Lean_Expr_constLevels_x21(v___x_4665_);
lean_dec_ref(v___x_4665_);
v___f_4667_ = lean_alloc_closure((void*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof___lam__1___boxed), 13, 5);
lean_closure_set(v___f_4667_, 0, v_sizeOfBaseArgs_4632_);
lean_closure_set(v___f_4667_, 1, v_sizeOfLevels_4666_);
lean_closure_set(v___f_4667_, 2, v___x_4654_);
lean_closure_set(v___f_4667_, 3, v___x_4664_);
lean_closure_set(v___f_4667_, 4, v_numMinors_4663_);
if (v_isShared_4659_ == 0)
{
lean_ctor_set_tag(v___x_4658_, 1);
lean_ctor_set(v___x_4658_, 0, v_numMotives_4662_);
v___x_4669_ = v___x_4658_;
goto v_reusejp_4668_;
}
else
{
lean_object* v_reuseFailAlloc_4672_; 
v_reuseFailAlloc_4672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4672_, 0, v_numMotives_4662_);
v___x_4669_ = v_reuseFailAlloc_4672_;
goto v_reusejp_4668_;
}
v_reusejp_4668_:
{
uint8_t v___x_4670_; lean_object* v___x_4671_; 
v___x_4670_ = 0;
v___x_4671_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__13___redArg(v_a_4656_, v___x_4669_, v___f_4667_, v___x_4670_, v___x_4670_, v_a_4612_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_);
return v___x_4671_;
}
}
}
else
{
lean_dec_ref(v___x_4654_);
lean_dec(v_a_4645_);
lean_dec_ref(v___y_4634_);
lean_dec_ref(v_sizeOfBaseArgs_4632_);
lean_dec_ref(v_lhsArgs_4627_);
lean_dec_ref(v_lhs_4611_);
return v___x_4655_;
}
}
else
{
lean_object* v_a_4674_; lean_object* v___x_4676_; uint8_t v_isShared_4677_; uint8_t v_isSharedCheck_4681_; 
lean_dec(v___x_4643_);
lean_dec(v_us_4641_);
lean_dec(v_a_4639_);
lean_dec_ref(v___y_4634_);
lean_dec_ref(v_sizeOfBaseArgs_4632_);
lean_dec_ref(v_lhsArgs_4627_);
lean_dec(v_numParams_4619_);
lean_dec_ref(v_lhs_4611_);
v_a_4674_ = lean_ctor_get(v___x_4644_, 0);
v_isSharedCheck_4681_ = !lean_is_exclusive(v___x_4644_);
if (v_isSharedCheck_4681_ == 0)
{
v___x_4676_ = v___x_4644_;
v_isShared_4677_ = v_isSharedCheck_4681_;
goto v_resetjp_4675_;
}
else
{
lean_inc(v_a_4674_);
lean_dec(v___x_4644_);
v___x_4676_ = lean_box(0);
v_isShared_4677_ = v_isSharedCheck_4681_;
goto v_resetjp_4675_;
}
v_resetjp_4675_:
{
lean_object* v___x_4679_; 
if (v_isShared_4677_ == 0)
{
v___x_4679_ = v___x_4676_;
goto v_reusejp_4678_;
}
else
{
lean_object* v_reuseFailAlloc_4680_; 
v_reuseFailAlloc_4680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4680_, 0, v_a_4674_);
v___x_4679_ = v_reuseFailAlloc_4680_;
goto v_reusejp_4678_;
}
v_reusejp_4678_:
{
return v___x_4679_;
}
}
}
}
else
{
lean_object* v___x_4682_; 
lean_dec_ref(v___x_4640_);
lean_dec(v_a_4639_);
lean_dec_ref(v___y_4634_);
lean_dec_ref(v_sizeOfBaseArgs_4632_);
lean_dec_ref(v_lhsArgs_4627_);
lean_dec(v_numParams_4619_);
lean_dec_ref(v_toConstantVal_4618_);
lean_dec_ref(v_lhs_4611_);
lean_inc_ref(v_a_4612_);
v___x_4682_ = l_Lean_Meta_SizeOfSpecNested_throwFailed___redArg(v_a_4612_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_);
return v___x_4682_;
}
}
else
{
lean_dec_ref(v___y_4634_);
lean_dec_ref(v_sizeOfBaseArgs_4632_);
lean_dec_ref(v_lhsArgs_4627_);
lean_dec(v_numParams_4619_);
lean_dec_ref(v_toConstantVal_4618_);
lean_dec_ref(v_lhs_4611_);
return v___x_4638_;
}
}
else
{
lean_dec_ref(v___y_4634_);
lean_dec_ref(v_sizeOfBaseArgs_4632_);
lean_dec_ref(v_lhsArgs_4627_);
lean_dec(v_numParams_4619_);
lean_dec_ref(v_toConstantVal_4618_);
lean_dec_ref(v_lhs_4611_);
return v___x_4636_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4687_; lean_object* v___x_4688_; 
v___x_4687_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___lam__0___closed__0));
v___x_4688_ = l_Lean_stringToMessageData(v___x_4687_);
return v___x_4688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___lam__0(lean_object* v_lhs_4689_, lean_object* v_dummy_4690_, lean_object* v___x_4691_, lean_object* v_indices_4692_, lean_object* v___x_4693_, lean_object* v___x_4694_, lean_object* v___x_4695_, uint8_t v___x_4696_, uint8_t v___x_4697_, lean_object* v_val_4698_, lean_object* v___x_4699_, lean_object* v___x_4700_, lean_object* v_a_4701_, lean_object* v___x_4702_, lean_object* v_us_4703_, lean_object* v_major_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_){
_start:
{
lean_object* v_nargs_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; 
v_nargs_4711_ = l_Lean_Expr_getAppNumArgs(v_lhs_4689_);
lean_inc(v_nargs_4711_);
v___x_4712_ = lean_mk_array(v_nargs_4711_, v_dummy_4690_);
v___x_4713_ = lean_nat_sub(v_nargs_4711_, v___x_4691_);
lean_dec(v_nargs_4711_);
v___x_4714_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_lhs_4689_, v___x_4712_, v___x_4713_);
v___x_4715_ = lean_array_get_size(v___x_4714_);
v___x_4716_ = lean_nat_sub(v___x_4715_, v___x_4691_);
v___x_4717_ = lean_array_get_size(v_indices_4692_);
v___x_4718_ = lean_nat_sub(v___x_4716_, v___x_4717_);
lean_dec(v___x_4716_);
lean_inc_ref(v___x_4714_);
v___x_4719_ = l_Array_toSubarray___redArg(v___x_4714_, v___x_4693_, v___x_4718_);
v___x_4720_ = l_Subarray_copy___redArg(v___x_4719_);
v___x_4721_ = l_Array_append___redArg(v___x_4720_, v_indices_4692_);
v___x_4722_ = lean_mk_empty_array_with_capacity(v___x_4691_);
v___x_4723_ = lean_array_push(v___x_4722_, v_major_4704_);
v___x_4724_ = l_Array_append___redArg(v___x_4721_, v___x_4723_);
v___x_4725_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___lam__0___closed__0));
lean_inc_ref(v___x_4694_);
v___x_4726_ = l_Lean_Name_mkStr2(v___x_4725_, v___x_4694_);
v___x_4727_ = l_Lean_Meta_mkAppM(v___x_4726_, v___x_4723_, v___y_4706_, v___y_4707_, v___y_4708_, v___y_4709_);
if (lean_obj_tag(v___x_4727_) == 0)
{
lean_object* v_a_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; 
v_a_4728_ = lean_ctor_get(v___x_4727_, 0);
lean_inc(v_a_4728_);
lean_dec_ref(v___x_4727_);
v___x_4729_ = l_Lean_mkAppN(v___x_4695_, v___x_4724_);
lean_inc_ref(v___x_4729_);
v___x_4730_ = l_Lean_Meta_mkEq(v___x_4729_, v_a_4728_, v___y_4706_, v___y_4707_, v___y_4708_, v___y_4709_);
if (lean_obj_tag(v___x_4730_) == 0)
{
lean_object* v_a_4731_; uint8_t v___x_4732_; lean_object* v___x_4733_; 
v_a_4731_ = lean_ctor_get(v___x_4730_, 0);
lean_inc(v_a_4731_);
lean_dec_ref(v___x_4730_);
v___x_4732_ = 1;
v___x_4733_ = l_Lean_Meta_mkForallFVars(v___x_4724_, v_a_4731_, v___x_4696_, v___x_4697_, v___x_4697_, v___x_4732_, v___y_4706_, v___y_4707_, v___y_4708_, v___y_4709_);
if (lean_obj_tag(v___x_4733_) == 0)
{
lean_object* v_a_4734_; lean_object* v___x_4735_; 
v_a_4734_ = lean_ctor_get(v___x_4733_, 0);
lean_inc(v_a_4734_);
lean_dec_ref(v___x_4733_);
v___x_4735_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof(v_val_4698_, v___x_4729_, v___y_4705_, v___y_4706_, v___y_4707_, v___y_4708_, v___y_4709_);
if (lean_obj_tag(v___x_4735_) == 0)
{
lean_object* v_a_4736_; lean_object* v___x_4737_; 
v_a_4736_ = lean_ctor_get(v___x_4735_, 0);
lean_inc(v_a_4736_);
lean_dec_ref(v___x_4735_);
v___x_4737_ = l_Lean_Meta_mkLambdaFVars(v___x_4724_, v_a_4736_, v___x_4696_, v___x_4697_, v___x_4696_, v___x_4697_, v___x_4732_, v___y_4706_, v___y_4707_, v___y_4708_, v___y_4709_);
lean_dec_ref(v___x_4724_);
if (lean_obj_tag(v___x_4737_) == 0)
{
lean_object* v_a_4738_; lean_object* v___x_4740_; uint8_t v_isShared_4741_; uint8_t v_isSharedCheck_4794_; 
v_a_4738_ = lean_ctor_get(v___x_4737_, 0);
v_isSharedCheck_4794_ = !lean_is_exclusive(v___x_4737_);
if (v_isSharedCheck_4794_ == 0)
{
v___x_4740_ = v___x_4737_;
v_isShared_4741_ = v_isSharedCheck_4794_;
goto v_resetjp_4739_;
}
else
{
lean_inc(v_a_4738_);
lean_dec(v___x_4737_);
v___x_4740_ = lean_box(0);
v_isShared_4741_ = v_isSharedCheck_4794_;
goto v_resetjp_4739_;
}
v_resetjp_4739_:
{
lean_object* v___y_4743_; lean_object* v___y_4744_; lean_object* v___x_4770_; lean_object* v___x_4771_; 
v___x_4770_ = l_Lean_Name_mkStr2(v___x_4699_, v___x_4694_);
lean_inc(v___x_4770_);
v___x_4771_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof_spec__0___redArg(v___x_4770_, v___y_4708_);
if (lean_obj_tag(v___x_4771_) == 0)
{
lean_object* v_a_4772_; uint8_t v___x_4773_; 
v_a_4772_ = lean_ctor_get(v___x_4771_, 0);
lean_inc(v_a_4772_);
lean_dec_ref(v___x_4771_);
v___x_4773_ = lean_unbox(v_a_4772_);
lean_dec(v_a_4772_);
if (v___x_4773_ == 0)
{
lean_dec(v___x_4770_);
v___y_4743_ = v___y_4708_;
v___y_4744_ = v___y_4709_;
goto v___jp_4742_;
}
else
{
lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; 
v___x_4774_ = lean_obj_once(&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___lam__0___closed__1, &l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___lam__0___closed__1_once, _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___lam__0___closed__1);
lean_inc(v_a_4738_);
v___x_4775_ = l_Lean_MessageData_ofExpr(v_a_4738_);
v___x_4776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4776_, 0, v___x_4774_);
lean_ctor_set(v___x_4776_, 1, v___x_4775_);
v___x_4777_ = l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof_spec__1___redArg(v___x_4770_, v___x_4776_, v___y_4706_, v___y_4707_, v___y_4708_, v___y_4709_);
if (lean_obj_tag(v___x_4777_) == 0)
{
lean_dec_ref(v___x_4777_);
v___y_4743_ = v___y_4708_;
v___y_4744_ = v___y_4709_;
goto v___jp_4742_;
}
else
{
lean_object* v_a_4778_; lean_object* v___x_4780_; uint8_t v_isShared_4781_; uint8_t v_isSharedCheck_4785_; 
lean_del_object(v___x_4740_);
lean_dec(v_a_4738_);
lean_dec(v_a_4734_);
lean_dec_ref(v___x_4714_);
lean_dec(v_us_4703_);
lean_dec(v___x_4702_);
lean_dec(v_a_4701_);
lean_dec(v___x_4700_);
v_a_4778_ = lean_ctor_get(v___x_4777_, 0);
v_isSharedCheck_4785_ = !lean_is_exclusive(v___x_4777_);
if (v_isSharedCheck_4785_ == 0)
{
v___x_4780_ = v___x_4777_;
v_isShared_4781_ = v_isSharedCheck_4785_;
goto v_resetjp_4779_;
}
else
{
lean_inc(v_a_4778_);
lean_dec(v___x_4777_);
v___x_4780_ = lean_box(0);
v_isShared_4781_ = v_isSharedCheck_4785_;
goto v_resetjp_4779_;
}
v_resetjp_4779_:
{
lean_object* v___x_4783_; 
if (v_isShared_4781_ == 0)
{
v___x_4783_ = v___x_4780_;
goto v_reusejp_4782_;
}
else
{
lean_object* v_reuseFailAlloc_4784_; 
v_reuseFailAlloc_4784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4784_, 0, v_a_4778_);
v___x_4783_ = v_reuseFailAlloc_4784_;
goto v_reusejp_4782_;
}
v_reusejp_4782_:
{
return v___x_4783_;
}
}
}
}
}
else
{
lean_object* v_a_4786_; lean_object* v___x_4788_; uint8_t v_isShared_4789_; uint8_t v_isSharedCheck_4793_; 
lean_dec(v___x_4770_);
lean_del_object(v___x_4740_);
lean_dec(v_a_4738_);
lean_dec(v_a_4734_);
lean_dec_ref(v___x_4714_);
lean_dec(v_us_4703_);
lean_dec(v___x_4702_);
lean_dec(v_a_4701_);
lean_dec(v___x_4700_);
v_a_4786_ = lean_ctor_get(v___x_4771_, 0);
v_isSharedCheck_4793_ = !lean_is_exclusive(v___x_4771_);
if (v_isSharedCheck_4793_ == 0)
{
v___x_4788_ = v___x_4771_;
v_isShared_4789_ = v_isSharedCheck_4793_;
goto v_resetjp_4787_;
}
else
{
lean_inc(v_a_4786_);
lean_dec(v___x_4771_);
v___x_4788_ = lean_box(0);
v_isShared_4789_ = v_isSharedCheck_4793_;
goto v_resetjp_4787_;
}
v_resetjp_4787_:
{
lean_object* v___x_4791_; 
if (v_isShared_4789_ == 0)
{
v___x_4791_ = v___x_4788_;
goto v_reusejp_4790_;
}
else
{
lean_object* v_reuseFailAlloc_4792_; 
v_reuseFailAlloc_4792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4792_, 0, v_a_4786_);
v___x_4791_ = v_reuseFailAlloc_4792_;
goto v_reusejp_4790_;
}
v_reusejp_4790_:
{
return v___x_4791_;
}
}
}
v___jp_4742_:
{
lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4749_; 
lean_inc(v___x_4700_);
v___x_4745_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4745_, 0, v___x_4700_);
lean_ctor_set(v___x_4745_, 1, v_a_4701_);
lean_ctor_set(v___x_4745_, 2, v_a_4734_);
lean_inc(v___x_4700_);
v___x_4746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4746_, 0, v___x_4700_);
lean_ctor_set(v___x_4746_, 1, v___x_4702_);
v___x_4747_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4747_, 0, v___x_4745_);
lean_ctor_set(v___x_4747_, 1, v_a_4738_);
lean_ctor_set(v___x_4747_, 2, v___x_4746_);
if (v_isShared_4741_ == 0)
{
lean_ctor_set_tag(v___x_4740_, 2);
lean_ctor_set(v___x_4740_, 0, v___x_4747_);
v___x_4749_ = v___x_4740_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4769_; 
v_reuseFailAlloc_4769_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4769_, 0, v___x_4747_);
v___x_4749_ = v_reuseFailAlloc_4769_;
goto v_reusejp_4748_;
}
v_reusejp_4748_:
{
lean_object* v___x_4750_; 
v___x_4750_ = l_Lean_addDecl(v___x_4749_, v___x_4696_, v___y_4743_, v___y_4744_);
if (lean_obj_tag(v___x_4750_) == 0)
{
lean_object* v___x_4752_; uint8_t v_isShared_4753_; uint8_t v_isSharedCheck_4759_; 
v_isSharedCheck_4759_ = !lean_is_exclusive(v___x_4750_);
if (v_isSharedCheck_4759_ == 0)
{
lean_object* v_unused_4760_; 
v_unused_4760_ = lean_ctor_get(v___x_4750_, 0);
lean_dec(v_unused_4760_);
v___x_4752_ = v___x_4750_;
v_isShared_4753_ = v_isSharedCheck_4759_;
goto v_resetjp_4751_;
}
else
{
lean_dec(v___x_4750_);
v___x_4752_ = lean_box(0);
v_isShared_4753_ = v_isSharedCheck_4759_;
goto v_resetjp_4751_;
}
v_resetjp_4751_:
{
lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4757_; 
v___x_4754_ = l_Lean_mkConst(v___x_4700_, v_us_4703_);
v___x_4755_ = l_Lean_mkAppN(v___x_4754_, v___x_4714_);
lean_dec_ref(v___x_4714_);
if (v_isShared_4753_ == 0)
{
lean_ctor_set(v___x_4752_, 0, v___x_4755_);
v___x_4757_ = v___x_4752_;
goto v_reusejp_4756_;
}
else
{
lean_object* v_reuseFailAlloc_4758_; 
v_reuseFailAlloc_4758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4758_, 0, v___x_4755_);
v___x_4757_ = v_reuseFailAlloc_4758_;
goto v_reusejp_4756_;
}
v_reusejp_4756_:
{
return v___x_4757_;
}
}
}
else
{
lean_object* v_a_4761_; lean_object* v___x_4763_; uint8_t v_isShared_4764_; uint8_t v_isSharedCheck_4768_; 
lean_dec_ref(v___x_4714_);
lean_dec(v_us_4703_);
lean_dec(v___x_4700_);
v_a_4761_ = lean_ctor_get(v___x_4750_, 0);
v_isSharedCheck_4768_ = !lean_is_exclusive(v___x_4750_);
if (v_isSharedCheck_4768_ == 0)
{
v___x_4763_ = v___x_4750_;
v_isShared_4764_ = v_isSharedCheck_4768_;
goto v_resetjp_4762_;
}
else
{
lean_inc(v_a_4761_);
lean_dec(v___x_4750_);
v___x_4763_ = lean_box(0);
v_isShared_4764_ = v_isSharedCheck_4768_;
goto v_resetjp_4762_;
}
v_resetjp_4762_:
{
lean_object* v___x_4766_; 
if (v_isShared_4764_ == 0)
{
v___x_4766_ = v___x_4763_;
goto v_reusejp_4765_;
}
else
{
lean_object* v_reuseFailAlloc_4767_; 
v_reuseFailAlloc_4767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4767_, 0, v_a_4761_);
v___x_4766_ = v_reuseFailAlloc_4767_;
goto v_reusejp_4765_;
}
v_reusejp_4765_:
{
return v___x_4766_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_4734_);
lean_dec_ref(v___x_4714_);
lean_dec(v_us_4703_);
lean_dec(v___x_4702_);
lean_dec(v_a_4701_);
lean_dec(v___x_4700_);
lean_dec_ref(v___x_4699_);
lean_dec_ref(v___x_4694_);
return v___x_4737_;
}
}
else
{
lean_dec(v_a_4734_);
lean_dec_ref(v___x_4724_);
lean_dec_ref(v___x_4714_);
lean_dec(v_us_4703_);
lean_dec(v___x_4702_);
lean_dec(v_a_4701_);
lean_dec(v___x_4700_);
lean_dec_ref(v___x_4699_);
lean_dec_ref(v___x_4694_);
return v___x_4735_;
}
}
else
{
lean_dec_ref(v___x_4729_);
lean_dec_ref(v___x_4724_);
lean_dec_ref(v___x_4714_);
lean_dec(v_us_4703_);
lean_dec(v___x_4702_);
lean_dec(v_a_4701_);
lean_dec(v___x_4700_);
lean_dec_ref(v___x_4699_);
lean_dec_ref(v_val_4698_);
lean_dec_ref(v___x_4694_);
return v___x_4733_;
}
}
else
{
lean_dec_ref(v___x_4729_);
lean_dec_ref(v___x_4724_);
lean_dec_ref(v___x_4714_);
lean_dec(v_us_4703_);
lean_dec(v___x_4702_);
lean_dec(v_a_4701_);
lean_dec(v___x_4700_);
lean_dec_ref(v___x_4699_);
lean_dec_ref(v_val_4698_);
lean_dec_ref(v___x_4694_);
return v___x_4730_;
}
}
else
{
lean_dec_ref(v___x_4724_);
lean_dec_ref(v___x_4714_);
lean_dec(v_us_4703_);
lean_dec(v___x_4702_);
lean_dec(v_a_4701_);
lean_dec(v___x_4700_);
lean_dec_ref(v___x_4699_);
lean_dec_ref(v_val_4698_);
lean_dec_ref(v___x_4695_);
lean_dec_ref(v___x_4694_);
return v___x_4727_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___lam__0___boxed(lean_object** _args){
lean_object* v_lhs_4795_ = _args[0];
lean_object* v_dummy_4796_ = _args[1];
lean_object* v___x_4797_ = _args[2];
lean_object* v_indices_4798_ = _args[3];
lean_object* v___x_4799_ = _args[4];
lean_object* v___x_4800_ = _args[5];
lean_object* v___x_4801_ = _args[6];
lean_object* v___x_4802_ = _args[7];
lean_object* v___x_4803_ = _args[8];
lean_object* v_val_4804_ = _args[9];
lean_object* v___x_4805_ = _args[10];
lean_object* v___x_4806_ = _args[11];
lean_object* v_a_4807_ = _args[12];
lean_object* v___x_4808_ = _args[13];
lean_object* v_us_4809_ = _args[14];
lean_object* v_major_4810_ = _args[15];
lean_object* v___y_4811_ = _args[16];
lean_object* v___y_4812_ = _args[17];
lean_object* v___y_4813_ = _args[18];
lean_object* v___y_4814_ = _args[19];
lean_object* v___y_4815_ = _args[20];
lean_object* v___y_4816_ = _args[21];
_start:
{
uint8_t v___x_44906__boxed_4817_; uint8_t v___x_44907__boxed_4818_; lean_object* v_res_4819_; 
v___x_44906__boxed_4817_ = lean_unbox(v___x_4802_);
v___x_44907__boxed_4818_ = lean_unbox(v___x_4803_);
v_res_4819_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___lam__0(v_lhs_4795_, v_dummy_4796_, v___x_4797_, v_indices_4798_, v___x_4799_, v___x_4800_, v___x_4801_, v___x_44906__boxed_4817_, v___x_44907__boxed_4818_, v_val_4804_, v___x_4805_, v___x_4806_, v_a_4807_, v___x_4808_, v_us_4809_, v_major_4810_, v___y_4811_, v___y_4812_, v___y_4813_, v___y_4814_, v___y_4815_);
lean_dec(v___y_4815_);
lean_dec_ref(v___y_4814_);
lean_dec(v___y_4813_);
lean_dec_ref(v___y_4812_);
lean_dec_ref(v___y_4811_);
lean_dec_ref(v_indices_4798_);
lean_dec(v___x_4797_);
return v_res_4819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___lam__1(lean_object* v_lhs_4820_, lean_object* v_dummy_4821_, lean_object* v___x_4822_, lean_object* v___x_4823_, lean_object* v___x_4824_, lean_object* v___x_4825_, uint8_t v___x_4826_, uint8_t v___x_4827_, lean_object* v_val_4828_, lean_object* v___x_4829_, lean_object* v___x_4830_, lean_object* v_a_4831_, lean_object* v___x_4832_, lean_object* v_us_4833_, lean_object* v___x_4834_, lean_object* v_indices_4835_, lean_object* v_x_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_){
_start:
{
lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___f_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; 
v___x_4843_ = lean_box(v___x_4826_);
v___x_4844_ = lean_box(v___x_4827_);
lean_inc_ref(v_indices_4835_);
v___f_4845_ = lean_alloc_closure((void*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___lam__0___boxed), 22, 15);
lean_closure_set(v___f_4845_, 0, v_lhs_4820_);
lean_closure_set(v___f_4845_, 1, v_dummy_4821_);
lean_closure_set(v___f_4845_, 2, v___x_4822_);
lean_closure_set(v___f_4845_, 3, v_indices_4835_);
lean_closure_set(v___f_4845_, 4, v___x_4823_);
lean_closure_set(v___f_4845_, 5, v___x_4824_);
lean_closure_set(v___f_4845_, 6, v___x_4825_);
lean_closure_set(v___f_4845_, 7, v___x_4843_);
lean_closure_set(v___f_4845_, 8, v___x_4844_);
lean_closure_set(v___f_4845_, 9, v_val_4828_);
lean_closure_set(v___f_4845_, 10, v___x_4829_);
lean_closure_set(v___f_4845_, 11, v___x_4830_);
lean_closure_set(v___f_4845_, 12, v_a_4831_);
lean_closure_set(v___f_4845_, 13, v___x_4832_);
lean_closure_set(v___f_4845_, 14, v_us_4833_);
v___x_4846_ = l_Lean_mkAppN(v___x_4834_, v_indices_4835_);
lean_dec_ref(v_indices_4835_);
v___x_4847_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___lam__1___closed__1));
v___x_4848_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__6___redArg(v___x_4847_, v___x_4846_, v___f_4845_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_);
return v___x_4848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__12___boxed(lean_object* v_as_4849_, lean_object* v_sz_4850_, lean_object* v_i_4851_, lean_object* v_b_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_){
_start:
{
size_t v_sz_boxed_4859_; size_t v_i_boxed_4860_; lean_object* v_res_4861_; 
v_sz_boxed_4859_ = lean_unbox_usize(v_sz_4850_);
lean_dec(v_sz_4850_);
v_i_boxed_4860_ = lean_unbox_usize(v_i_4851_);
lean_dec(v_i_4851_);
v_res_4861_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__12(v_as_4849_, v_sz_boxed_4859_, v_i_boxed_4860_, v_b_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_, v___y_4857_);
lean_dec(v___y_4857_);
lean_dec_ref(v___y_4856_);
lean_dec(v___y_4855_);
lean_dec_ref(v___y_4854_);
lean_dec_ref(v___y_4853_);
lean_dec_ref(v_as_4849_);
return v_res_4861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___boxed(lean_object* v_ys_4862_, lean_object* v_lhs_4863_, lean_object* v_rhs_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_, lean_object* v_a_4868_, lean_object* v_a_4869_, lean_object* v_a_4870_){
_start:
{
lean_object* v_res_4871_; 
v_res_4871_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep(v_ys_4862_, v_lhs_4863_, v_rhs_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_);
lean_dec(v_a_4869_);
lean_dec_ref(v_a_4868_);
lean_dec(v_a_4867_);
lean_dec_ref(v_a_4866_);
lean_dec_ref(v_a_4865_);
lean_dec_ref(v_ys_4862_);
return v_res_4871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof___boxed(lean_object* v_info_4872_, lean_object* v_lhs_4873_, lean_object* v_a_4874_, lean_object* v_a_4875_, lean_object* v_a_4876_, lean_object* v_a_4877_, lean_object* v_a_4878_, lean_object* v_a_4879_){
_start:
{
lean_object* v_res_4880_; 
v_res_4880_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof(v_info_4872_, v_lhs_4873_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_, v_a_4878_);
lean_dec(v_a_4878_);
lean_dec_ref(v_a_4877_);
lean_dec(v_a_4876_);
lean_dec_ref(v_a_4875_);
lean_dec_ref(v_a_4874_);
return v_res_4880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___boxed(lean_object* v_ys_4881_, lean_object* v_lhs_4882_, lean_object* v_rhs_4883_, lean_object* v_a_4884_, lean_object* v_a_4885_, lean_object* v_a_4886_, lean_object* v_a_4887_, lean_object* v_a_4888_, lean_object* v_a_4889_){
_start:
{
lean_object* v_res_4890_; 
v_res_4890_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof(v_ys_4881_, v_lhs_4882_, v_rhs_4883_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_, v_a_4888_);
lean_dec(v_a_4888_);
lean_dec_ref(v_a_4887_);
lean_dec(v_a_4886_);
lean_dec_ref(v_a_4885_);
lean_dec_ref(v_a_4884_);
lean_dec_ref(v_ys_4881_);
return v_res_4890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___boxed(lean_object* v_lhs_4891_, lean_object* v_rhs_4892_, lean_object* v_a_4893_, lean_object* v_a_4894_, lean_object* v_a_4895_, lean_object* v_a_4896_, lean_object* v_a_4897_, lean_object* v_a_4898_){
_start:
{
lean_object* v_res_4899_; 
v_res_4899_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma(v_lhs_4891_, v_rhs_4892_, v_a_4893_, v_a_4894_, v_a_4895_, v_a_4896_, v_a_4897_);
lean_dec(v_a_4897_);
lean_dec(v_a_4895_);
lean_dec_ref(v_a_4894_);
lean_dec_ref(v_a_4893_);
return v_res_4899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__7(lean_object* v_00_u03b1_4900_, lean_object* v_type_4901_, lean_object* v_k_4902_, uint8_t v_cleanupAnnotations_4903_, uint8_t v_whnfType_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_){
_start:
{
lean_object* v___x_4911_; 
v___x_4911_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__7___redArg(v_type_4901_, v_k_4902_, v_cleanupAnnotations_4903_, v_whnfType_4904_, v___y_4905_, v___y_4906_, v___y_4907_, v___y_4908_, v___y_4909_);
return v___x_4911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__7___boxed(lean_object* v_00_u03b1_4912_, lean_object* v_type_4913_, lean_object* v_k_4914_, lean_object* v_cleanupAnnotations_4915_, lean_object* v_whnfType_4916_, lean_object* v___y_4917_, lean_object* v___y_4918_, lean_object* v___y_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4923_; uint8_t v_whnfType_boxed_4924_; lean_object* v_res_4925_; 
v_cleanupAnnotations_boxed_4923_ = lean_unbox(v_cleanupAnnotations_4915_);
v_whnfType_boxed_4924_ = lean_unbox(v_whnfType_4916_);
v_res_4925_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__7(v_00_u03b1_4912_, v_type_4913_, v_k_4914_, v_cleanupAnnotations_boxed_4923_, v_whnfType_boxed_4924_, v___y_4917_, v___y_4918_, v___y_4919_, v___y_4920_, v___y_4921_);
lean_dec(v___y_4921_);
lean_dec_ref(v___y_4920_);
lean_dec(v___y_4919_);
lean_dec_ref(v___y_4918_);
lean_dec_ref(v___y_4917_);
return v_res_4925_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8(lean_object* v_00_u03b1_4926_, lean_object* v_ref_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_){
_start:
{
lean_object* v___x_4934_; 
v___x_4934_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___redArg(v_ref_4927_);
return v___x_4934_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8___boxed(lean_object* v_00_u03b1_4935_, lean_object* v_ref_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_){
_start:
{
lean_object* v_res_4943_; 
v_res_4943_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__8(v_00_u03b1_4935_, v_ref_4936_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_);
lean_dec(v___y_4941_);
lean_dec_ref(v___y_4940_);
lean_dec(v___y_4939_);
lean_dec_ref(v___y_4938_);
lean_dec_ref(v___y_4937_);
return v_res_4943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__13(lean_object* v_00_u03b1_4944_, lean_object* v_type_4945_, lean_object* v_maxFVars_x3f_4946_, lean_object* v_k_4947_, uint8_t v_cleanupAnnotations_4948_, uint8_t v_whnfType_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_){
_start:
{
lean_object* v___x_4956_; 
v___x_4956_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__13___redArg(v_type_4945_, v_maxFVars_x3f_4946_, v_k_4947_, v_cleanupAnnotations_4948_, v_whnfType_4949_, v___y_4950_, v___y_4951_, v___y_4952_, v___y_4953_, v___y_4954_);
return v___x_4956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__13___boxed(lean_object* v_00_u03b1_4957_, lean_object* v_type_4958_, lean_object* v_maxFVars_x3f_4959_, lean_object* v_k_4960_, lean_object* v_cleanupAnnotations_4961_, lean_object* v_whnfType_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4969_; uint8_t v_whnfType_boxed_4970_; lean_object* v_res_4971_; 
v_cleanupAnnotations_boxed_4969_ = lean_unbox(v_cleanupAnnotations_4961_);
v_whnfType_boxed_4970_ = lean_unbox(v_whnfType_4962_);
v_res_4971_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemmaProof_spec__13(v_00_u03b1_4957_, v_type_4958_, v_maxFVars_x3f_4959_, v_k_4960_, v_cleanupAnnotations_boxed_4969_, v_whnfType_boxed_4970_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_, v___y_4967_);
lean_dec(v___y_4967_);
lean_dec_ref(v___y_4966_);
lean_dec(v___y_4965_);
lean_dec_ref(v___y_4964_);
lean_dec_ref(v___y_4963_);
return v_res_4971_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof_spec__1(lean_object* v_cls_4972_, lean_object* v_msg_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_){
_start:
{
lean_object* v___x_4980_; 
v___x_4980_ = l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof_spec__1___redArg(v_cls_4972_, v_msg_4973_, v___y_4975_, v___y_4976_, v___y_4977_, v___y_4978_);
return v___x_4980_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof_spec__1___boxed(lean_object* v_cls_4981_, lean_object* v_msg_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_){
_start:
{
lean_object* v_res_4989_; 
v_res_4989_ = l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof_spec__1(v_cls_4981_, v_msg_4982_, v___y_4983_, v___y_4984_, v___y_4985_, v___y_4986_, v___y_4987_);
lean_dec(v___y_4987_);
lean_dec_ref(v___y_4986_);
lean_dec(v___y_4985_);
lean_dec_ref(v___y_4984_);
lean_dec_ref(v___y_4983_);
return v_res_4989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep_spec__3(lean_object* v_a_4990_, lean_object* v_as_4991_, size_t v_sz_4992_, size_t v_i_4993_, lean_object* v_b_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_){
_start:
{
lean_object* v___x_5001_; 
v___x_5001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep_spec__3___redArg(v_a_4990_, v_as_4991_, v_sz_4992_, v_i_4993_, v_b_4994_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_);
return v___x_5001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep_spec__3___boxed(lean_object* v_a_5002_, lean_object* v_as_5003_, lean_object* v_sz_5004_, lean_object* v_i_5005_, lean_object* v_b_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_){
_start:
{
size_t v_sz_boxed_5013_; size_t v_i_boxed_5014_; lean_object* v_res_5015_; 
v_sz_boxed_5013_ = lean_unbox_usize(v_sz_5004_);
lean_dec(v_sz_5004_);
v_i_boxed_5014_ = lean_unbox_usize(v_i_5005_);
lean_dec(v_i_5005_);
v_res_5015_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep_spec__3(v_a_5002_, v_as_5003_, v_sz_boxed_5013_, v_i_boxed_5014_, v_b_5006_, v___y_5007_, v___y_5008_, v___y_5009_, v___y_5010_, v___y_5011_);
lean_dec(v___y_5011_);
lean_dec_ref(v___y_5010_);
lean_dec(v___y_5009_);
lean_dec_ref(v___y_5008_);
lean_dec_ref(v___y_5007_);
lean_dec_ref(v_as_5003_);
return v_res_5015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__6_spec__6(lean_object* v_00_u03b1_5016_, lean_object* v_name_5017_, uint8_t v_bi_5018_, lean_object* v_type_5019_, lean_object* v_k_5020_, uint8_t v_kind_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_){
_start:
{
lean_object* v___x_5028_; 
v___x_5028_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__6_spec__6___redArg(v_name_5017_, v_bi_5018_, v_type_5019_, v_k_5020_, v_kind_5021_, v___y_5022_, v___y_5023_, v___y_5024_, v___y_5025_, v___y_5026_);
return v___x_5028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__6_spec__6___boxed(lean_object* v_00_u03b1_5029_, lean_object* v_name_5030_, lean_object* v_bi_5031_, lean_object* v_type_5032_, lean_object* v_k_5033_, lean_object* v_kind_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_, lean_object* v___y_5037_, lean_object* v___y_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_){
_start:
{
uint8_t v_bi_boxed_5041_; uint8_t v_kind_boxed_5042_; lean_object* v_res_5043_; 
v_bi_boxed_5041_ = lean_unbox(v_bi_5031_);
v_kind_boxed_5042_ = lean_unbox(v_kind_5034_);
v_res_5043_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__6_spec__6(v_00_u03b1_5029_, v_name_5030_, v_bi_boxed_5041_, v_type_5032_, v_k_5033_, v_kind_boxed_5042_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_);
lean_dec(v___y_5039_);
lean_dec_ref(v___y_5038_);
lean_dec(v___y_5037_);
lean_dec_ref(v___y_5036_);
lean_dec_ref(v___y_5035_);
return v_res_5043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__6(lean_object* v_00_u03b1_5044_, lean_object* v_name_5045_, lean_object* v_type_5046_, lean_object* v_k_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_){
_start:
{
lean_object* v___x_5054_; 
v___x_5054_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__6___redArg(v_name_5045_, v_type_5046_, v_k_5047_, v___y_5048_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_);
return v___x_5054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__6___boxed(lean_object* v_00_u03b1_5055_, lean_object* v_name_5056_, lean_object* v_type_5057_, lean_object* v_k_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_){
_start:
{
lean_object* v_res_5065_; 
v_res_5065_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma_spec__6(v_00_u03b1_5055_, v_name_5056_, v_type_5057_, v_k_5058_, v___y_5059_, v___y_5060_, v___y_5061_, v___y_5062_, v___y_5063_);
lean_dec(v___y_5063_);
lean_dec_ref(v___y_5062_);
lean_dec(v___y_5061_);
lean_dec_ref(v___y_5060_);
lean_dec_ref(v___y_5059_);
return v_res_5065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_main_step(lean_object* v_lhs_5066_, lean_object* v_rhs_5067_, lean_object* v_a_5068_, lean_object* v_a_5069_, lean_object* v_a_5070_, lean_object* v_a_5071_, lean_object* v_a_5072_){
_start:
{
lean_object* v___x_5074_; 
lean_inc_ref(v_rhs_5067_);
lean_inc_ref(v_lhs_5066_);
v___x_5074_ = l_Lean_Meta_isExprDefEq(v_lhs_5066_, v_rhs_5067_, v_a_5069_, v_a_5070_, v_a_5071_, v_a_5072_);
if (lean_obj_tag(v___x_5074_) == 0)
{
lean_object* v_a_5075_; uint8_t v___x_5076_; 
v_a_5075_ = lean_ctor_get(v___x_5074_, 0);
lean_inc(v_a_5075_);
lean_dec_ref(v___x_5074_);
v___x_5076_ = lean_unbox(v_a_5075_);
lean_dec(v_a_5075_);
if (v___x_5076_ == 0)
{
lean_object* v___x_5077_; 
lean_inc_ref(v_a_5068_);
v___x_5077_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_recToSizeOf(v_lhs_5066_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_, v_a_5072_);
if (lean_obj_tag(v___x_5077_) == 0)
{
lean_object* v_a_5078_; lean_object* v___x_5079_; 
v_a_5078_ = lean_ctor_get(v___x_5077_, 0);
lean_inc(v_a_5078_);
lean_dec_ref(v___x_5077_);
lean_inc_ref(v_a_5071_);
v___x_5079_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma(v_a_5078_, v_rhs_5067_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_, v_a_5072_);
return v___x_5079_;
}
else
{
lean_dec_ref(v_rhs_5067_);
return v___x_5077_;
}
}
else
{
lean_object* v___x_5080_; 
lean_dec_ref(v_lhs_5066_);
v___x_5080_ = l_Lean_Meta_mkEqRefl(v_rhs_5067_, v_a_5069_, v_a_5070_, v_a_5071_, v_a_5072_);
return v___x_5080_;
}
}
else
{
lean_object* v_a_5081_; lean_object* v___x_5083_; uint8_t v_isShared_5084_; uint8_t v_isSharedCheck_5088_; 
lean_dec_ref(v_rhs_5067_);
lean_dec_ref(v_lhs_5066_);
v_a_5081_ = lean_ctor_get(v___x_5074_, 0);
v_isSharedCheck_5088_ = !lean_is_exclusive(v___x_5074_);
if (v_isSharedCheck_5088_ == 0)
{
v___x_5083_ = v___x_5074_;
v_isShared_5084_ = v_isSharedCheck_5088_;
goto v_resetjp_5082_;
}
else
{
lean_inc(v_a_5081_);
lean_dec(v___x_5074_);
v___x_5083_ = lean_box(0);
v_isShared_5084_ = v_isSharedCheck_5088_;
goto v_resetjp_5082_;
}
v_resetjp_5082_:
{
lean_object* v___x_5086_; 
if (v_isShared_5084_ == 0)
{
v___x_5086_ = v___x_5083_;
goto v_reusejp_5085_;
}
else
{
lean_object* v_reuseFailAlloc_5087_; 
v_reuseFailAlloc_5087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5087_, 0, v_a_5081_);
v___x_5086_ = v_reuseFailAlloc_5087_;
goto v_reusejp_5085_;
}
v_reusejp_5085_:
{
return v___x_5086_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_main_step___boxed(lean_object* v_lhs_5089_, lean_object* v_rhs_5090_, lean_object* v_a_5091_, lean_object* v_a_5092_, lean_object* v_a_5093_, lean_object* v_a_5094_, lean_object* v_a_5095_, lean_object* v_a_5096_){
_start:
{
lean_object* v_res_5097_; 
v_res_5097_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_main_step(v_lhs_5089_, v_rhs_5090_, v_a_5091_, v_a_5092_, v_a_5093_, v_a_5094_, v_a_5095_);
lean_dec(v_a_5095_);
lean_dec_ref(v_a_5094_);
lean_dec(v_a_5093_);
lean_dec_ref(v_a_5092_);
lean_dec_ref(v_a_5091_);
return v_res_5097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_main_loop(lean_object* v_lhs_5103_, lean_object* v_rhs_5104_, lean_object* v_a_5105_, lean_object* v_a_5106_, lean_object* v_a_5107_, lean_object* v_a_5108_, lean_object* v_a_5109_){
_start:
{
lean_object* v___y_5112_; lean_object* v___y_5113_; lean_object* v___y_5114_; lean_object* v___y_5115_; lean_object* v___y_5116_; lean_object* v___y_5126_; lean_object* v___y_5127_; lean_object* v___y_5128_; lean_object* v___y_5129_; lean_object* v___y_5130_; lean_object* v_cls_5163_; lean_object* v___x_5164_; 
v_cls_5163_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_main_loop___closed__1));
v___x_5164_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof_spec__0___redArg(v_cls_5163_, v_a_5108_);
if (lean_obj_tag(v___x_5164_) == 0)
{
lean_object* v_a_5165_; uint8_t v___x_5166_; 
v_a_5165_ = lean_ctor_get(v___x_5164_, 0);
lean_inc(v_a_5165_);
lean_dec_ref(v___x_5164_);
v___x_5166_ = lean_unbox(v_a_5165_);
lean_dec(v_a_5165_);
if (v___x_5166_ == 0)
{
v___y_5126_ = v_a_5105_;
v___y_5127_ = v_a_5106_;
v___y_5128_ = v_a_5107_;
v___y_5129_ = v_a_5108_;
v___y_5130_ = v_a_5109_;
goto v___jp_5125_;
}
else
{
lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; 
lean_inc_ref(v_lhs_5103_);
v___x_5167_ = l_Lean_MessageData_ofExpr(v_lhs_5103_);
v___x_5168_ = lean_obj_once(&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__4, &l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__4_once, _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__4);
v___x_5169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5169_, 0, v___x_5167_);
lean_ctor_set(v___x_5169_, 1, v___x_5168_);
lean_inc_ref(v_rhs_5104_);
v___x_5170_ = l_Lean_MessageData_ofExpr(v_rhs_5104_);
v___x_5171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5171_, 0, v___x_5169_);
lean_ctor_set(v___x_5171_, 1, v___x_5170_);
v___x_5172_ = l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof_spec__1___redArg(v_cls_5163_, v___x_5171_, v_a_5106_, v_a_5107_, v_a_5108_, v_a_5109_);
if (lean_obj_tag(v___x_5172_) == 0)
{
lean_dec_ref(v___x_5172_);
v___y_5126_ = v_a_5105_;
v___y_5127_ = v_a_5106_;
v___y_5128_ = v_a_5107_;
v___y_5129_ = v_a_5108_;
v___y_5130_ = v_a_5109_;
goto v___jp_5125_;
}
else
{
lean_object* v_a_5173_; lean_object* v___x_5175_; uint8_t v_isShared_5176_; uint8_t v_isSharedCheck_5180_; 
lean_dec_ref(v_rhs_5104_);
lean_dec_ref(v_lhs_5103_);
v_a_5173_ = lean_ctor_get(v___x_5172_, 0);
v_isSharedCheck_5180_ = !lean_is_exclusive(v___x_5172_);
if (v_isSharedCheck_5180_ == 0)
{
v___x_5175_ = v___x_5172_;
v_isShared_5176_ = v_isSharedCheck_5180_;
goto v_resetjp_5174_;
}
else
{
lean_inc(v_a_5173_);
lean_dec(v___x_5172_);
v___x_5175_ = lean_box(0);
v_isShared_5176_ = v_isSharedCheck_5180_;
goto v_resetjp_5174_;
}
v_resetjp_5174_:
{
lean_object* v___x_5178_; 
if (v_isShared_5176_ == 0)
{
v___x_5178_ = v___x_5175_;
goto v_reusejp_5177_;
}
else
{
lean_object* v_reuseFailAlloc_5179_; 
v_reuseFailAlloc_5179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5179_, 0, v_a_5173_);
v___x_5178_ = v_reuseFailAlloc_5179_;
goto v_reusejp_5177_;
}
v_reusejp_5177_:
{
return v___x_5178_;
}
}
}
}
}
else
{
lean_object* v_a_5181_; lean_object* v___x_5183_; uint8_t v_isShared_5184_; uint8_t v_isSharedCheck_5188_; 
lean_dec_ref(v_rhs_5104_);
lean_dec_ref(v_lhs_5103_);
v_a_5181_ = lean_ctor_get(v___x_5164_, 0);
v_isSharedCheck_5188_ = !lean_is_exclusive(v___x_5164_);
if (v_isSharedCheck_5188_ == 0)
{
v___x_5183_ = v___x_5164_;
v_isShared_5184_ = v_isSharedCheck_5188_;
goto v_resetjp_5182_;
}
else
{
lean_inc(v_a_5181_);
lean_dec(v___x_5164_);
v___x_5183_ = lean_box(0);
v_isShared_5184_ = v_isSharedCheck_5188_;
goto v_resetjp_5182_;
}
v_resetjp_5182_:
{
lean_object* v___x_5186_; 
if (v_isShared_5184_ == 0)
{
v___x_5186_ = v___x_5183_;
goto v_reusejp_5185_;
}
else
{
lean_object* v_reuseFailAlloc_5187_; 
v_reuseFailAlloc_5187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5187_, 0, v_a_5181_);
v___x_5186_ = v_reuseFailAlloc_5187_;
goto v_reusejp_5185_;
}
v_reusejp_5185_:
{
return v___x_5186_;
}
}
}
v___jp_5111_:
{
lean_object* v___x_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; 
v___x_5117_ = lean_obj_once(&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__1, &l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__1_once, _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__1);
v___x_5118_ = l_Lean_indentExpr(v_lhs_5103_);
v___x_5119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5119_, 0, v___x_5117_);
lean_ctor_set(v___x_5119_, 1, v___x_5118_);
v___x_5120_ = lean_obj_once(&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__3, &l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__3_once, _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__3);
v___x_5121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5121_, 0, v___x_5119_);
lean_ctor_set(v___x_5121_, 1, v___x_5120_);
v___x_5122_ = l_Lean_indentExpr(v_rhs_5104_);
v___x_5123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5123_, 0, v___x_5121_);
lean_ctor_set(v___x_5123_, 1, v___x_5122_);
lean_inc_ref(v___y_5112_);
v___x_5124_ = l_Lean_Meta_SizeOfSpecNested_throwUnexpected___redArg(v___x_5123_, v___y_5112_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_);
return v___x_5124_;
}
v___jp_5125_:
{
lean_object* v___x_5131_; 
lean_inc_ref(v_rhs_5104_);
lean_inc_ref(v_lhs_5103_);
v___x_5131_ = l_Lean_Meta_isExprDefEq(v_lhs_5103_, v_rhs_5104_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_);
if (lean_obj_tag(v___x_5131_) == 0)
{
lean_object* v_a_5132_; uint8_t v___x_5133_; 
v_a_5132_ = lean_ctor_get(v___x_5131_, 0);
lean_inc(v_a_5132_);
lean_dec_ref(v___x_5131_);
v___x_5133_ = lean_unbox(v_a_5132_);
lean_dec(v_a_5132_);
if (v___x_5133_ == 0)
{
lean_object* v___x_5134_; 
lean_inc_ref(v_lhs_5103_);
v___x_5134_ = l_Lean_Meta_whnfI(v_lhs_5103_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_);
if (lean_obj_tag(v___x_5134_) == 0)
{
lean_object* v_a_5135_; lean_object* v___x_5136_; 
v_a_5135_ = lean_ctor_get(v___x_5134_, 0);
lean_inc(v_a_5135_);
lean_dec_ref(v___x_5134_);
lean_inc_ref(v_rhs_5104_);
v___x_5136_ = l_Lean_Meta_whnfI(v_rhs_5104_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_);
if (lean_obj_tag(v___x_5136_) == 0)
{
lean_object* v_a_5137_; lean_object* v___x_5138_; 
v_a_5137_ = lean_ctor_get(v___x_5136_, 0);
lean_inc(v_a_5137_);
lean_dec_ref(v___x_5136_);
v___x_5138_ = l_Lean_Expr_natAdd_x3f(v_a_5135_);
lean_dec(v_a_5135_);
if (lean_obj_tag(v___x_5138_) == 1)
{
lean_object* v_val_5139_; lean_object* v_fst_5140_; lean_object* v_snd_5141_; lean_object* v___x_5142_; 
v_val_5139_ = lean_ctor_get(v___x_5138_, 0);
lean_inc(v_val_5139_);
lean_dec_ref(v___x_5138_);
v_fst_5140_ = lean_ctor_get(v_val_5139_, 0);
lean_inc(v_fst_5140_);
v_snd_5141_ = lean_ctor_get(v_val_5139_, 1);
lean_inc(v_snd_5141_);
lean_dec(v_val_5139_);
v___x_5142_ = l_Lean_Expr_natAdd_x3f(v_a_5137_);
lean_dec(v_a_5137_);
if (lean_obj_tag(v___x_5142_) == 1)
{
lean_object* v_val_5143_; lean_object* v_fst_5144_; lean_object* v_snd_5145_; lean_object* v___x_5146_; 
lean_dec_ref(v_rhs_5104_);
lean_dec_ref(v_lhs_5103_);
v_val_5143_ = lean_ctor_get(v___x_5142_, 0);
lean_inc(v_val_5143_);
lean_dec_ref(v___x_5142_);
v_fst_5144_ = lean_ctor_get(v_val_5143_, 0);
lean_inc(v_fst_5144_);
v_snd_5145_ = lean_ctor_get(v_val_5143_, 1);
lean_inc(v_snd_5145_);
lean_dec(v_val_5143_);
v___x_5146_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_main_loop(v_fst_5140_, v_fst_5144_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_);
if (lean_obj_tag(v___x_5146_) == 0)
{
lean_object* v_a_5147_; lean_object* v___x_5148_; 
v_a_5147_ = lean_ctor_get(v___x_5146_, 0);
lean_inc(v_a_5147_);
lean_dec_ref(v___x_5146_);
v___x_5148_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_main_step(v_snd_5141_, v_snd_5145_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_);
if (lean_obj_tag(v___x_5148_) == 0)
{
lean_object* v_a_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; 
v_a_5149_ = lean_ctor_get(v___x_5148_, 0);
lean_inc(v_a_5149_);
lean_dec_ref(v___x_5148_);
v___x_5150_ = lean_obj_once(&l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__6, &l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__6_once, _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__6);
v___x_5151_ = l_Lean_Meta_mkCongrArg(v___x_5150_, v_a_5147_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_);
if (lean_obj_tag(v___x_5151_) == 0)
{
lean_object* v_a_5152_; lean_object* v___x_5153_; 
v_a_5152_ = lean_ctor_get(v___x_5151_, 0);
lean_inc(v_a_5152_);
lean_dec_ref(v___x_5151_);
v___x_5153_ = l_Lean_Meta_mkCongr(v_a_5152_, v_a_5149_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_);
return v___x_5153_;
}
else
{
lean_dec(v_a_5149_);
return v___x_5151_;
}
}
else
{
lean_dec(v_a_5147_);
return v___x_5148_;
}
}
else
{
lean_dec(v_snd_5145_);
lean_dec(v_snd_5141_);
return v___x_5146_;
}
}
else
{
lean_dec(v___x_5142_);
lean_dec(v_snd_5141_);
lean_dec(v_fst_5140_);
v___y_5112_ = v___y_5126_;
v___y_5113_ = v___y_5127_;
v___y_5114_ = v___y_5128_;
v___y_5115_ = v___y_5129_;
v___y_5116_ = v___y_5130_;
goto v___jp_5111_;
}
}
else
{
lean_dec(v___x_5138_);
lean_dec(v_a_5137_);
v___y_5112_ = v___y_5126_;
v___y_5113_ = v___y_5127_;
v___y_5114_ = v___y_5128_;
v___y_5115_ = v___y_5129_;
v___y_5116_ = v___y_5130_;
goto v___jp_5111_;
}
}
else
{
lean_dec(v_a_5135_);
lean_dec_ref(v_rhs_5104_);
lean_dec_ref(v_lhs_5103_);
return v___x_5136_;
}
}
else
{
lean_dec_ref(v_rhs_5104_);
lean_dec_ref(v_lhs_5103_);
return v___x_5134_;
}
}
else
{
lean_object* v___x_5154_; 
lean_dec_ref(v_lhs_5103_);
v___x_5154_ = l_Lean_Meta_mkEqRefl(v_rhs_5104_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_);
return v___x_5154_;
}
}
else
{
lean_object* v_a_5155_; lean_object* v___x_5157_; uint8_t v_isShared_5158_; uint8_t v_isSharedCheck_5162_; 
lean_dec_ref(v_rhs_5104_);
lean_dec_ref(v_lhs_5103_);
v_a_5155_ = lean_ctor_get(v___x_5131_, 0);
v_isSharedCheck_5162_ = !lean_is_exclusive(v___x_5131_);
if (v_isSharedCheck_5162_ == 0)
{
v___x_5157_ = v___x_5131_;
v_isShared_5158_ = v_isSharedCheck_5162_;
goto v_resetjp_5156_;
}
else
{
lean_inc(v_a_5155_);
lean_dec(v___x_5131_);
v___x_5157_ = lean_box(0);
v_isShared_5158_ = v_isSharedCheck_5162_;
goto v_resetjp_5156_;
}
v_resetjp_5156_:
{
lean_object* v___x_5160_; 
if (v_isShared_5158_ == 0)
{
v___x_5160_ = v___x_5157_;
goto v_reusejp_5159_;
}
else
{
lean_object* v_reuseFailAlloc_5161_; 
v_reuseFailAlloc_5161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5161_, 0, v_a_5155_);
v___x_5160_ = v_reuseFailAlloc_5161_;
goto v_reusejp_5159_;
}
v_reusejp_5159_:
{
return v___x_5160_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_main_loop___boxed(lean_object* v_lhs_5189_, lean_object* v_rhs_5190_, lean_object* v_a_5191_, lean_object* v_a_5192_, lean_object* v_a_5193_, lean_object* v_a_5194_, lean_object* v_a_5195_, lean_object* v_a_5196_){
_start:
{
lean_object* v_res_5197_; 
v_res_5197_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_main_loop(v_lhs_5189_, v_rhs_5190_, v_a_5191_, v_a_5192_, v_a_5193_, v_a_5194_, v_a_5195_);
lean_dec(v_a_5195_);
lean_dec_ref(v_a_5194_);
lean_dec(v_a_5193_);
lean_dec_ref(v_a_5192_);
lean_dec_ref(v_a_5191_);
return v_res_5197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SizeOfSpecNested_main(lean_object* v_lhs_5198_, lean_object* v_rhs_5199_, lean_object* v_a_5200_, lean_object* v_a_5201_, lean_object* v_a_5202_, lean_object* v_a_5203_, lean_object* v_a_5204_){
_start:
{
lean_object* v___x_5206_; 
lean_inc_ref(v_rhs_5199_);
lean_inc_ref(v_lhs_5198_);
v___x_5206_ = l_Lean_Meta_isExprDefEq(v_lhs_5198_, v_rhs_5199_, v_a_5201_, v_a_5202_, v_a_5203_, v_a_5204_);
if (lean_obj_tag(v___x_5206_) == 0)
{
lean_object* v_a_5207_; uint8_t v___x_5208_; 
v_a_5207_ = lean_ctor_get(v___x_5206_, 0);
lean_inc(v_a_5207_);
lean_dec_ref(v___x_5206_);
v___x_5208_ = lean_unbox(v_a_5207_);
lean_dec(v_a_5207_);
if (v___x_5208_ == 0)
{
lean_object* v___x_5209_; 
v___x_5209_ = l_Lean_Meta_whnfI(v_lhs_5198_, v_a_5201_, v_a_5202_, v_a_5203_, v_a_5204_);
if (lean_obj_tag(v___x_5209_) == 0)
{
lean_object* v_a_5210_; lean_object* v___x_5211_; 
v_a_5210_ = lean_ctor_get(v___x_5209_, 0);
lean_inc(v_a_5210_);
lean_dec_ref(v___x_5209_);
v___x_5211_ = l_Lean_Meta_unfoldDefinition(v_a_5210_, v_a_5201_, v_a_5202_, v_a_5203_, v_a_5204_);
if (lean_obj_tag(v___x_5211_) == 0)
{
lean_object* v_a_5212_; lean_object* v___x_5213_; 
v_a_5212_ = lean_ctor_get(v___x_5211_, 0);
lean_inc(v_a_5212_);
lean_dec_ref(v___x_5211_);
v___x_5213_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_main_loop(v_a_5212_, v_rhs_5199_, v_a_5200_, v_a_5201_, v_a_5202_, v_a_5203_, v_a_5204_);
return v___x_5213_;
}
else
{
lean_dec_ref(v_rhs_5199_);
return v___x_5211_;
}
}
else
{
lean_dec_ref(v_rhs_5199_);
return v___x_5209_;
}
}
else
{
lean_object* v___x_5214_; 
lean_dec_ref(v_lhs_5198_);
v___x_5214_ = l_Lean_Meta_mkEqRefl(v_rhs_5199_, v_a_5201_, v_a_5202_, v_a_5203_, v_a_5204_);
return v___x_5214_;
}
}
else
{
lean_object* v_a_5215_; lean_object* v___x_5217_; uint8_t v_isShared_5218_; uint8_t v_isSharedCheck_5222_; 
lean_dec_ref(v_rhs_5199_);
lean_dec_ref(v_lhs_5198_);
v_a_5215_ = lean_ctor_get(v___x_5206_, 0);
v_isSharedCheck_5222_ = !lean_is_exclusive(v___x_5206_);
if (v_isSharedCheck_5222_ == 0)
{
v___x_5217_ = v___x_5206_;
v_isShared_5218_ = v_isSharedCheck_5222_;
goto v_resetjp_5216_;
}
else
{
lean_inc(v_a_5215_);
lean_dec(v___x_5206_);
v___x_5217_ = lean_box(0);
v_isShared_5218_ = v_isSharedCheck_5222_;
goto v_resetjp_5216_;
}
v_resetjp_5216_:
{
lean_object* v___x_5220_; 
if (v_isShared_5218_ == 0)
{
v___x_5220_ = v___x_5217_;
goto v_reusejp_5219_;
}
else
{
lean_object* v_reuseFailAlloc_5221_; 
v_reuseFailAlloc_5221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5221_, 0, v_a_5215_);
v___x_5220_ = v_reuseFailAlloc_5221_;
goto v_reusejp_5219_;
}
v_reusejp_5219_:
{
return v___x_5220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SizeOfSpecNested_main___boxed(lean_object* v_lhs_5223_, lean_object* v_rhs_5224_, lean_object* v_a_5225_, lean_object* v_a_5226_, lean_object* v_a_5227_, lean_object* v_a_5228_, lean_object* v_a_5229_, lean_object* v_a_5230_){
_start:
{
lean_object* v_res_5231_; 
v_res_5231_ = l_Lean_Meta_SizeOfSpecNested_main(v_lhs_5223_, v_rhs_5224_, v_a_5225_, v_a_5226_, v_a_5227_, v_a_5228_, v_a_5229_);
lean_dec(v_a_5229_);
lean_dec_ref(v_a_5228_);
lean_dec(v_a_5227_);
lean_dec_ref(v_a_5226_);
lean_dec_ref(v_a_5225_);
return v_res_5231_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__2___redArg(lean_object* v_a_5232_, lean_object* v_b_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_){
_start:
{
lean_object* v_array_5239_; lean_object* v_start_5240_; lean_object* v_stop_5241_; lean_object* v___x_5243_; uint8_t v_isShared_5244_; uint8_t v_isSharedCheck_5273_; 
v_array_5239_ = lean_ctor_get(v_a_5232_, 0);
v_start_5240_ = lean_ctor_get(v_a_5232_, 1);
v_stop_5241_ = lean_ctor_get(v_a_5232_, 2);
v_isSharedCheck_5273_ = !lean_is_exclusive(v_a_5232_);
if (v_isSharedCheck_5273_ == 0)
{
v___x_5243_ = v_a_5232_;
v_isShared_5244_ = v_isSharedCheck_5273_;
goto v_resetjp_5242_;
}
else
{
lean_inc(v_stop_5241_);
lean_inc(v_start_5240_);
lean_inc(v_array_5239_);
lean_dec(v_a_5232_);
v___x_5243_ = lean_box(0);
v_isShared_5244_ = v_isSharedCheck_5273_;
goto v_resetjp_5242_;
}
v_resetjp_5242_:
{
uint8_t v___x_5245_; 
v___x_5245_ = lean_nat_dec_lt(v_start_5240_, v_stop_5241_);
if (v___x_5245_ == 0)
{
lean_object* v___x_5246_; 
lean_del_object(v___x_5243_);
lean_dec(v_stop_5241_);
lean_dec(v_start_5240_);
lean_dec_ref(v_array_5239_);
v___x_5246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5246_, 0, v_b_5233_);
return v___x_5246_;
}
else
{
lean_object* v___x_5247_; lean_object* v___x_5248_; 
v___x_5247_ = lean_array_fget(v_array_5239_, v_start_5240_);
lean_inc(v___x_5247_);
v___x_5248_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_ignoreField(v___x_5247_, v___y_5234_, v___y_5235_, v___y_5236_, v___y_5237_);
if (lean_obj_tag(v___x_5248_) == 0)
{
lean_object* v_a_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5253_; 
v_a_5249_ = lean_ctor_get(v___x_5248_, 0);
lean_inc(v_a_5249_);
lean_dec_ref(v___x_5248_);
v___x_5250_ = lean_unsigned_to_nat(1u);
v___x_5251_ = lean_nat_add(v_start_5240_, v___x_5250_);
lean_dec(v_start_5240_);
if (v_isShared_5244_ == 0)
{
lean_ctor_set(v___x_5243_, 1, v___x_5251_);
v___x_5253_ = v___x_5243_;
goto v_reusejp_5252_;
}
else
{
lean_object* v_reuseFailAlloc_5264_; 
v_reuseFailAlloc_5264_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5264_, 0, v_array_5239_);
lean_ctor_set(v_reuseFailAlloc_5264_, 1, v___x_5251_);
lean_ctor_set(v_reuseFailAlloc_5264_, 2, v_stop_5241_);
v___x_5253_ = v_reuseFailAlloc_5264_;
goto v_reusejp_5252_;
}
v_reusejp_5252_:
{
uint8_t v___x_5254_; 
v___x_5254_ = lean_unbox(v_a_5249_);
lean_dec(v_a_5249_);
if (v___x_5254_ == 0)
{
lean_object* v___x_5255_; lean_object* v___x_5256_; lean_object* v___x_5257_; lean_object* v___x_5258_; 
v___x_5255_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop_spec__0___closed__0));
v___x_5256_ = lean_mk_empty_array_with_capacity(v___x_5250_);
v___x_5257_ = lean_array_push(v___x_5256_, v___x_5247_);
v___x_5258_ = l_Lean_Meta_mkAppM(v___x_5255_, v___x_5257_, v___y_5234_, v___y_5235_, v___y_5236_, v___y_5237_);
if (lean_obj_tag(v___x_5258_) == 0)
{
lean_object* v_a_5259_; lean_object* v___x_5260_; 
v_a_5259_ = lean_ctor_get(v___x_5258_, 0);
lean_inc(v_a_5259_);
lean_dec_ref(v___x_5258_);
v___x_5260_ = l_Lean_Meta_mkAdd(v_b_5233_, v_a_5259_, v___y_5234_, v___y_5235_, v___y_5236_, v___y_5237_);
if (lean_obj_tag(v___x_5260_) == 0)
{
lean_object* v_a_5261_; 
v_a_5261_ = lean_ctor_get(v___x_5260_, 0);
lean_inc(v_a_5261_);
lean_dec_ref(v___x_5260_);
v_a_5232_ = v___x_5253_;
v_b_5233_ = v_a_5261_;
goto _start;
}
else
{
lean_dec_ref(v___x_5253_);
return v___x_5260_;
}
}
else
{
lean_dec_ref(v___x_5253_);
lean_dec_ref(v_b_5233_);
return v___x_5258_;
}
}
else
{
lean_dec(v___x_5247_);
v_a_5232_ = v___x_5253_;
goto _start;
}
}
}
else
{
lean_object* v_a_5265_; lean_object* v___x_5267_; uint8_t v_isShared_5268_; uint8_t v_isSharedCheck_5272_; 
lean_dec(v___x_5247_);
lean_del_object(v___x_5243_);
lean_dec(v_stop_5241_);
lean_dec(v_start_5240_);
lean_dec_ref(v_array_5239_);
lean_dec_ref(v_b_5233_);
v_a_5265_ = lean_ctor_get(v___x_5248_, 0);
v_isSharedCheck_5272_ = !lean_is_exclusive(v___x_5248_);
if (v_isSharedCheck_5272_ == 0)
{
v___x_5267_ = v___x_5248_;
v_isShared_5268_ = v_isSharedCheck_5272_;
goto v_resetjp_5266_;
}
else
{
lean_inc(v_a_5265_);
lean_dec(v___x_5248_);
v___x_5267_ = lean_box(0);
v_isShared_5268_ = v_isSharedCheck_5272_;
goto v_resetjp_5266_;
}
v_resetjp_5266_:
{
lean_object* v___x_5270_; 
if (v_isShared_5268_ == 0)
{
v___x_5270_ = v___x_5267_;
goto v_reusejp_5269_;
}
else
{
lean_object* v_reuseFailAlloc_5271_; 
v_reuseFailAlloc_5271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5271_, 0, v_a_5265_);
v___x_5270_ = v_reuseFailAlloc_5271_;
goto v_reusejp_5269_;
}
v_reusejp_5269_:
{
return v___x_5270_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__2___redArg___boxed(lean_object* v_a_5274_, lean_object* v_b_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_){
_start:
{
lean_object* v_res_5281_; 
v_res_5281_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__2___redArg(v_a_5274_, v_b_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_);
lean_dec(v___y_5279_);
lean_dec_ref(v___y_5278_);
lean_dec(v___y_5277_);
lean_dec_ref(v___y_5276_);
return v_res_5281_;
}
}
static lean_object* _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5283_; lean_object* v___x_5284_; 
v___x_5283_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__0));
v___x_5284_ = l_Lean_stringToMessageData(v___x_5283_);
return v___x_5284_;
}
}
static lean_object* _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5286_; lean_object* v___x_5287_; 
v___x_5286_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__2));
v___x_5287_ = l_Lean_stringToMessageData(v___x_5286_);
return v___x_5287_;
}
}
static lean_object* _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5289_; lean_object* v___x_5290_; 
v___x_5289_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__4));
v___x_5290_ = l_Lean_stringToMessageData(v___x_5289_);
return v___x_5290_;
}
}
static lean_object* _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__7(void){
_start:
{
lean_object* v___x_5292_; lean_object* v___x_5293_; 
v___x_5292_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__6));
v___x_5293_ = l_Lean_stringToMessageData(v___x_5292_);
return v___x_5293_;
}
}
static lean_object* _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__11(void){
_start:
{
lean_object* v___x_5298_; lean_object* v___x_5299_; 
v___x_5298_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__10));
v___x_5299_ = l_Lean_stringToMessageData(v___x_5298_);
return v___x_5299_;
}
}
static lean_object* _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__13(void){
_start:
{
lean_object* v___x_5301_; lean_object* v___x_5302_; 
v___x_5301_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__12));
v___x_5302_ = l_Lean_stringToMessageData(v___x_5301_);
return v___x_5302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0(lean_object* v___x_5303_, lean_object* v_indInfo_5304_, lean_object* v_levelParams_5305_, uint8_t v___x_5306_, lean_object* v_a_5307_, lean_object* v_a_5308_, lean_object* v___x_5309_, lean_object* v_sizeOfFns_5310_, lean_object* v_ctorName_5311_, lean_object* v___x_5312_, lean_object* v_recMap_5313_, lean_object* v___x_5314_, lean_object* v___x_5315_, lean_object* v___x_5316_, lean_object* v_name_5317_, lean_object* v___x_5318_, lean_object* v_localInsts_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_){
_start:
{
lean_object* v___y_5326_; lean_object* v___y_5327_; lean_object* v___y_5328_; lean_object* v___y_5329_; lean_object* v___y_5330_; lean_object* v___y_5331_; lean_object* v___y_5332_; lean_object* v___y_5349_; lean_object* v___y_5350_; lean_object* v___y_5351_; lean_object* v___y_5352_; lean_object* v___y_5353_; lean_object* v___y_5354_; lean_object* v___y_5355_; uint8_t v___y_5380_; uint8_t v___y_5381_; lean_object* v___y_5382_; lean_object* v___y_5383_; lean_object* v___y_5384_; lean_object* v___y_5385_; lean_object* v_thmValue_5386_; lean_object* v___y_5387_; lean_object* v___y_5388_; lean_object* v___y_5389_; lean_object* v___y_5390_; uint8_t v___y_5409_; lean_object* v___y_5410_; uint8_t v___y_5411_; lean_object* v___y_5412_; lean_object* v___y_5413_; lean_object* v___y_5414_; lean_object* v___y_5415_; lean_object* v___y_5416_; lean_object* v___y_5417_; lean_object* v___y_5418_; lean_object* v___y_5419_; lean_object* v___y_5420_; uint8_t v___y_5444_; uint8_t v___y_5445_; lean_object* v___y_5446_; lean_object* v___y_5447_; lean_object* v___y_5448_; lean_object* v___y_5449_; lean_object* v___y_5450_; lean_object* v___y_5451_; lean_object* v___y_5452_; lean_object* v___y_5453_; lean_object* v___y_5454_; lean_object* v___y_5455_; lean_object* v___y_5464_; lean_object* v___y_5465_; lean_object* v___y_5466_; lean_object* v___y_5467_; lean_object* v___y_5468_; lean_object* v___y_5469_; lean_object* v___y_5470_; lean_object* v___y_5471_; lean_object* v___x_5495_; 
lean_inc(v___y_5323_);
lean_inc_ref(v___y_5322_);
lean_inc(v___y_5321_);
lean_inc_ref(v___y_5320_);
lean_inc_ref(v___x_5303_);
v___x_5495_ = lean_infer_type(v___x_5303_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_);
if (lean_obj_tag(v___x_5495_) == 0)
{
lean_object* v_a_5496_; lean_object* v_toConstantVal_5497_; lean_object* v_numParams_5498_; lean_object* v_nargs_5499_; lean_object* v_dummy_5500_; lean_object* v___x_5501_; lean_object* v___x_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; lean_object* v___y_5506_; lean_object* v___x_5582_; uint8_t v___x_5583_; 
v_a_5496_ = lean_ctor_get(v___x_5495_, 0);
lean_inc(v_a_5496_);
lean_dec_ref(v___x_5495_);
v_toConstantVal_5497_ = lean_ctor_get(v_indInfo_5304_, 0);
v_numParams_5498_ = lean_ctor_get(v_indInfo_5304_, 1);
v_nargs_5499_ = l_Lean_Expr_getAppNumArgs(v_a_5496_);
v_dummy_5500_ = lean_obj_once(&l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__3, &l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__3_once, _init_l_Lean_Meta_mkSizeOfSpecLemmaInstance___closed__3);
lean_inc(v_nargs_5499_);
v___x_5501_ = lean_mk_array(v_nargs_5499_, v_dummy_5500_);
v___x_5502_ = lean_unsigned_to_nat(1u);
v___x_5503_ = lean_nat_sub(v_nargs_5499_, v___x_5502_);
lean_dec(v_nargs_5499_);
lean_inc(v_a_5496_);
v___x_5504_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_5496_, v___x_5501_, v___x_5503_);
v___x_5582_ = lean_array_get_size(v___x_5504_);
v___x_5583_ = lean_nat_dec_le(v_numParams_5498_, v___x_5318_);
if (v___x_5583_ == 0)
{
lean_object* v___x_5584_; 
lean_dec(v___x_5318_);
lean_inc(v_numParams_5498_);
v___x_5584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5584_, 0, v_numParams_5498_);
lean_ctor_set(v___x_5584_, 1, v___x_5582_);
v___y_5506_ = v___x_5584_;
goto v___jp_5505_;
}
else
{
lean_object* v___x_5585_; 
v___x_5585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5585_, 0, v___x_5318_);
lean_ctor_set(v___x_5585_, 1, v___x_5582_);
v___y_5506_ = v___x_5585_;
goto v___jp_5505_;
}
v___jp_5505_:
{
lean_object* v___x_5507_; 
lean_inc(v_a_5496_);
v___x_5507_ = l_Lean_Meta_getLevel(v_a_5496_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_);
if (lean_obj_tag(v___x_5507_) == 0)
{
lean_object* v_a_5508_; lean_object* v___x_5509_; lean_object* v___x_5510_; lean_object* v___x_5511_; lean_object* v___x_5512_; 
v_a_5508_ = lean_ctor_get(v___x_5507_, 0);
lean_inc(v_a_5508_);
lean_dec_ref(v___x_5507_);
lean_inc(v___x_5315_);
v___x_5509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5509_, 0, v_a_5508_);
lean_ctor_set(v___x_5509_, 1, v___x_5315_);
v___x_5510_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___lam__0___closed__1));
v___x_5511_ = l_Lean_mkConst(v___x_5510_, v___x_5315_);
v___x_5512_ = l_Lean_Meta_mkNumeral(v___x_5511_, v___x_5502_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_);
if (lean_obj_tag(v___x_5512_) == 0)
{
lean_object* v_a_5513_; lean_object* v___x_5514_; 
v_a_5513_ = lean_ctor_get(v___x_5512_, 0);
lean_inc(v_a_5513_);
lean_dec_ref(v___x_5512_);
lean_inc_ref(v___x_5314_);
v___x_5514_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__2___redArg(v___x_5314_, v_a_5513_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_);
if (lean_obj_tag(v___x_5514_) == 0)
{
lean_object* v_a_5515_; lean_object* v_lower_5516_; lean_object* v_upper_5517_; lean_object* v___x_5519_; uint8_t v_isShared_5520_; uint8_t v_isSharedCheck_5557_; 
v_a_5515_ = lean_ctor_get(v___x_5514_, 0);
lean_inc(v_a_5515_);
lean_dec_ref(v___x_5514_);
v_lower_5516_ = lean_ctor_get(v___y_5506_, 0);
v_upper_5517_ = lean_ctor_get(v___y_5506_, 1);
v_isSharedCheck_5557_ = !lean_is_exclusive(v___y_5506_);
if (v_isSharedCheck_5557_ == 0)
{
v___x_5519_ = v___y_5506_;
v_isShared_5520_ = v_isSharedCheck_5557_;
goto v_resetjp_5518_;
}
else
{
lean_inc(v_upper_5517_);
lean_inc(v_lower_5516_);
lean_dec(v___y_5506_);
v___x_5519_ = lean_box(0);
v_isShared_5520_ = v_isSharedCheck_5557_;
goto v_resetjp_5518_;
}
v_resetjp_5518_:
{
lean_object* v_name_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v___x_5528_; lean_object* v___x_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; 
v_name_5521_ = lean_ctor_get(v_toConstantVal_5497_, 0);
v___x_5522_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMinors_loop_spec__0___closed__0));
v___x_5523_ = l_Array_toSubarray___redArg(v___x_5504_, v_lower_5516_, v_upper_5517_);
v___x_5524_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__9));
lean_inc(v_name_5521_);
v___x_5525_ = l_Lean_Name_append(v_name_5521_, v___x_5524_);
v___x_5526_ = l_Lean_mkConst(v___x_5525_, v___x_5316_);
v___x_5527_ = l_Subarray_copy___redArg(v___x_5523_);
lean_inc_ref(v___x_5312_);
v___x_5528_ = l_Array_append___redArg(v___x_5312_, v___x_5527_);
lean_dec_ref(v___x_5527_);
v___x_5529_ = l_Array_append___redArg(v___x_5528_, v_localInsts_5319_);
v___x_5530_ = l_Lean_mkAppN(v___x_5526_, v___x_5529_);
lean_dec_ref(v___x_5529_);
v___x_5531_ = l_Lean_mkConst(v___x_5522_, v___x_5509_);
v___x_5532_ = l_Lean_mkApp3(v___x_5531_, v_a_5496_, v___x_5530_, v___x_5303_);
lean_inc(v_a_5515_);
lean_inc_ref(v___x_5532_);
v___x_5533_ = l_Lean_Meta_mkEq(v___x_5532_, v_a_5515_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_);
if (lean_obj_tag(v___x_5533_) == 0)
{
lean_object* v_a_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; lean_object* v_a_5537_; uint8_t v___x_5538_; 
v_a_5534_ = lean_ctor_get(v___x_5533_, 0);
lean_inc(v_a_5534_);
lean_dec_ref(v___x_5533_);
v___x_5535_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__2));
v___x_5536_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__0___redArg(v___x_5535_, v___y_5322_);
v_a_5537_ = lean_ctor_get(v___x_5536_, 0);
lean_inc(v_a_5537_);
lean_dec_ref(v___x_5536_);
v___x_5538_ = lean_unbox(v_a_5537_);
lean_dec(v_a_5537_);
if (v___x_5538_ == 0)
{
lean_del_object(v___x_5519_);
lean_dec(v_name_5317_);
v___y_5464_ = v_a_5515_;
v___y_5465_ = v_a_5534_;
v___y_5466_ = v___x_5532_;
v___y_5467_ = v___x_5535_;
v___y_5468_ = v___y_5320_;
v___y_5469_ = v___y_5321_;
v___y_5470_ = v___y_5322_;
v___y_5471_ = v___y_5323_;
goto v___jp_5463_;
}
else
{
lean_object* v___x_5539_; lean_object* v___x_5540_; lean_object* v___x_5542_; 
v___x_5539_ = lean_obj_once(&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__11, &l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__11_once, _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__11);
v___x_5540_ = l_Lean_MessageData_ofName(v_name_5317_);
if (v_isShared_5520_ == 0)
{
lean_ctor_set_tag(v___x_5519_, 7);
lean_ctor_set(v___x_5519_, 1, v___x_5540_);
lean_ctor_set(v___x_5519_, 0, v___x_5539_);
v___x_5542_ = v___x_5519_;
goto v_reusejp_5541_;
}
else
{
lean_object* v_reuseFailAlloc_5548_; 
v_reuseFailAlloc_5548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5548_, 0, v___x_5539_);
lean_ctor_set(v_reuseFailAlloc_5548_, 1, v___x_5540_);
v___x_5542_ = v_reuseFailAlloc_5548_;
goto v_reusejp_5541_;
}
v_reusejp_5541_:
{
lean_object* v___x_5543_; lean_object* v___x_5544_; lean_object* v___x_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; 
v___x_5543_ = lean_obj_once(&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__13, &l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__13_once, _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__13);
v___x_5544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5544_, 0, v___x_5542_);
lean_ctor_set(v___x_5544_, 1, v___x_5543_);
lean_inc(v_a_5534_);
v___x_5545_ = l_Lean_MessageData_ofExpr(v_a_5534_);
v___x_5546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5546_, 0, v___x_5544_);
lean_ctor_set(v___x_5546_, 1, v___x_5545_);
v___x_5547_ = l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1(v___x_5535_, v___x_5546_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_);
if (lean_obj_tag(v___x_5547_) == 0)
{
lean_dec_ref(v___x_5547_);
v___y_5464_ = v_a_5515_;
v___y_5465_ = v_a_5534_;
v___y_5466_ = v___x_5532_;
v___y_5467_ = v___x_5535_;
v___y_5468_ = v___y_5320_;
v___y_5469_ = v___y_5321_;
v___y_5470_ = v___y_5322_;
v___y_5471_ = v___y_5323_;
goto v___jp_5463_;
}
else
{
lean_dec(v_a_5534_);
lean_dec_ref(v___x_5532_);
lean_dec(v_a_5515_);
lean_dec_ref(v_localInsts_5319_);
lean_dec_ref(v___x_5314_);
lean_dec(v_recMap_5313_);
lean_dec_ref(v___x_5312_);
lean_dec(v_ctorName_5311_);
lean_dec_ref(v_sizeOfFns_5310_);
lean_dec(v___x_5309_);
lean_dec_ref(v_a_5308_);
lean_dec_ref(v_a_5307_);
lean_dec(v_levelParams_5305_);
lean_dec_ref(v_indInfo_5304_);
return v___x_5547_;
}
}
}
}
else
{
lean_object* v_a_5549_; lean_object* v___x_5551_; uint8_t v_isShared_5552_; uint8_t v_isSharedCheck_5556_; 
lean_dec_ref(v___x_5532_);
lean_del_object(v___x_5519_);
lean_dec(v_a_5515_);
lean_dec_ref(v_localInsts_5319_);
lean_dec(v_name_5317_);
lean_dec_ref(v___x_5314_);
lean_dec(v_recMap_5313_);
lean_dec_ref(v___x_5312_);
lean_dec(v_ctorName_5311_);
lean_dec_ref(v_sizeOfFns_5310_);
lean_dec(v___x_5309_);
lean_dec_ref(v_a_5308_);
lean_dec_ref(v_a_5307_);
lean_dec(v_levelParams_5305_);
lean_dec_ref(v_indInfo_5304_);
v_a_5549_ = lean_ctor_get(v___x_5533_, 0);
v_isSharedCheck_5556_ = !lean_is_exclusive(v___x_5533_);
if (v_isSharedCheck_5556_ == 0)
{
v___x_5551_ = v___x_5533_;
v_isShared_5552_ = v_isSharedCheck_5556_;
goto v_resetjp_5550_;
}
else
{
lean_inc(v_a_5549_);
lean_dec(v___x_5533_);
v___x_5551_ = lean_box(0);
v_isShared_5552_ = v_isSharedCheck_5556_;
goto v_resetjp_5550_;
}
v_resetjp_5550_:
{
lean_object* v___x_5554_; 
if (v_isShared_5552_ == 0)
{
v___x_5554_ = v___x_5551_;
goto v_reusejp_5553_;
}
else
{
lean_object* v_reuseFailAlloc_5555_; 
v_reuseFailAlloc_5555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5555_, 0, v_a_5549_);
v___x_5554_ = v_reuseFailAlloc_5555_;
goto v_reusejp_5553_;
}
v_reusejp_5553_:
{
return v___x_5554_;
}
}
}
}
}
else
{
lean_object* v_a_5558_; lean_object* v___x_5560_; uint8_t v_isShared_5561_; uint8_t v_isSharedCheck_5565_; 
lean_dec_ref(v___x_5509_);
lean_dec_ref(v___y_5506_);
lean_dec_ref(v___x_5504_);
lean_dec(v_a_5496_);
lean_dec_ref(v_localInsts_5319_);
lean_dec(v_name_5317_);
lean_dec(v___x_5316_);
lean_dec_ref(v___x_5314_);
lean_dec(v_recMap_5313_);
lean_dec_ref(v___x_5312_);
lean_dec(v_ctorName_5311_);
lean_dec_ref(v_sizeOfFns_5310_);
lean_dec(v___x_5309_);
lean_dec_ref(v_a_5308_);
lean_dec_ref(v_a_5307_);
lean_dec(v_levelParams_5305_);
lean_dec_ref(v_indInfo_5304_);
lean_dec_ref(v___x_5303_);
v_a_5558_ = lean_ctor_get(v___x_5514_, 0);
v_isSharedCheck_5565_ = !lean_is_exclusive(v___x_5514_);
if (v_isSharedCheck_5565_ == 0)
{
v___x_5560_ = v___x_5514_;
v_isShared_5561_ = v_isSharedCheck_5565_;
goto v_resetjp_5559_;
}
else
{
lean_inc(v_a_5558_);
lean_dec(v___x_5514_);
v___x_5560_ = lean_box(0);
v_isShared_5561_ = v_isSharedCheck_5565_;
goto v_resetjp_5559_;
}
v_resetjp_5559_:
{
lean_object* v___x_5563_; 
if (v_isShared_5561_ == 0)
{
v___x_5563_ = v___x_5560_;
goto v_reusejp_5562_;
}
else
{
lean_object* v_reuseFailAlloc_5564_; 
v_reuseFailAlloc_5564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5564_, 0, v_a_5558_);
v___x_5563_ = v_reuseFailAlloc_5564_;
goto v_reusejp_5562_;
}
v_reusejp_5562_:
{
return v___x_5563_;
}
}
}
}
else
{
lean_object* v_a_5566_; lean_object* v___x_5568_; uint8_t v_isShared_5569_; uint8_t v_isSharedCheck_5573_; 
lean_dec_ref(v___x_5509_);
lean_dec_ref(v___y_5506_);
lean_dec_ref(v___x_5504_);
lean_dec(v_a_5496_);
lean_dec_ref(v_localInsts_5319_);
lean_dec(v_name_5317_);
lean_dec(v___x_5316_);
lean_dec_ref(v___x_5314_);
lean_dec(v_recMap_5313_);
lean_dec_ref(v___x_5312_);
lean_dec(v_ctorName_5311_);
lean_dec_ref(v_sizeOfFns_5310_);
lean_dec(v___x_5309_);
lean_dec_ref(v_a_5308_);
lean_dec_ref(v_a_5307_);
lean_dec(v_levelParams_5305_);
lean_dec_ref(v_indInfo_5304_);
lean_dec_ref(v___x_5303_);
v_a_5566_ = lean_ctor_get(v___x_5512_, 0);
v_isSharedCheck_5573_ = !lean_is_exclusive(v___x_5512_);
if (v_isSharedCheck_5573_ == 0)
{
v___x_5568_ = v___x_5512_;
v_isShared_5569_ = v_isSharedCheck_5573_;
goto v_resetjp_5567_;
}
else
{
lean_inc(v_a_5566_);
lean_dec(v___x_5512_);
v___x_5568_ = lean_box(0);
v_isShared_5569_ = v_isSharedCheck_5573_;
goto v_resetjp_5567_;
}
v_resetjp_5567_:
{
lean_object* v___x_5571_; 
if (v_isShared_5569_ == 0)
{
v___x_5571_ = v___x_5568_;
goto v_reusejp_5570_;
}
else
{
lean_object* v_reuseFailAlloc_5572_; 
v_reuseFailAlloc_5572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5572_, 0, v_a_5566_);
v___x_5571_ = v_reuseFailAlloc_5572_;
goto v_reusejp_5570_;
}
v_reusejp_5570_:
{
return v___x_5571_;
}
}
}
}
else
{
lean_object* v_a_5574_; lean_object* v___x_5576_; uint8_t v_isShared_5577_; uint8_t v_isSharedCheck_5581_; 
lean_dec_ref(v___y_5506_);
lean_dec_ref(v___x_5504_);
lean_dec(v_a_5496_);
lean_dec_ref(v_localInsts_5319_);
lean_dec(v_name_5317_);
lean_dec(v___x_5316_);
lean_dec(v___x_5315_);
lean_dec_ref(v___x_5314_);
lean_dec(v_recMap_5313_);
lean_dec_ref(v___x_5312_);
lean_dec(v_ctorName_5311_);
lean_dec_ref(v_sizeOfFns_5310_);
lean_dec(v___x_5309_);
lean_dec_ref(v_a_5308_);
lean_dec_ref(v_a_5307_);
lean_dec(v_levelParams_5305_);
lean_dec_ref(v_indInfo_5304_);
lean_dec_ref(v___x_5303_);
v_a_5574_ = lean_ctor_get(v___x_5507_, 0);
v_isSharedCheck_5581_ = !lean_is_exclusive(v___x_5507_);
if (v_isSharedCheck_5581_ == 0)
{
v___x_5576_ = v___x_5507_;
v_isShared_5577_ = v_isSharedCheck_5581_;
goto v_resetjp_5575_;
}
else
{
lean_inc(v_a_5574_);
lean_dec(v___x_5507_);
v___x_5576_ = lean_box(0);
v_isShared_5577_ = v_isSharedCheck_5581_;
goto v_resetjp_5575_;
}
v_resetjp_5575_:
{
lean_object* v___x_5579_; 
if (v_isShared_5577_ == 0)
{
v___x_5579_ = v___x_5576_;
goto v_reusejp_5578_;
}
else
{
lean_object* v_reuseFailAlloc_5580_; 
v_reuseFailAlloc_5580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5580_, 0, v_a_5574_);
v___x_5579_ = v_reuseFailAlloc_5580_;
goto v_reusejp_5578_;
}
v_reusejp_5578_:
{
return v___x_5579_;
}
}
}
}
}
else
{
lean_object* v_a_5586_; lean_object* v___x_5588_; uint8_t v_isShared_5589_; uint8_t v_isSharedCheck_5593_; 
lean_dec_ref(v_localInsts_5319_);
lean_dec(v___x_5318_);
lean_dec(v_name_5317_);
lean_dec(v___x_5316_);
lean_dec(v___x_5315_);
lean_dec_ref(v___x_5314_);
lean_dec(v_recMap_5313_);
lean_dec_ref(v___x_5312_);
lean_dec(v_ctorName_5311_);
lean_dec_ref(v_sizeOfFns_5310_);
lean_dec(v___x_5309_);
lean_dec_ref(v_a_5308_);
lean_dec_ref(v_a_5307_);
lean_dec(v_levelParams_5305_);
lean_dec_ref(v_indInfo_5304_);
lean_dec_ref(v___x_5303_);
v_a_5586_ = lean_ctor_get(v___x_5495_, 0);
v_isSharedCheck_5593_ = !lean_is_exclusive(v___x_5495_);
if (v_isSharedCheck_5593_ == 0)
{
v___x_5588_ = v___x_5495_;
v_isShared_5589_ = v_isSharedCheck_5593_;
goto v_resetjp_5587_;
}
else
{
lean_inc(v_a_5586_);
lean_dec(v___x_5495_);
v___x_5588_ = lean_box(0);
v_isShared_5589_ = v_isSharedCheck_5593_;
goto v_resetjp_5587_;
}
v_resetjp_5587_:
{
lean_object* v___x_5591_; 
if (v_isShared_5589_ == 0)
{
v___x_5591_ = v___x_5588_;
goto v_reusejp_5590_;
}
else
{
lean_object* v_reuseFailAlloc_5592_; 
v_reuseFailAlloc_5592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5592_, 0, v_a_5586_);
v___x_5591_ = v_reuseFailAlloc_5592_;
goto v_reusejp_5590_;
}
v_reusejp_5590_:
{
return v___x_5591_;
}
}
}
v___jp_5325_:
{
lean_object* v___x_5333_; lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; 
lean_inc(v___y_5328_);
v___x_5333_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5333_, 0, v___y_5328_);
lean_ctor_set(v___x_5333_, 1, v_levelParams_5305_);
lean_ctor_set(v___x_5333_, 2, v___y_5326_);
v___x_5334_ = lean_box(0);
lean_inc(v___y_5328_);
v___x_5335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5335_, 0, v___y_5328_);
lean_ctor_set(v___x_5335_, 1, v___x_5334_);
v___x_5336_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5336_, 0, v___x_5333_);
lean_ctor_set(v___x_5336_, 1, v___y_5327_);
lean_ctor_set(v___x_5336_, 2, v___x_5335_);
v___x_5337_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_5337_, 0, v___x_5336_);
v___x_5338_ = l_Lean_addDecl(v___x_5337_, v___x_5306_, v___y_5331_, v___y_5332_);
if (lean_obj_tag(v___x_5338_) == 0)
{
lean_object* v___x_5339_; 
lean_dec_ref(v___x_5338_);
lean_inc(v___y_5328_);
v___x_5339_ = l_Lean_inferDefEqAttr(v___y_5328_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_);
if (lean_obj_tag(v___x_5339_) == 0)
{
lean_object* v_add_5340_; lean_object* v___x_5341_; uint8_t v___x_5342_; lean_object* v___x_5343_; lean_object* v___x_5344_; 
lean_dec_ref(v___x_5339_);
v_add_5340_ = lean_ctor_get(v_a_5307_, 1);
lean_inc_ref(v_add_5340_);
lean_dec_ref(v_a_5307_);
v___x_5341_ = lean_box(0);
v___x_5342_ = 0;
v___x_5343_ = lean_box(v___x_5342_);
lean_inc(v___y_5332_);
lean_inc_ref(v___y_5331_);
lean_inc(v___y_5328_);
v___x_5344_ = lean_apply_6(v_add_5340_, v___y_5328_, v___x_5341_, v___x_5343_, v___y_5331_, v___y_5332_, lean_box(0));
if (lean_obj_tag(v___x_5344_) == 0)
{
lean_object* v_add_5345_; lean_object* v___x_5346_; lean_object* v___x_5347_; 
lean_dec_ref(v___x_5344_);
v_add_5345_ = lean_ctor_get(v_a_5308_, 1);
lean_inc_ref(v_add_5345_);
lean_dec_ref(v_a_5308_);
v___x_5346_ = lean_box(v___x_5342_);
lean_inc(v___y_5332_);
lean_inc_ref(v___y_5331_);
v___x_5347_ = lean_apply_6(v_add_5345_, v___y_5328_, v___x_5309_, v___x_5346_, v___y_5331_, v___y_5332_, lean_box(0));
return v___x_5347_;
}
else
{
lean_dec(v___y_5328_);
lean_dec(v___x_5309_);
lean_dec_ref(v_a_5308_);
return v___x_5344_;
}
}
else
{
lean_dec(v___y_5328_);
lean_dec(v___x_5309_);
lean_dec_ref(v_a_5308_);
lean_dec_ref(v_a_5307_);
return v___x_5339_;
}
}
else
{
lean_dec(v___y_5328_);
lean_dec(v___x_5309_);
lean_dec_ref(v_a_5308_);
lean_dec_ref(v_a_5307_);
return v___x_5338_;
}
}
v___jp_5348_:
{
lean_object* v___x_5356_; 
lean_inc(v___y_5355_);
lean_inc_ref(v___y_5354_);
lean_inc(v___y_5353_);
lean_inc_ref(v___y_5352_);
lean_inc_ref(v___y_5350_);
v___x_5356_ = lean_infer_type(v___y_5350_, v___y_5352_, v___y_5353_, v___y_5354_, v___y_5355_);
if (lean_obj_tag(v___x_5356_) == 0)
{
lean_object* v_a_5357_; lean_object* v___x_5358_; 
v_a_5357_ = lean_ctor_get(v___x_5356_, 0);
lean_inc(v_a_5357_);
lean_dec_ref(v___x_5356_);
lean_inc_ref(v___y_5349_);
v___x_5358_ = l_Lean_Meta_isExprDefEq(v_a_5357_, v___y_5349_, v___y_5352_, v___y_5353_, v___y_5354_, v___y_5355_);
if (lean_obj_tag(v___x_5358_) == 0)
{
lean_object* v_a_5359_; uint8_t v___x_5360_; 
v_a_5359_ = lean_ctor_get(v___x_5358_, 0);
lean_inc(v_a_5359_);
lean_dec_ref(v___x_5358_);
v___x_5360_ = lean_unbox(v_a_5359_);
lean_dec(v_a_5359_);
if (v___x_5360_ == 0)
{
lean_object* v___x_5361_; lean_object* v___x_5362_; 
lean_dec(v___y_5351_);
lean_dec_ref(v___y_5350_);
lean_dec_ref(v___y_5349_);
lean_dec(v___x_5309_);
lean_dec_ref(v_a_5308_);
lean_dec_ref(v_a_5307_);
lean_dec(v_levelParams_5305_);
v___x_5361_ = lean_obj_once(&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__1, &l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__1_once, _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__1);
v___x_5362_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__0___redArg(v___x_5361_, v___y_5352_, v___y_5353_, v___y_5354_, v___y_5355_);
return v___x_5362_;
}
else
{
v___y_5326_ = v___y_5349_;
v___y_5327_ = v___y_5350_;
v___y_5328_ = v___y_5351_;
v___y_5329_ = v___y_5352_;
v___y_5330_ = v___y_5353_;
v___y_5331_ = v___y_5354_;
v___y_5332_ = v___y_5355_;
goto v___jp_5325_;
}
}
else
{
lean_object* v_a_5363_; lean_object* v___x_5365_; uint8_t v_isShared_5366_; uint8_t v_isSharedCheck_5370_; 
lean_dec(v___y_5351_);
lean_dec_ref(v___y_5350_);
lean_dec_ref(v___y_5349_);
lean_dec(v___x_5309_);
lean_dec_ref(v_a_5308_);
lean_dec_ref(v_a_5307_);
lean_dec(v_levelParams_5305_);
v_a_5363_ = lean_ctor_get(v___x_5358_, 0);
v_isSharedCheck_5370_ = !lean_is_exclusive(v___x_5358_);
if (v_isSharedCheck_5370_ == 0)
{
v___x_5365_ = v___x_5358_;
v_isShared_5366_ = v_isSharedCheck_5370_;
goto v_resetjp_5364_;
}
else
{
lean_inc(v_a_5363_);
lean_dec(v___x_5358_);
v___x_5365_ = lean_box(0);
v_isShared_5366_ = v_isSharedCheck_5370_;
goto v_resetjp_5364_;
}
v_resetjp_5364_:
{
lean_object* v___x_5368_; 
if (v_isShared_5366_ == 0)
{
v___x_5368_ = v___x_5365_;
goto v_reusejp_5367_;
}
else
{
lean_object* v_reuseFailAlloc_5369_; 
v_reuseFailAlloc_5369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5369_, 0, v_a_5363_);
v___x_5368_ = v_reuseFailAlloc_5369_;
goto v_reusejp_5367_;
}
v_reusejp_5367_:
{
return v___x_5368_;
}
}
}
}
else
{
lean_object* v_a_5371_; lean_object* v___x_5373_; uint8_t v_isShared_5374_; uint8_t v_isSharedCheck_5378_; 
lean_dec(v___y_5351_);
lean_dec_ref(v___y_5350_);
lean_dec_ref(v___y_5349_);
lean_dec(v___x_5309_);
lean_dec_ref(v_a_5308_);
lean_dec_ref(v_a_5307_);
lean_dec(v_levelParams_5305_);
v_a_5371_ = lean_ctor_get(v___x_5356_, 0);
v_isSharedCheck_5378_ = !lean_is_exclusive(v___x_5356_);
if (v_isSharedCheck_5378_ == 0)
{
v___x_5373_ = v___x_5356_;
v_isShared_5374_ = v_isSharedCheck_5378_;
goto v_resetjp_5372_;
}
else
{
lean_inc(v_a_5371_);
lean_dec(v___x_5356_);
v___x_5373_ = lean_box(0);
v_isShared_5374_ = v_isSharedCheck_5378_;
goto v_resetjp_5372_;
}
v_resetjp_5372_:
{
lean_object* v___x_5376_; 
if (v_isShared_5374_ == 0)
{
v___x_5376_ = v___x_5373_;
goto v_reusejp_5375_;
}
else
{
lean_object* v_reuseFailAlloc_5377_; 
v_reuseFailAlloc_5377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5377_, 0, v_a_5371_);
v___x_5376_ = v_reuseFailAlloc_5377_;
goto v_reusejp_5375_;
}
v_reusejp_5375_:
{
return v___x_5376_;
}
}
}
}
v___jp_5379_:
{
lean_object* v___x_5391_; 
v___x_5391_ = l_Lean_Meta_mkLambdaFVars(v___y_5382_, v_thmValue_5386_, v___x_5306_, v___y_5380_, v___x_5306_, v___y_5380_, v___y_5381_, v___y_5387_, v___y_5388_, v___y_5389_, v___y_5390_);
lean_dec_ref(v___y_5382_);
if (lean_obj_tag(v___x_5391_) == 0)
{
lean_object* v_a_5392_; lean_object* v___x_5393_; lean_object* v_a_5394_; uint8_t v___x_5395_; 
v_a_5392_ = lean_ctor_get(v___x_5391_, 0);
lean_inc(v_a_5392_);
lean_dec_ref(v___x_5391_);
lean_inc(v___y_5385_);
v___x_5393_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__0___redArg(v___y_5385_, v___y_5389_);
v_a_5394_ = lean_ctor_get(v___x_5393_, 0);
lean_inc(v_a_5394_);
lean_dec_ref(v___x_5393_);
v___x_5395_ = lean_unbox(v_a_5394_);
lean_dec(v_a_5394_);
if (v___x_5395_ == 0)
{
lean_dec(v___y_5385_);
v___y_5349_ = v___y_5383_;
v___y_5350_ = v_a_5392_;
v___y_5351_ = v___y_5384_;
v___y_5352_ = v___y_5387_;
v___y_5353_ = v___y_5388_;
v___y_5354_ = v___y_5389_;
v___y_5355_ = v___y_5390_;
goto v___jp_5348_;
}
else
{
lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; 
v___x_5396_ = lean_obj_once(&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__3, &l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__3_once, _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__3);
lean_inc(v_a_5392_);
v___x_5397_ = l_Lean_MessageData_ofExpr(v_a_5392_);
v___x_5398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5398_, 0, v___x_5396_);
lean_ctor_set(v___x_5398_, 1, v___x_5397_);
v___x_5399_ = l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1(v___y_5385_, v___x_5398_, v___y_5387_, v___y_5388_, v___y_5389_, v___y_5390_);
if (lean_obj_tag(v___x_5399_) == 0)
{
lean_dec_ref(v___x_5399_);
v___y_5349_ = v___y_5383_;
v___y_5350_ = v_a_5392_;
v___y_5351_ = v___y_5384_;
v___y_5352_ = v___y_5387_;
v___y_5353_ = v___y_5388_;
v___y_5354_ = v___y_5389_;
v___y_5355_ = v___y_5390_;
goto v___jp_5348_;
}
else
{
lean_dec(v_a_5392_);
lean_dec(v___y_5384_);
lean_dec_ref(v___y_5383_);
lean_dec(v___x_5309_);
lean_dec_ref(v_a_5308_);
lean_dec_ref(v_a_5307_);
lean_dec(v_levelParams_5305_);
return v___x_5399_;
}
}
}
else
{
lean_object* v_a_5400_; lean_object* v___x_5402_; uint8_t v_isShared_5403_; uint8_t v_isSharedCheck_5407_; 
lean_dec(v___y_5385_);
lean_dec(v___y_5384_);
lean_dec_ref(v___y_5383_);
lean_dec(v___x_5309_);
lean_dec_ref(v_a_5308_);
lean_dec_ref(v_a_5307_);
lean_dec(v_levelParams_5305_);
v_a_5400_ = lean_ctor_get(v___x_5391_, 0);
v_isSharedCheck_5407_ = !lean_is_exclusive(v___x_5391_);
if (v_isSharedCheck_5407_ == 0)
{
v___x_5402_ = v___x_5391_;
v_isShared_5403_ = v_isSharedCheck_5407_;
goto v_resetjp_5401_;
}
else
{
lean_inc(v_a_5400_);
lean_dec(v___x_5391_);
v___x_5402_ = lean_box(0);
v_isShared_5403_ = v_isSharedCheck_5407_;
goto v_resetjp_5401_;
}
v_resetjp_5401_:
{
lean_object* v___x_5405_; 
if (v_isShared_5403_ == 0)
{
v___x_5405_ = v___x_5402_;
goto v_reusejp_5404_;
}
else
{
lean_object* v_reuseFailAlloc_5406_; 
v_reuseFailAlloc_5406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5406_, 0, v_a_5400_);
v___x_5405_ = v_reuseFailAlloc_5406_;
goto v_reusejp_5404_;
}
v_reusejp_5404_:
{
return v___x_5405_;
}
}
}
}
v___jp_5408_:
{
uint8_t v___x_5421_; 
v___x_5421_ = l_Lean_InductiveVal_isNested(v_indInfo_5304_);
if (v___x_5421_ == 0)
{
lean_object* v___x_5422_; 
lean_dec_ref(v___y_5415_);
lean_dec_ref(v_localInsts_5319_);
lean_dec(v_recMap_5313_);
lean_dec_ref(v___x_5312_);
lean_dec(v_ctorName_5311_);
lean_dec_ref(v_sizeOfFns_5310_);
lean_dec_ref(v_indInfo_5304_);
v___x_5422_ = l_Lean_Meta_mkEqRefl(v___y_5413_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_);
if (lean_obj_tag(v___x_5422_) == 0)
{
lean_object* v_a_5423_; 
v_a_5423_ = lean_ctor_get(v___x_5422_, 0);
lean_inc(v_a_5423_);
lean_dec_ref(v___x_5422_);
v___y_5380_ = v___y_5409_;
v___y_5381_ = v___y_5411_;
v___y_5382_ = v___y_5410_;
v___y_5383_ = v___y_5412_;
v___y_5384_ = v___y_5414_;
v___y_5385_ = v___y_5416_;
v_thmValue_5386_ = v_a_5423_;
v___y_5387_ = v___y_5417_;
v___y_5388_ = v___y_5418_;
v___y_5389_ = v___y_5419_;
v___y_5390_ = v___y_5420_;
goto v___jp_5379_;
}
else
{
lean_object* v_a_5424_; lean_object* v___x_5426_; uint8_t v_isShared_5427_; uint8_t v_isSharedCheck_5431_; 
lean_dec(v___y_5416_);
lean_dec(v___y_5414_);
lean_dec_ref(v___y_5412_);
lean_dec_ref(v___y_5410_);
lean_dec(v___x_5309_);
lean_dec_ref(v_a_5308_);
lean_dec_ref(v_a_5307_);
lean_dec(v_levelParams_5305_);
v_a_5424_ = lean_ctor_get(v___x_5422_, 0);
v_isSharedCheck_5431_ = !lean_is_exclusive(v___x_5422_);
if (v_isSharedCheck_5431_ == 0)
{
v___x_5426_ = v___x_5422_;
v_isShared_5427_ = v_isSharedCheck_5431_;
goto v_resetjp_5425_;
}
else
{
lean_inc(v_a_5424_);
lean_dec(v___x_5422_);
v___x_5426_ = lean_box(0);
v_isShared_5427_ = v_isSharedCheck_5431_;
goto v_resetjp_5425_;
}
v_resetjp_5425_:
{
lean_object* v___x_5429_; 
if (v_isShared_5427_ == 0)
{
v___x_5429_ = v___x_5426_;
goto v_reusejp_5428_;
}
else
{
lean_object* v_reuseFailAlloc_5430_; 
v_reuseFailAlloc_5430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5430_, 0, v_a_5424_);
v___x_5429_ = v_reuseFailAlloc_5430_;
goto v_reusejp_5428_;
}
v_reusejp_5428_:
{
return v___x_5429_;
}
}
}
}
else
{
lean_object* v___x_5432_; lean_object* v___x_5433_; 
v___x_5432_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5432_, 0, v_indInfo_5304_);
lean_ctor_set(v___x_5432_, 1, v_sizeOfFns_5310_);
lean_ctor_set(v___x_5432_, 2, v_ctorName_5311_);
lean_ctor_set(v___x_5432_, 3, v___x_5312_);
lean_ctor_set(v___x_5432_, 4, v_localInsts_5319_);
lean_ctor_set(v___x_5432_, 5, v_recMap_5313_);
v___x_5433_ = l_Lean_Meta_SizeOfSpecNested_main(v___y_5415_, v___y_5413_, v___x_5432_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_);
lean_dec_ref(v___x_5432_);
if (lean_obj_tag(v___x_5433_) == 0)
{
lean_object* v_a_5434_; 
v_a_5434_ = lean_ctor_get(v___x_5433_, 0);
lean_inc(v_a_5434_);
lean_dec_ref(v___x_5433_);
v___y_5380_ = v___y_5409_;
v___y_5381_ = v___y_5411_;
v___y_5382_ = v___y_5410_;
v___y_5383_ = v___y_5412_;
v___y_5384_ = v___y_5414_;
v___y_5385_ = v___y_5416_;
v_thmValue_5386_ = v_a_5434_;
v___y_5387_ = v___y_5417_;
v___y_5388_ = v___y_5418_;
v___y_5389_ = v___y_5419_;
v___y_5390_ = v___y_5420_;
goto v___jp_5379_;
}
else
{
lean_object* v_a_5435_; lean_object* v___x_5437_; uint8_t v_isShared_5438_; uint8_t v_isSharedCheck_5442_; 
lean_dec(v___y_5416_);
lean_dec(v___y_5414_);
lean_dec_ref(v___y_5412_);
lean_dec_ref(v___y_5410_);
lean_dec(v___x_5309_);
lean_dec_ref(v_a_5308_);
lean_dec_ref(v_a_5307_);
lean_dec(v_levelParams_5305_);
v_a_5435_ = lean_ctor_get(v___x_5433_, 0);
v_isSharedCheck_5442_ = !lean_is_exclusive(v___x_5433_);
if (v_isSharedCheck_5442_ == 0)
{
v___x_5437_ = v___x_5433_;
v_isShared_5438_ = v_isSharedCheck_5442_;
goto v_resetjp_5436_;
}
else
{
lean_inc(v_a_5435_);
lean_dec(v___x_5433_);
v___x_5437_ = lean_box(0);
v_isShared_5438_ = v_isSharedCheck_5442_;
goto v_resetjp_5436_;
}
v_resetjp_5436_:
{
lean_object* v___x_5440_; 
if (v_isShared_5438_ == 0)
{
v___x_5440_ = v___x_5437_;
goto v_reusejp_5439_;
}
else
{
lean_object* v_reuseFailAlloc_5441_; 
v_reuseFailAlloc_5441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5441_, 0, v_a_5435_);
v___x_5440_ = v_reuseFailAlloc_5441_;
goto v_reusejp_5439_;
}
v_reusejp_5439_:
{
return v___x_5440_;
}
}
}
}
}
v___jp_5443_:
{
lean_object* v___x_5456_; lean_object* v_a_5457_; uint8_t v___x_5458_; 
lean_inc(v___y_5451_);
v___x_5456_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__0___redArg(v___y_5451_, v___y_5454_);
v_a_5457_ = lean_ctor_get(v___x_5456_, 0);
lean_inc(v_a_5457_);
lean_dec_ref(v___x_5456_);
v___x_5458_ = lean_unbox(v_a_5457_);
lean_dec(v_a_5457_);
if (v___x_5458_ == 0)
{
v___y_5409_ = v___y_5444_;
v___y_5410_ = v___y_5446_;
v___y_5411_ = v___y_5445_;
v___y_5412_ = v___y_5448_;
v___y_5413_ = v___y_5447_;
v___y_5414_ = v___y_5449_;
v___y_5415_ = v___y_5450_;
v___y_5416_ = v___y_5451_;
v___y_5417_ = v___y_5452_;
v___y_5418_ = v___y_5453_;
v___y_5419_ = v___y_5454_;
v___y_5420_ = v___y_5455_;
goto v___jp_5408_;
}
else
{
lean_object* v___x_5459_; lean_object* v___x_5460_; lean_object* v___x_5461_; lean_object* v___x_5462_; 
v___x_5459_ = lean_obj_once(&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__5, &l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__5_once, _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__5);
lean_inc_ref(v___y_5448_);
v___x_5460_ = l_Lean_MessageData_ofExpr(v___y_5448_);
v___x_5461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5461_, 0, v___x_5459_);
lean_ctor_set(v___x_5461_, 1, v___x_5460_);
lean_inc(v___y_5451_);
v___x_5462_ = l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1(v___y_5451_, v___x_5461_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_);
if (lean_obj_tag(v___x_5462_) == 0)
{
lean_dec_ref(v___x_5462_);
v___y_5409_ = v___y_5444_;
v___y_5410_ = v___y_5446_;
v___y_5411_ = v___y_5445_;
v___y_5412_ = v___y_5448_;
v___y_5413_ = v___y_5447_;
v___y_5414_ = v___y_5449_;
v___y_5415_ = v___y_5450_;
v___y_5416_ = v___y_5451_;
v___y_5417_ = v___y_5452_;
v___y_5418_ = v___y_5453_;
v___y_5419_ = v___y_5454_;
v___y_5420_ = v___y_5455_;
goto v___jp_5408_;
}
else
{
lean_dec(v___y_5451_);
lean_dec_ref(v___y_5450_);
lean_dec(v___y_5449_);
lean_dec_ref(v___y_5448_);
lean_dec_ref(v___y_5447_);
lean_dec_ref(v___y_5446_);
lean_dec_ref(v_localInsts_5319_);
lean_dec(v_recMap_5313_);
lean_dec_ref(v___x_5312_);
lean_dec(v_ctorName_5311_);
lean_dec_ref(v_sizeOfFns_5310_);
lean_dec(v___x_5309_);
lean_dec_ref(v_a_5308_);
lean_dec_ref(v_a_5307_);
lean_dec(v_levelParams_5305_);
lean_dec_ref(v_indInfo_5304_);
return v___x_5462_;
}
}
}
v___jp_5463_:
{
lean_object* v___x_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; uint8_t v___x_5475_; uint8_t v___x_5476_; lean_object* v___x_5477_; 
lean_inc_ref(v___x_5312_);
v___x_5472_ = l_Array_append___redArg(v___x_5312_, v_localInsts_5319_);
v___x_5473_ = l_Subarray_copy___redArg(v___x_5314_);
v___x_5474_ = l_Array_append___redArg(v___x_5472_, v___x_5473_);
lean_dec_ref(v___x_5473_);
v___x_5475_ = 1;
v___x_5476_ = 1;
v___x_5477_ = l_Lean_Meta_mkForallFVars(v___x_5474_, v___y_5465_, v___x_5306_, v___x_5475_, v___x_5475_, v___x_5476_, v___y_5468_, v___y_5469_, v___y_5470_, v___y_5471_);
if (lean_obj_tag(v___x_5477_) == 0)
{
lean_object* v_a_5478_; lean_object* v___x_5479_; lean_object* v_a_5480_; lean_object* v___x_5481_; uint8_t v___x_5482_; 
v_a_5478_ = lean_ctor_get(v___x_5477_, 0);
lean_inc(v_a_5478_);
lean_dec_ref(v___x_5477_);
lean_inc(v___y_5467_);
v___x_5479_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__0___redArg(v___y_5467_, v___y_5470_);
v_a_5480_ = lean_ctor_get(v___x_5479_, 0);
lean_inc(v_a_5480_);
lean_dec_ref(v___x_5479_);
lean_inc(v_ctorName_5311_);
v___x_5481_ = l_Lean_Meta_mkSizeOfSpecLemmaName(v_ctorName_5311_);
v___x_5482_ = lean_unbox(v_a_5480_);
lean_dec(v_a_5480_);
if (v___x_5482_ == 0)
{
v___y_5444_ = v___x_5475_;
v___y_5445_ = v___x_5476_;
v___y_5446_ = v___x_5474_;
v___y_5447_ = v___y_5464_;
v___y_5448_ = v_a_5478_;
v___y_5449_ = v___x_5481_;
v___y_5450_ = v___y_5466_;
v___y_5451_ = v___y_5467_;
v___y_5452_ = v___y_5468_;
v___y_5453_ = v___y_5469_;
v___y_5454_ = v___y_5470_;
v___y_5455_ = v___y_5471_;
goto v___jp_5443_;
}
else
{
lean_object* v___x_5483_; lean_object* v___x_5484_; lean_object* v___x_5485_; lean_object* v___x_5486_; 
v___x_5483_ = lean_obj_once(&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__7, &l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__7_once, _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__7);
lean_inc(v___x_5481_);
v___x_5484_ = l_Lean_MessageData_ofName(v___x_5481_);
v___x_5485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5485_, 0, v___x_5483_);
lean_ctor_set(v___x_5485_, 1, v___x_5484_);
lean_inc(v___y_5467_);
v___x_5486_ = l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1(v___y_5467_, v___x_5485_, v___y_5468_, v___y_5469_, v___y_5470_, v___y_5471_);
if (lean_obj_tag(v___x_5486_) == 0)
{
lean_dec_ref(v___x_5486_);
v___y_5444_ = v___x_5475_;
v___y_5445_ = v___x_5476_;
v___y_5446_ = v___x_5474_;
v___y_5447_ = v___y_5464_;
v___y_5448_ = v_a_5478_;
v___y_5449_ = v___x_5481_;
v___y_5450_ = v___y_5466_;
v___y_5451_ = v___y_5467_;
v___y_5452_ = v___y_5468_;
v___y_5453_ = v___y_5469_;
v___y_5454_ = v___y_5470_;
v___y_5455_ = v___y_5471_;
goto v___jp_5443_;
}
else
{
lean_dec(v___x_5481_);
lean_dec(v_a_5478_);
lean_dec_ref(v___x_5474_);
lean_dec(v___y_5467_);
lean_dec_ref(v___y_5466_);
lean_dec_ref(v___y_5464_);
lean_dec_ref(v_localInsts_5319_);
lean_dec(v_recMap_5313_);
lean_dec_ref(v___x_5312_);
lean_dec(v_ctorName_5311_);
lean_dec_ref(v_sizeOfFns_5310_);
lean_dec(v___x_5309_);
lean_dec_ref(v_a_5308_);
lean_dec_ref(v_a_5307_);
lean_dec(v_levelParams_5305_);
lean_dec_ref(v_indInfo_5304_);
return v___x_5486_;
}
}
}
else
{
lean_object* v_a_5487_; lean_object* v___x_5489_; uint8_t v_isShared_5490_; uint8_t v_isSharedCheck_5494_; 
lean_dec_ref(v___x_5474_);
lean_dec(v___y_5467_);
lean_dec_ref(v___y_5466_);
lean_dec_ref(v___y_5464_);
lean_dec_ref(v_localInsts_5319_);
lean_dec(v_recMap_5313_);
lean_dec_ref(v___x_5312_);
lean_dec(v_ctorName_5311_);
lean_dec_ref(v_sizeOfFns_5310_);
lean_dec(v___x_5309_);
lean_dec_ref(v_a_5308_);
lean_dec_ref(v_a_5307_);
lean_dec(v_levelParams_5305_);
lean_dec_ref(v_indInfo_5304_);
v_a_5487_ = lean_ctor_get(v___x_5477_, 0);
v_isSharedCheck_5494_ = !lean_is_exclusive(v___x_5477_);
if (v_isSharedCheck_5494_ == 0)
{
v___x_5489_ = v___x_5477_;
v_isShared_5490_ = v_isSharedCheck_5494_;
goto v_resetjp_5488_;
}
else
{
lean_inc(v_a_5487_);
lean_dec(v___x_5477_);
v___x_5489_ = lean_box(0);
v_isShared_5490_ = v_isSharedCheck_5494_;
goto v_resetjp_5488_;
}
v_resetjp_5488_:
{
lean_object* v___x_5492_; 
if (v_isShared_5490_ == 0)
{
v___x_5492_ = v___x_5489_;
goto v_reusejp_5491_;
}
else
{
lean_object* v_reuseFailAlloc_5493_; 
v_reuseFailAlloc_5493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5493_, 0, v_a_5487_);
v___x_5492_ = v_reuseFailAlloc_5493_;
goto v_reusejp_5491_;
}
v_reusejp_5491_:
{
return v___x_5492_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___boxed(lean_object** _args){
lean_object* v___x_5594_ = _args[0];
lean_object* v_indInfo_5595_ = _args[1];
lean_object* v_levelParams_5596_ = _args[2];
lean_object* v___x_5597_ = _args[3];
lean_object* v_a_5598_ = _args[4];
lean_object* v_a_5599_ = _args[5];
lean_object* v___x_5600_ = _args[6];
lean_object* v_sizeOfFns_5601_ = _args[7];
lean_object* v_ctorName_5602_ = _args[8];
lean_object* v___x_5603_ = _args[9];
lean_object* v_recMap_5604_ = _args[10];
lean_object* v___x_5605_ = _args[11];
lean_object* v___x_5606_ = _args[12];
lean_object* v___x_5607_ = _args[13];
lean_object* v_name_5608_ = _args[14];
lean_object* v___x_5609_ = _args[15];
lean_object* v_localInsts_5610_ = _args[16];
lean_object* v___y_5611_ = _args[17];
lean_object* v___y_5612_ = _args[18];
lean_object* v___y_5613_ = _args[19];
lean_object* v___y_5614_ = _args[20];
lean_object* v___y_5615_ = _args[21];
_start:
{
uint8_t v___x_17777__boxed_5616_; lean_object* v_res_5617_; 
v___x_17777__boxed_5616_ = lean_unbox(v___x_5597_);
v_res_5617_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0(v___x_5594_, v_indInfo_5595_, v_levelParams_5596_, v___x_17777__boxed_5616_, v_a_5598_, v_a_5599_, v___x_5600_, v_sizeOfFns_5601_, v_ctorName_5602_, v___x_5603_, v_recMap_5604_, v___x_5605_, v___x_5606_, v___x_5607_, v_name_5608_, v___x_5609_, v_localInsts_5610_, v___y_5611_, v___y_5612_, v___y_5613_, v___y_5614_);
lean_dec(v___y_5614_);
lean_dec_ref(v___y_5613_);
lean_dec(v___y_5612_);
lean_dec_ref(v___y_5611_);
return v_res_5617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__1(lean_object* v_numParams_5618_, lean_object* v_ctorName_5619_, lean_object* v___x_5620_, lean_object* v_indInfo_5621_, lean_object* v_levelParams_5622_, uint8_t v___x_5623_, lean_object* v_a_5624_, lean_object* v_a_5625_, lean_object* v___x_5626_, lean_object* v_sizeOfFns_5627_, lean_object* v_recMap_5628_, lean_object* v___x_5629_, lean_object* v_name_5630_, lean_object* v_xs_5631_, lean_object* v_x_5632_, lean_object* v___y_5633_, lean_object* v___y_5634_, lean_object* v___y_5635_, lean_object* v___y_5636_){
_start:
{
lean_object* v___x_5638_; lean_object* v___x_5639_; lean_object* v_lower_5641_; lean_object* v_upper_5642_; lean_object* v___x_5650_; uint8_t v___x_5651_; 
v___x_5638_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_5618_);
lean_inc_ref(v_xs_5631_);
v___x_5639_ = l_Array_toSubarray___redArg(v_xs_5631_, v___x_5638_, v_numParams_5618_);
v___x_5650_ = lean_array_get_size(v_xs_5631_);
v___x_5651_ = lean_nat_dec_le(v_numParams_5618_, v___x_5638_);
if (v___x_5651_ == 0)
{
v_lower_5641_ = v_numParams_5618_;
v_upper_5642_ = v___x_5650_;
goto v___jp_5640_;
}
else
{
lean_dec(v_numParams_5618_);
v_lower_5641_ = v___x_5638_;
v_upper_5642_ = v___x_5650_;
goto v___jp_5640_;
}
v___jp_5640_:
{
lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___f_5648_; lean_object* v___x_5649_; 
lean_inc_ref(v_xs_5631_);
v___x_5643_ = l_Array_toSubarray___redArg(v_xs_5631_, v_lower_5641_, v_upper_5642_);
lean_inc(v___x_5620_);
lean_inc(v_ctorName_5619_);
v___x_5644_ = l_Lean_mkConst(v_ctorName_5619_, v___x_5620_);
v___x_5645_ = l_Lean_mkAppN(v___x_5644_, v_xs_5631_);
lean_dec_ref(v_xs_5631_);
v___x_5646_ = l_Subarray_copy___redArg(v___x_5639_);
v___x_5647_ = lean_box(v___x_5623_);
lean_inc_ref(v___x_5646_);
v___f_5648_ = lean_alloc_closure((void*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___boxed), 22, 16);
lean_closure_set(v___f_5648_, 0, v___x_5645_);
lean_closure_set(v___f_5648_, 1, v_indInfo_5621_);
lean_closure_set(v___f_5648_, 2, v_levelParams_5622_);
lean_closure_set(v___f_5648_, 3, v___x_5647_);
lean_closure_set(v___f_5648_, 4, v_a_5624_);
lean_closure_set(v___f_5648_, 5, v_a_5625_);
lean_closure_set(v___f_5648_, 6, v___x_5626_);
lean_closure_set(v___f_5648_, 7, v_sizeOfFns_5627_);
lean_closure_set(v___f_5648_, 8, v_ctorName_5619_);
lean_closure_set(v___f_5648_, 9, v___x_5646_);
lean_closure_set(v___f_5648_, 10, v_recMap_5628_);
lean_closure_set(v___f_5648_, 11, v___x_5643_);
lean_closure_set(v___f_5648_, 12, v___x_5629_);
lean_closure_set(v___f_5648_, 13, v___x_5620_);
lean_closure_set(v___f_5648_, 14, v_name_5630_);
lean_closure_set(v___f_5648_, 15, v___x_5638_);
v___x_5649_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances___redArg(v___x_5646_, v___f_5648_, v___y_5633_, v___y_5634_, v___y_5635_, v___y_5636_);
return v___x_5649_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__1___boxed(lean_object** _args){
lean_object* v_numParams_5652_ = _args[0];
lean_object* v_ctorName_5653_ = _args[1];
lean_object* v___x_5654_ = _args[2];
lean_object* v_indInfo_5655_ = _args[3];
lean_object* v_levelParams_5656_ = _args[4];
lean_object* v___x_5657_ = _args[5];
lean_object* v_a_5658_ = _args[6];
lean_object* v_a_5659_ = _args[7];
lean_object* v___x_5660_ = _args[8];
lean_object* v_sizeOfFns_5661_ = _args[9];
lean_object* v_recMap_5662_ = _args[10];
lean_object* v___x_5663_ = _args[11];
lean_object* v_name_5664_ = _args[12];
lean_object* v_xs_5665_ = _args[13];
lean_object* v_x_5666_ = _args[14];
lean_object* v___y_5667_ = _args[15];
lean_object* v___y_5668_ = _args[16];
lean_object* v___y_5669_ = _args[17];
lean_object* v___y_5670_ = _args[18];
lean_object* v___y_5671_ = _args[19];
_start:
{
uint8_t v___x_18379__boxed_5672_; lean_object* v_res_5673_; 
v___x_18379__boxed_5672_ = lean_unbox(v___x_5657_);
v_res_5673_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__1(v_numParams_5652_, v_ctorName_5653_, v___x_5654_, v_indInfo_5655_, v_levelParams_5656_, v___x_18379__boxed_5672_, v_a_5658_, v_a_5659_, v___x_5660_, v_sizeOfFns_5661_, v_recMap_5662_, v___x_5663_, v_name_5664_, v_xs_5665_, v_x_5666_, v___y_5667_, v___y_5668_, v___y_5669_, v___y_5670_);
lean_dec(v___y_5670_);
lean_dec_ref(v___y_5669_);
lean_dec(v___y_5668_);
lean_dec_ref(v___y_5667_);
lean_dec_ref(v_x_5666_);
return v_res_5673_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__0_spec__0(lean_object* v_msg_5674_, lean_object* v___y_5675_, lean_object* v___y_5676_, lean_object* v___y_5677_, lean_object* v___y_5678_){
_start:
{
lean_object* v___x_5680_; lean_object* v___x_5681_; lean_object* v_toApplicative_5682_; lean_object* v___x_5684_; uint8_t v_isShared_5685_; uint8_t v_isSharedCheck_5743_; 
v___x_5680_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__0);
v___x_5681_ = l_StateRefT_x27_instMonad___redArg(v___x_5680_);
v_toApplicative_5682_ = lean_ctor_get(v___x_5681_, 0);
v_isSharedCheck_5743_ = !lean_is_exclusive(v___x_5681_);
if (v_isSharedCheck_5743_ == 0)
{
lean_object* v_unused_5744_; 
v_unused_5744_ = lean_ctor_get(v___x_5681_, 1);
lean_dec(v_unused_5744_);
v___x_5684_ = v___x_5681_;
v_isShared_5685_ = v_isSharedCheck_5743_;
goto v_resetjp_5683_;
}
else
{
lean_inc(v_toApplicative_5682_);
lean_dec(v___x_5681_);
v___x_5684_ = lean_box(0);
v_isShared_5685_ = v_isSharedCheck_5743_;
goto v_resetjp_5683_;
}
v_resetjp_5683_:
{
lean_object* v_toFunctor_5686_; lean_object* v_toSeq_5687_; lean_object* v_toSeqLeft_5688_; lean_object* v_toSeqRight_5689_; lean_object* v___x_5691_; uint8_t v_isShared_5692_; uint8_t v_isSharedCheck_5741_; 
v_toFunctor_5686_ = lean_ctor_get(v_toApplicative_5682_, 0);
v_toSeq_5687_ = lean_ctor_get(v_toApplicative_5682_, 2);
v_toSeqLeft_5688_ = lean_ctor_get(v_toApplicative_5682_, 3);
v_toSeqRight_5689_ = lean_ctor_get(v_toApplicative_5682_, 4);
v_isSharedCheck_5741_ = !lean_is_exclusive(v_toApplicative_5682_);
if (v_isSharedCheck_5741_ == 0)
{
lean_object* v_unused_5742_; 
v_unused_5742_ = lean_ctor_get(v_toApplicative_5682_, 1);
lean_dec(v_unused_5742_);
v___x_5691_ = v_toApplicative_5682_;
v_isShared_5692_ = v_isSharedCheck_5741_;
goto v_resetjp_5690_;
}
else
{
lean_inc(v_toSeqRight_5689_);
lean_inc(v_toSeqLeft_5688_);
lean_inc(v_toSeq_5687_);
lean_inc(v_toFunctor_5686_);
lean_dec(v_toApplicative_5682_);
v___x_5691_ = lean_box(0);
v_isShared_5692_ = v_isSharedCheck_5741_;
goto v_resetjp_5690_;
}
v_resetjp_5690_:
{
lean_object* v___f_5693_; lean_object* v___f_5694_; lean_object* v___f_5695_; lean_object* v___f_5696_; lean_object* v___x_5697_; lean_object* v___f_5698_; lean_object* v___f_5699_; lean_object* v___f_5700_; lean_object* v___x_5702_; 
v___f_5693_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__1));
v___f_5694_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_5686_);
v___f_5695_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5695_, 0, v_toFunctor_5686_);
v___f_5696_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5696_, 0, v_toFunctor_5686_);
v___x_5697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5697_, 0, v___f_5695_);
lean_ctor_set(v___x_5697_, 1, v___f_5696_);
v___f_5698_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5698_, 0, v_toSeqRight_5689_);
v___f_5699_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5699_, 0, v_toSeqLeft_5688_);
v___f_5700_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5700_, 0, v_toSeq_5687_);
if (v_isShared_5692_ == 0)
{
lean_ctor_set(v___x_5691_, 4, v___f_5698_);
lean_ctor_set(v___x_5691_, 3, v___f_5699_);
lean_ctor_set(v___x_5691_, 2, v___f_5700_);
lean_ctor_set(v___x_5691_, 1, v___f_5693_);
lean_ctor_set(v___x_5691_, 0, v___x_5697_);
v___x_5702_ = v___x_5691_;
goto v_reusejp_5701_;
}
else
{
lean_object* v_reuseFailAlloc_5740_; 
v_reuseFailAlloc_5740_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5740_, 0, v___x_5697_);
lean_ctor_set(v_reuseFailAlloc_5740_, 1, v___f_5693_);
lean_ctor_set(v_reuseFailAlloc_5740_, 2, v___f_5700_);
lean_ctor_set(v_reuseFailAlloc_5740_, 3, v___f_5699_);
lean_ctor_set(v_reuseFailAlloc_5740_, 4, v___f_5698_);
v___x_5702_ = v_reuseFailAlloc_5740_;
goto v_reusejp_5701_;
}
v_reusejp_5701_:
{
lean_object* v___x_5704_; 
if (v_isShared_5685_ == 0)
{
lean_ctor_set(v___x_5684_, 1, v___f_5694_);
lean_ctor_set(v___x_5684_, 0, v___x_5702_);
v___x_5704_ = v___x_5684_;
goto v_reusejp_5703_;
}
else
{
lean_object* v_reuseFailAlloc_5739_; 
v_reuseFailAlloc_5739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5739_, 0, v___x_5702_);
lean_ctor_set(v_reuseFailAlloc_5739_, 1, v___f_5694_);
v___x_5704_ = v_reuseFailAlloc_5739_;
goto v_reusejp_5703_;
}
v_reusejp_5703_:
{
lean_object* v___x_5705_; lean_object* v_toApplicative_5706_; lean_object* v___x_5708_; uint8_t v_isShared_5709_; uint8_t v_isSharedCheck_5737_; 
v___x_5705_ = l_StateRefT_x27_instMonad___redArg(v___x_5704_);
v_toApplicative_5706_ = lean_ctor_get(v___x_5705_, 0);
v_isSharedCheck_5737_ = !lean_is_exclusive(v___x_5705_);
if (v_isSharedCheck_5737_ == 0)
{
lean_object* v_unused_5738_; 
v_unused_5738_ = lean_ctor_get(v___x_5705_, 1);
lean_dec(v_unused_5738_);
v___x_5708_ = v___x_5705_;
v_isShared_5709_ = v_isSharedCheck_5737_;
goto v_resetjp_5707_;
}
else
{
lean_inc(v_toApplicative_5706_);
lean_dec(v___x_5705_);
v___x_5708_ = lean_box(0);
v_isShared_5709_ = v_isSharedCheck_5737_;
goto v_resetjp_5707_;
}
v_resetjp_5707_:
{
lean_object* v_toFunctor_5710_; lean_object* v_toSeq_5711_; lean_object* v_toSeqLeft_5712_; lean_object* v_toSeqRight_5713_; lean_object* v___x_5715_; uint8_t v_isShared_5716_; uint8_t v_isSharedCheck_5735_; 
v_toFunctor_5710_ = lean_ctor_get(v_toApplicative_5706_, 0);
v_toSeq_5711_ = lean_ctor_get(v_toApplicative_5706_, 2);
v_toSeqLeft_5712_ = lean_ctor_get(v_toApplicative_5706_, 3);
v_toSeqRight_5713_ = lean_ctor_get(v_toApplicative_5706_, 4);
v_isSharedCheck_5735_ = !lean_is_exclusive(v_toApplicative_5706_);
if (v_isSharedCheck_5735_ == 0)
{
lean_object* v_unused_5736_; 
v_unused_5736_ = lean_ctor_get(v_toApplicative_5706_, 1);
lean_dec(v_unused_5736_);
v___x_5715_ = v_toApplicative_5706_;
v_isShared_5716_ = v_isSharedCheck_5735_;
goto v_resetjp_5714_;
}
else
{
lean_inc(v_toSeqRight_5713_);
lean_inc(v_toSeqLeft_5712_);
lean_inc(v_toSeq_5711_);
lean_inc(v_toFunctor_5710_);
lean_dec(v_toApplicative_5706_);
v___x_5715_ = lean_box(0);
v_isShared_5716_ = v_isSharedCheck_5735_;
goto v_resetjp_5714_;
}
v_resetjp_5714_:
{
lean_object* v___f_5717_; lean_object* v___f_5718_; lean_object* v___f_5719_; lean_object* v___f_5720_; lean_object* v___x_5721_; lean_object* v___f_5722_; lean_object* v___f_5723_; lean_object* v___f_5724_; lean_object* v___x_5726_; 
v___f_5717_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__3));
v___f_5718_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_5710_);
v___f_5719_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5719_, 0, v_toFunctor_5710_);
v___f_5720_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5720_, 0, v_toFunctor_5710_);
v___x_5721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5721_, 0, v___f_5719_);
lean_ctor_set(v___x_5721_, 1, v___f_5720_);
v___f_5722_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5722_, 0, v_toSeqRight_5713_);
v___f_5723_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5723_, 0, v_toSeqLeft_5712_);
v___f_5724_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5724_, 0, v_toSeq_5711_);
if (v_isShared_5716_ == 0)
{
lean_ctor_set(v___x_5715_, 4, v___f_5722_);
lean_ctor_set(v___x_5715_, 3, v___f_5723_);
lean_ctor_set(v___x_5715_, 2, v___f_5724_);
lean_ctor_set(v___x_5715_, 1, v___f_5717_);
lean_ctor_set(v___x_5715_, 0, v___x_5721_);
v___x_5726_ = v___x_5715_;
goto v_reusejp_5725_;
}
else
{
lean_object* v_reuseFailAlloc_5734_; 
v_reuseFailAlloc_5734_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5734_, 0, v___x_5721_);
lean_ctor_set(v_reuseFailAlloc_5734_, 1, v___f_5717_);
lean_ctor_set(v_reuseFailAlloc_5734_, 2, v___f_5724_);
lean_ctor_set(v_reuseFailAlloc_5734_, 3, v___f_5723_);
lean_ctor_set(v_reuseFailAlloc_5734_, 4, v___f_5722_);
v___x_5726_ = v_reuseFailAlloc_5734_;
goto v_reusejp_5725_;
}
v_reusejp_5725_:
{
lean_object* v___x_5728_; 
if (v_isShared_5709_ == 0)
{
lean_ctor_set(v___x_5708_, 1, v___f_5718_);
lean_ctor_set(v___x_5708_, 0, v___x_5726_);
v___x_5728_ = v___x_5708_;
goto v_reusejp_5727_;
}
else
{
lean_object* v_reuseFailAlloc_5733_; 
v_reuseFailAlloc_5733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5733_, 0, v___x_5726_);
lean_ctor_set(v_reuseFailAlloc_5733_, 1, v___f_5718_);
v___x_5728_ = v_reuseFailAlloc_5733_;
goto v_reusejp_5727_;
}
v_reusejp_5727_:
{
lean_object* v___x_5729_; lean_object* v___x_5730_; lean_object* v___x_16875__overap_5731_; lean_object* v___x_5732_; 
v___x_5729_ = lean_box(0);
v___x_5730_ = l_instInhabitedOfMonad___redArg(v___x_5728_, v___x_5729_);
v___x_16875__overap_5731_ = lean_panic_fn(v___x_5730_, v_msg_5674_);
lean_inc(v___y_5678_);
lean_inc_ref(v___y_5677_);
lean_inc(v___y_5676_);
lean_inc_ref(v___y_5675_);
v___x_5732_ = lean_apply_5(v___x_16875__overap_5731_, v___y_5675_, v___y_5676_, v___y_5677_, v___y_5678_, lean_box(0));
return v___x_5732_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__0_spec__0___boxed(lean_object* v_msg_5745_, lean_object* v___y_5746_, lean_object* v___y_5747_, lean_object* v___y_5748_, lean_object* v___y_5749_, lean_object* v___y_5750_){
_start:
{
lean_object* v_res_5751_; 
v_res_5751_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__0_spec__0(v_msg_5745_, v___y_5746_, v___y_5747_, v___y_5748_, v___y_5749_);
lean_dec(v___y_5749_);
lean_dec_ref(v___y_5748_);
lean_dec(v___y_5747_);
lean_dec_ref(v___y_5746_);
return v_res_5751_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__0___closed__1(void){
_start:
{
lean_object* v___x_5753_; lean_object* v___x_5754_; 
v___x_5753_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__0___closed__0));
v___x_5754_ = l_Lean_stringToMessageData(v___x_5753_);
return v___x_5754_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__0___closed__3(void){
_start:
{
lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; lean_object* v___x_5760_; lean_object* v___x_5761_; 
v___x_5756_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__6));
v___x_5757_ = lean_unsigned_to_nat(11u);
v___x_5758_ = lean_unsigned_to_nat(122u);
v___x_5759_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__0___closed__2));
v___x_5760_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__4));
v___x_5761_ = l_mkPanicMessageWithDecl(v___x_5760_, v___x_5759_, v___x_5758_, v___x_5757_, v___x_5756_);
return v___x_5761_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__0(lean_object* v_constName_5762_, lean_object* v___y_5763_, lean_object* v___y_5764_, lean_object* v___y_5765_, lean_object* v___y_5766_){
_start:
{
lean_object* v___x_5776_; lean_object* v_env_5777_; uint8_t v___x_5778_; lean_object* v___x_5779_; 
v___x_5776_ = lean_st_ref_get(v___y_5766_);
v_env_5777_ = lean_ctor_get(v___x_5776_, 0);
lean_inc_ref(v_env_5777_);
lean_dec(v___x_5776_);
v___x_5778_ = 0;
lean_inc(v_constName_5762_);
v___x_5779_ = l_Lean_Environment_findAsync_x3f(v_env_5777_, v_constName_5762_, v___x_5778_);
if (lean_obj_tag(v___x_5779_) == 1)
{
lean_object* v_val_5780_; uint8_t v_kind_5781_; 
v_val_5780_ = lean_ctor_get(v___x_5779_, 0);
lean_inc(v_val_5780_);
lean_dec_ref(v___x_5779_);
v_kind_5781_ = lean_ctor_get_uint8(v_val_5780_, sizeof(void*)*3);
if (v_kind_5781_ == 6)
{
lean_object* v___x_5782_; 
v___x_5782_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_5780_);
if (lean_obj_tag(v___x_5782_) == 6)
{
lean_object* v_val_5783_; lean_object* v___x_5785_; uint8_t v_isShared_5786_; uint8_t v_isSharedCheck_5790_; 
lean_dec(v_constName_5762_);
v_val_5783_ = lean_ctor_get(v___x_5782_, 0);
v_isSharedCheck_5790_ = !lean_is_exclusive(v___x_5782_);
if (v_isSharedCheck_5790_ == 0)
{
v___x_5785_ = v___x_5782_;
v_isShared_5786_ = v_isSharedCheck_5790_;
goto v_resetjp_5784_;
}
else
{
lean_inc(v_val_5783_);
lean_dec(v___x_5782_);
v___x_5785_ = lean_box(0);
v_isShared_5786_ = v_isSharedCheck_5790_;
goto v_resetjp_5784_;
}
v_resetjp_5784_:
{
lean_object* v___x_5788_; 
if (v_isShared_5786_ == 0)
{
lean_ctor_set_tag(v___x_5785_, 0);
v___x_5788_ = v___x_5785_;
goto v_reusejp_5787_;
}
else
{
lean_object* v_reuseFailAlloc_5789_; 
v_reuseFailAlloc_5789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5789_, 0, v_val_5783_);
v___x_5788_ = v_reuseFailAlloc_5789_;
goto v_reusejp_5787_;
}
v_reusejp_5787_:
{
return v___x_5788_;
}
}
}
else
{
lean_object* v___x_5791_; lean_object* v___x_5792_; 
lean_dec_ref(v___x_5782_);
v___x_5791_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__0___closed__3);
v___x_5792_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__0_spec__0(v___x_5791_, v___y_5763_, v___y_5764_, v___y_5765_, v___y_5766_);
if (lean_obj_tag(v___x_5792_) == 0)
{
lean_object* v_a_5793_; lean_object* v___x_5795_; uint8_t v_isShared_5796_; uint8_t v_isSharedCheck_5801_; 
v_a_5793_ = lean_ctor_get(v___x_5792_, 0);
v_isSharedCheck_5801_ = !lean_is_exclusive(v___x_5792_);
if (v_isSharedCheck_5801_ == 0)
{
v___x_5795_ = v___x_5792_;
v_isShared_5796_ = v_isSharedCheck_5801_;
goto v_resetjp_5794_;
}
else
{
lean_inc(v_a_5793_);
lean_dec(v___x_5792_);
v___x_5795_ = lean_box(0);
v_isShared_5796_ = v_isSharedCheck_5801_;
goto v_resetjp_5794_;
}
v_resetjp_5794_:
{
if (lean_obj_tag(v_a_5793_) == 0)
{
lean_del_object(v___x_5795_);
goto v___jp_5768_;
}
else
{
lean_object* v_val_5797_; lean_object* v___x_5799_; 
lean_dec(v_constName_5762_);
v_val_5797_ = lean_ctor_get(v_a_5793_, 0);
lean_inc(v_val_5797_);
lean_dec_ref(v_a_5793_);
if (v_isShared_5796_ == 0)
{
lean_ctor_set(v___x_5795_, 0, v_val_5797_);
v___x_5799_ = v___x_5795_;
goto v_reusejp_5798_;
}
else
{
lean_object* v_reuseFailAlloc_5800_; 
v_reuseFailAlloc_5800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5800_, 0, v_val_5797_);
v___x_5799_ = v_reuseFailAlloc_5800_;
goto v_reusejp_5798_;
}
v_reusejp_5798_:
{
return v___x_5799_;
}
}
}
}
else
{
lean_object* v_a_5802_; lean_object* v___x_5804_; uint8_t v_isShared_5805_; uint8_t v_isSharedCheck_5809_; 
lean_dec(v_constName_5762_);
v_a_5802_ = lean_ctor_get(v___x_5792_, 0);
v_isSharedCheck_5809_ = !lean_is_exclusive(v___x_5792_);
if (v_isSharedCheck_5809_ == 0)
{
v___x_5804_ = v___x_5792_;
v_isShared_5805_ = v_isSharedCheck_5809_;
goto v_resetjp_5803_;
}
else
{
lean_inc(v_a_5802_);
lean_dec(v___x_5792_);
v___x_5804_ = lean_box(0);
v_isShared_5805_ = v_isSharedCheck_5809_;
goto v_resetjp_5803_;
}
v_resetjp_5803_:
{
lean_object* v___x_5807_; 
if (v_isShared_5805_ == 0)
{
v___x_5807_ = v___x_5804_;
goto v_reusejp_5806_;
}
else
{
lean_object* v_reuseFailAlloc_5808_; 
v_reuseFailAlloc_5808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5808_, 0, v_a_5802_);
v___x_5807_ = v_reuseFailAlloc_5808_;
goto v_reusejp_5806_;
}
v_reusejp_5806_:
{
return v___x_5807_;
}
}
}
}
}
else
{
lean_dec(v_val_5780_);
goto v___jp_5768_;
}
}
else
{
lean_dec(v___x_5779_);
goto v___jp_5768_;
}
v___jp_5768_:
{
lean_object* v___x_5769_; uint8_t v___x_5770_; lean_object* v___x_5771_; lean_object* v___x_5772_; lean_object* v___x_5773_; lean_object* v___x_5774_; lean_object* v___x_5775_; 
v___x_5769_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__1, &l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__1_once, _init_l_Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0___closed__1);
v___x_5770_ = 0;
v___x_5771_ = l_Lean_MessageData_ofConstName(v_constName_5762_, v___x_5770_);
v___x_5772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5772_, 0, v___x_5769_);
lean_ctor_set(v___x_5772_, 1, v___x_5771_);
v___x_5773_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__0___closed__1);
v___x_5774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5774_, 0, v___x_5772_);
lean_ctor_set(v___x_5774_, 1, v___x_5773_);
v___x_5775_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__0___redArg(v___x_5774_, v___y_5763_, v___y_5764_, v___y_5765_, v___y_5766_);
return v___x_5775_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__0___boxed(lean_object* v_constName_5810_, lean_object* v___y_5811_, lean_object* v___y_5812_, lean_object* v___y_5813_, lean_object* v___y_5814_, lean_object* v___y_5815_){
_start:
{
lean_object* v_res_5816_; 
v_res_5816_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__0(v_constName_5810_, v___y_5811_, v___y_5812_, v___y_5813_, v___y_5814_);
lean_dec(v___y_5814_);
lean_dec_ref(v___y_5813_);
lean_dec(v___y_5812_);
lean_dec_ref(v___y_5811_);
return v_res_5816_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__1___redArg(lean_object* v_x_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_, lean_object* v___y_5820_, lean_object* v___y_5821_){
_start:
{
if (lean_obj_tag(v_x_5817_) == 0)
{
lean_object* v_a_5823_; lean_object* v___x_5824_; lean_object* v___x_5825_; 
v_a_5823_ = lean_ctor_get(v_x_5817_, 0);
lean_inc(v_a_5823_);
lean_dec_ref(v_x_5817_);
v___x_5824_ = l_Lean_stringToMessageData(v_a_5823_);
v___x_5825_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_Meta_mkSizeOfFn_spec__0_spec__0___redArg(v___x_5824_, v___y_5818_, v___y_5819_, v___y_5820_, v___y_5821_);
return v___x_5825_;
}
else
{
lean_object* v_a_5826_; lean_object* v___x_5828_; uint8_t v_isShared_5829_; uint8_t v_isSharedCheck_5833_; 
v_a_5826_ = lean_ctor_get(v_x_5817_, 0);
v_isSharedCheck_5833_ = !lean_is_exclusive(v_x_5817_);
if (v_isSharedCheck_5833_ == 0)
{
v___x_5828_ = v_x_5817_;
v_isShared_5829_ = v_isSharedCheck_5833_;
goto v_resetjp_5827_;
}
else
{
lean_inc(v_a_5826_);
lean_dec(v_x_5817_);
v___x_5828_ = lean_box(0);
v_isShared_5829_ = v_isSharedCheck_5833_;
goto v_resetjp_5827_;
}
v_resetjp_5827_:
{
lean_object* v___x_5831_; 
if (v_isShared_5829_ == 0)
{
lean_ctor_set_tag(v___x_5828_, 0);
v___x_5831_ = v___x_5828_;
goto v_reusejp_5830_;
}
else
{
lean_object* v_reuseFailAlloc_5832_; 
v_reuseFailAlloc_5832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5832_, 0, v_a_5826_);
v___x_5831_ = v_reuseFailAlloc_5832_;
goto v_reusejp_5830_;
}
v_reusejp_5830_:
{
return v___x_5831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__1___redArg___boxed(lean_object* v_x_5834_, lean_object* v___y_5835_, lean_object* v___y_5836_, lean_object* v___y_5837_, lean_object* v___y_5838_, lean_object* v___y_5839_){
_start:
{
lean_object* v_res_5840_; 
v_res_5840_ = l_Lean_ofExcept___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__1___redArg(v_x_5834_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_);
lean_dec(v___y_5838_);
lean_dec_ref(v___y_5837_);
lean_dec(v___y_5836_);
lean_dec_ref(v___y_5835_);
return v_res_5840_;
}
}
static lean_object* _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__15(void){
_start:
{
lean_object* v___x_5871_; 
v___x_5871_ = l_Array_mkArray0(lean_box(0));
return v___x_5871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2(lean_object* v_ctorName_5872_, lean_object* v_indInfo_5873_, lean_object* v_sizeOfFns_5874_, lean_object* v_recMap_5875_, lean_object* v___y_5876_, lean_object* v___y_5877_, lean_object* v___y_5878_, lean_object* v___y_5879_){
_start:
{
lean_object* v___x_5881_; 
lean_inc(v_ctorName_5872_);
v___x_5881_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__0(v_ctorName_5872_, v___y_5876_, v___y_5877_, v___y_5878_, v___y_5879_);
if (lean_obj_tag(v___x_5881_) == 0)
{
lean_object* v_a_5882_; lean_object* v___x_5883_; lean_object* v_env_5884_; lean_object* v___x_5885_; lean_object* v___x_5886_; lean_object* v___x_5887_; 
v_a_5882_ = lean_ctor_get(v___x_5881_, 0);
lean_inc(v_a_5882_);
lean_dec_ref(v___x_5881_);
v___x_5883_ = lean_st_ref_get(v___y_5879_);
v_env_5884_ = lean_ctor_get(v___x_5883_, 0);
lean_inc_ref(v_env_5884_);
lean_dec(v___x_5883_);
v___x_5885_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__1));
v___x_5886_ = l_Lean_getAttributeImpl(v_env_5884_, v___x_5885_);
v___x_5887_ = l_Lean_ofExcept___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__1___redArg(v___x_5886_, v___y_5876_, v___y_5877_, v___y_5878_, v___y_5879_);
if (lean_obj_tag(v___x_5887_) == 0)
{
lean_object* v_a_5888_; lean_object* v___x_5889_; lean_object* v_env_5890_; lean_object* v___x_5891_; lean_object* v___x_5892_; lean_object* v___x_5893_; lean_object* v___x_5894_; 
v_a_5888_ = lean_ctor_get(v___x_5887_, 0);
lean_inc(v_a_5888_);
lean_dec_ref(v___x_5887_);
v___x_5889_ = lean_st_ref_get(v___y_5879_);
v_env_5890_ = lean_ctor_get(v___x_5889_, 0);
lean_inc_ref(v_env_5890_);
lean_dec(v___x_5889_);
v___x_5891_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__2));
v___x_5892_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__3));
v___x_5893_ = l_Lean_getAttributeImpl(v_env_5890_, v___x_5892_);
v___x_5894_ = l_Lean_ofExcept___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__1___redArg(v___x_5893_, v___y_5876_, v___y_5877_, v___y_5878_, v___y_5879_);
if (lean_obj_tag(v___x_5894_) == 0)
{
lean_object* v_toConstantVal_5895_; lean_object* v_a_5896_; lean_object* v_numParams_5897_; lean_object* v_name_5898_; lean_object* v_levelParams_5899_; lean_object* v_type_5900_; lean_object* v___x_5902_; uint8_t v_isShared_5903_; uint8_t v_isSharedCheck_5927_; 
v_toConstantVal_5895_ = lean_ctor_get(v_a_5882_, 0);
lean_inc_ref(v_toConstantVal_5895_);
v_a_5896_ = lean_ctor_get(v___x_5894_, 0);
lean_inc(v_a_5896_);
lean_dec_ref(v___x_5894_);
v_numParams_5897_ = lean_ctor_get(v_a_5882_, 3);
lean_inc(v_numParams_5897_);
lean_dec(v_a_5882_);
v_name_5898_ = lean_ctor_get(v_toConstantVal_5895_, 0);
v_levelParams_5899_ = lean_ctor_get(v_toConstantVal_5895_, 1);
v_type_5900_ = lean_ctor_get(v_toConstantVal_5895_, 2);
v_isSharedCheck_5927_ = !lean_is_exclusive(v_toConstantVal_5895_);
if (v_isSharedCheck_5927_ == 0)
{
v___x_5902_ = v_toConstantVal_5895_;
v_isShared_5903_ = v_isSharedCheck_5927_;
goto v_resetjp_5901_;
}
else
{
lean_inc(v_type_5900_);
lean_inc(v_levelParams_5899_);
lean_inc(v_name_5898_);
lean_dec(v_toConstantVal_5895_);
v___x_5902_ = lean_box(0);
v_isShared_5903_ = v_isSharedCheck_5927_;
goto v_resetjp_5901_;
}
v_resetjp_5901_:
{
lean_object* v_ref_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; uint8_t v___x_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; lean_object* v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5918_; 
v_ref_5904_ = lean_ctor_get(v___y_5878_, 5);
v___x_5905_ = lean_box(0);
lean_inc(v_levelParams_5899_);
v___x_5906_ = l_List_mapTR_loop___at___00Lean_Meta_mkSizeOfFn_spec__1(v_levelParams_5899_, v___x_5905_);
v___x_5907_ = 0;
v___x_5908_ = l_Lean_SourceInfo_fromRef(v_ref_5904_, v___x_5907_);
v___x_5909_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__7));
lean_inc(v___x_5908_);
v___x_5910_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5910_, 0, v___x_5908_);
lean_ctor_set(v___x_5910_, 1, v___x_5891_);
v___x_5911_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__9));
v___x_5912_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__11));
v___x_5913_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__13));
v___x_5914_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__14));
lean_inc(v___x_5908_);
v___x_5915_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5915_, 0, v___x_5908_);
lean_ctor_set(v___x_5915_, 1, v___x_5914_);
v___x_5916_ = lean_obj_once(&l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__15, &l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__15_once, _init_l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___closed__15);
lean_inc(v___x_5908_);
if (v_isShared_5903_ == 0)
{
lean_ctor_set_tag(v___x_5902_, 1);
lean_ctor_set(v___x_5902_, 2, v___x_5916_);
lean_ctor_set(v___x_5902_, 1, v___x_5911_);
lean_ctor_set(v___x_5902_, 0, v___x_5908_);
v___x_5918_ = v___x_5902_;
goto v_reusejp_5917_;
}
else
{
lean_object* v_reuseFailAlloc_5926_; 
v_reuseFailAlloc_5926_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5926_, 0, v___x_5908_);
lean_ctor_set(v_reuseFailAlloc_5926_, 1, v___x_5911_);
lean_ctor_set(v_reuseFailAlloc_5926_, 2, v___x_5916_);
v___x_5918_ = v_reuseFailAlloc_5926_;
goto v_reusejp_5917_;
}
v_reusejp_5917_:
{
lean_object* v___x_5919_; lean_object* v___x_5920_; lean_object* v___x_5921_; lean_object* v___x_5922_; lean_object* v___x_5923_; lean_object* v___f_5924_; lean_object* v___x_5925_; 
lean_inc(v___x_5908_);
v___x_5919_ = l_Lean_Syntax_node2(v___x_5908_, v___x_5913_, v___x_5915_, v___x_5918_);
lean_inc(v___x_5908_);
v___x_5920_ = l_Lean_Syntax_node1(v___x_5908_, v___x_5912_, v___x_5919_);
lean_inc(v___x_5908_);
v___x_5921_ = l_Lean_Syntax_node1(v___x_5908_, v___x_5911_, v___x_5920_);
v___x_5922_ = l_Lean_Syntax_node2(v___x_5908_, v___x_5909_, v___x_5910_, v___x_5921_);
v___x_5923_ = lean_box(v___x_5907_);
v___f_5924_ = lean_alloc_closure((void*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__1___boxed), 20, 13);
lean_closure_set(v___f_5924_, 0, v_numParams_5897_);
lean_closure_set(v___f_5924_, 1, v_ctorName_5872_);
lean_closure_set(v___f_5924_, 2, v___x_5906_);
lean_closure_set(v___f_5924_, 3, v_indInfo_5873_);
lean_closure_set(v___f_5924_, 4, v_levelParams_5899_);
lean_closure_set(v___f_5924_, 5, v___x_5923_);
lean_closure_set(v___f_5924_, 6, v_a_5888_);
lean_closure_set(v___f_5924_, 7, v_a_5896_);
lean_closure_set(v___f_5924_, 8, v___x_5922_);
lean_closure_set(v___f_5924_, 9, v_sizeOfFns_5874_);
lean_closure_set(v___f_5924_, 10, v_recMap_5875_);
lean_closure_set(v___f_5924_, 11, v___x_5905_);
lean_closure_set(v___f_5924_, 12, v_name_5898_);
v___x_5925_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__0___redArg(v_type_5900_, v___f_5924_, v___x_5907_, v___x_5907_, v___y_5876_, v___y_5877_, v___y_5878_, v___y_5879_);
return v___x_5925_;
}
}
}
else
{
lean_object* v_a_5928_; lean_object* v___x_5930_; uint8_t v_isShared_5931_; uint8_t v_isSharedCheck_5935_; 
lean_dec(v_a_5888_);
lean_dec(v_a_5882_);
lean_dec(v_recMap_5875_);
lean_dec_ref(v_sizeOfFns_5874_);
lean_dec_ref(v_indInfo_5873_);
lean_dec(v_ctorName_5872_);
v_a_5928_ = lean_ctor_get(v___x_5894_, 0);
v_isSharedCheck_5935_ = !lean_is_exclusive(v___x_5894_);
if (v_isSharedCheck_5935_ == 0)
{
v___x_5930_ = v___x_5894_;
v_isShared_5931_ = v_isSharedCheck_5935_;
goto v_resetjp_5929_;
}
else
{
lean_inc(v_a_5928_);
lean_dec(v___x_5894_);
v___x_5930_ = lean_box(0);
v_isShared_5931_ = v_isSharedCheck_5935_;
goto v_resetjp_5929_;
}
v_resetjp_5929_:
{
lean_object* v___x_5933_; 
if (v_isShared_5931_ == 0)
{
v___x_5933_ = v___x_5930_;
goto v_reusejp_5932_;
}
else
{
lean_object* v_reuseFailAlloc_5934_; 
v_reuseFailAlloc_5934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5934_, 0, v_a_5928_);
v___x_5933_ = v_reuseFailAlloc_5934_;
goto v_reusejp_5932_;
}
v_reusejp_5932_:
{
return v___x_5933_;
}
}
}
}
else
{
lean_object* v_a_5936_; lean_object* v___x_5938_; uint8_t v_isShared_5939_; uint8_t v_isSharedCheck_5943_; 
lean_dec(v_a_5882_);
lean_dec(v_recMap_5875_);
lean_dec_ref(v_sizeOfFns_5874_);
lean_dec_ref(v_indInfo_5873_);
lean_dec(v_ctorName_5872_);
v_a_5936_ = lean_ctor_get(v___x_5887_, 0);
v_isSharedCheck_5943_ = !lean_is_exclusive(v___x_5887_);
if (v_isSharedCheck_5943_ == 0)
{
v___x_5938_ = v___x_5887_;
v_isShared_5939_ = v_isSharedCheck_5943_;
goto v_resetjp_5937_;
}
else
{
lean_inc(v_a_5936_);
lean_dec(v___x_5887_);
v___x_5938_ = lean_box(0);
v_isShared_5939_ = v_isSharedCheck_5943_;
goto v_resetjp_5937_;
}
v_resetjp_5937_:
{
lean_object* v___x_5941_; 
if (v_isShared_5939_ == 0)
{
v___x_5941_ = v___x_5938_;
goto v_reusejp_5940_;
}
else
{
lean_object* v_reuseFailAlloc_5942_; 
v_reuseFailAlloc_5942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5942_, 0, v_a_5936_);
v___x_5941_ = v_reuseFailAlloc_5942_;
goto v_reusejp_5940_;
}
v_reusejp_5940_:
{
return v___x_5941_;
}
}
}
}
else
{
lean_object* v_a_5944_; lean_object* v___x_5946_; uint8_t v_isShared_5947_; uint8_t v_isSharedCheck_5951_; 
lean_dec(v_recMap_5875_);
lean_dec_ref(v_sizeOfFns_5874_);
lean_dec_ref(v_indInfo_5873_);
lean_dec(v_ctorName_5872_);
v_a_5944_ = lean_ctor_get(v___x_5881_, 0);
v_isSharedCheck_5951_ = !lean_is_exclusive(v___x_5881_);
if (v_isSharedCheck_5951_ == 0)
{
v___x_5946_ = v___x_5881_;
v_isShared_5947_ = v_isSharedCheck_5951_;
goto v_resetjp_5945_;
}
else
{
lean_inc(v_a_5944_);
lean_dec(v___x_5881_);
v___x_5946_ = lean_box(0);
v_isShared_5947_ = v_isSharedCheck_5951_;
goto v_resetjp_5945_;
}
v_resetjp_5945_:
{
lean_object* v___x_5949_; 
if (v_isShared_5947_ == 0)
{
v___x_5949_ = v___x_5946_;
goto v_reusejp_5948_;
}
else
{
lean_object* v_reuseFailAlloc_5950_; 
v_reuseFailAlloc_5950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5950_, 0, v_a_5944_);
v___x_5949_ = v_reuseFailAlloc_5950_;
goto v_reusejp_5948_;
}
v_reusejp_5948_:
{
return v___x_5949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___boxed(lean_object* v_ctorName_5952_, lean_object* v_indInfo_5953_, lean_object* v_sizeOfFns_5954_, lean_object* v_recMap_5955_, lean_object* v___y_5956_, lean_object* v___y_5957_, lean_object* v___y_5958_, lean_object* v___y_5959_, lean_object* v___y_5960_){
_start:
{
lean_object* v_res_5961_; 
v_res_5961_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2(v_ctorName_5952_, v_indInfo_5953_, v_sizeOfFns_5954_, v_recMap_5955_, v___y_5956_, v___y_5957_, v___y_5958_, v___y_5959_);
lean_dec(v___y_5959_);
lean_dec_ref(v___y_5958_);
lean_dec(v___y_5957_);
lean_dec_ref(v___y_5956_);
return v_res_5961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem(lean_object* v_indInfo_5962_, lean_object* v_sizeOfFns_5963_, lean_object* v_recMap_5964_, lean_object* v_ctorName_5965_, lean_object* v_a_5966_, lean_object* v_a_5967_, lean_object* v_a_5968_, lean_object* v_a_5969_){
_start:
{
lean_object* v___f_5971_; uint8_t v___x_5972_; 
lean_inc(v_ctorName_5965_);
v___f_5971_ = lean_alloc_closure((void*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__2___boxed), 9, 4);
lean_closure_set(v___f_5971_, 0, v_ctorName_5965_);
lean_closure_set(v___f_5971_, 1, v_indInfo_5962_);
lean_closure_set(v___f_5971_, 2, v_sizeOfFns_5963_);
lean_closure_set(v___f_5971_, 3, v_recMap_5964_);
v___x_5972_ = l_Lean_isPrivateName(v_ctorName_5965_);
lean_dec(v_ctorName_5965_);
if (v___x_5972_ == 0)
{
uint8_t v___x_5973_; lean_object* v___x_5974_; 
v___x_5973_ = 1;
v___x_5974_ = l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg(v___f_5971_, v___x_5973_, v_a_5966_, v_a_5967_, v_a_5968_, v_a_5969_);
return v___x_5974_;
}
else
{
uint8_t v___x_5975_; lean_object* v___x_5976_; 
v___x_5975_ = 0;
v___x_5976_ = l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg(v___f_5971_, v___x_5975_, v_a_5966_, v_a_5967_, v_a_5968_, v_a_5969_);
return v___x_5976_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___boxed(lean_object* v_indInfo_5977_, lean_object* v_sizeOfFns_5978_, lean_object* v_recMap_5979_, lean_object* v_ctorName_5980_, lean_object* v_a_5981_, lean_object* v_a_5982_, lean_object* v_a_5983_, lean_object* v_a_5984_, lean_object* v_a_5985_){
_start:
{
lean_object* v_res_5986_; 
v_res_5986_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem(v_indInfo_5977_, v_sizeOfFns_5978_, v_recMap_5979_, v_ctorName_5980_, v_a_5981_, v_a_5982_, v_a_5983_, v_a_5984_);
lean_dec(v_a_5984_);
lean_dec_ref(v_a_5983_);
lean_dec(v_a_5982_);
lean_dec_ref(v_a_5981_);
return v_res_5986_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__1(lean_object* v_00_u03b1_5987_, lean_object* v_x_5988_, lean_object* v___y_5989_, lean_object* v___y_5990_, lean_object* v___y_5991_, lean_object* v___y_5992_){
_start:
{
lean_object* v___x_5994_; 
v___x_5994_ = l_Lean_ofExcept___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__1___redArg(v_x_5988_, v___y_5989_, v___y_5990_, v___y_5991_, v___y_5992_);
return v___x_5994_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__1___boxed(lean_object* v_00_u03b1_5995_, lean_object* v_x_5996_, lean_object* v___y_5997_, lean_object* v___y_5998_, lean_object* v___y_5999_, lean_object* v___y_6000_, lean_object* v___y_6001_){
_start:
{
lean_object* v_res_6002_; 
v_res_6002_ = l_Lean_ofExcept___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__1(v_00_u03b1_5995_, v_x_5996_, v___y_5997_, v___y_5998_, v___y_5999_, v___y_6000_);
lean_dec(v___y_6000_);
lean_dec_ref(v___y_5999_);
lean_dec(v___y_5998_);
lean_dec_ref(v___y_5997_);
return v_res_6002_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__2(lean_object* v_inst_6003_, lean_object* v_R_6004_, lean_object* v_a_6005_, lean_object* v_b_6006_, lean_object* v_c_6007_, lean_object* v___y_6008_, lean_object* v___y_6009_, lean_object* v___y_6010_, lean_object* v___y_6011_){
_start:
{
lean_object* v___x_6013_; 
v___x_6013_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__2___redArg(v_a_6005_, v_b_6006_, v___y_6008_, v___y_6009_, v___y_6010_, v___y_6011_);
return v___x_6013_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__2___boxed(lean_object* v_inst_6014_, lean_object* v_R_6015_, lean_object* v_a_6016_, lean_object* v_b_6017_, lean_object* v_c_6018_, lean_object* v___y_6019_, lean_object* v___y_6020_, lean_object* v___y_6021_, lean_object* v___y_6022_, lean_object* v___y_6023_){
_start:
{
lean_object* v_res_6024_; 
v_res_6024_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem_spec__2(v_inst_6014_, v_R_6015_, v_a_6016_, v_b_6017_, v_c_6018_, v___y_6019_, v___y_6020_, v___y_6021_, v___y_6022_);
lean_dec(v___y_6022_);
lean_dec_ref(v___y_6021_);
lean_dec(v___y_6020_);
lean_dec_ref(v___y_6019_);
return v_res_6024_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorems_spec__0___redArg(lean_object* v_a_6025_, lean_object* v_sizeOfFns_6026_, lean_object* v_recMap_6027_, lean_object* v_as_x27_6028_, lean_object* v_b_6029_, lean_object* v___y_6030_, lean_object* v___y_6031_, lean_object* v___y_6032_, lean_object* v___y_6033_){
_start:
{
if (lean_obj_tag(v_as_x27_6028_) == 0)
{
lean_object* v___x_6035_; 
lean_dec(v_recMap_6027_);
lean_dec_ref(v_sizeOfFns_6026_);
lean_dec_ref(v_a_6025_);
v___x_6035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6035_, 0, v_b_6029_);
return v___x_6035_;
}
else
{
lean_object* v_head_6036_; lean_object* v_tail_6037_; lean_object* v___x_6038_; 
v_head_6036_ = lean_ctor_get(v_as_x27_6028_, 0);
lean_inc(v_head_6036_);
v_tail_6037_ = lean_ctor_get(v_as_x27_6028_, 1);
lean_inc(v_tail_6037_);
lean_dec_ref(v_as_x27_6028_);
lean_inc(v_recMap_6027_);
lean_inc_ref(v_sizeOfFns_6026_);
lean_inc_ref(v_a_6025_);
v___x_6038_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem(v_a_6025_, v_sizeOfFns_6026_, v_recMap_6027_, v_head_6036_, v___y_6030_, v___y_6031_, v___y_6032_, v___y_6033_);
if (lean_obj_tag(v___x_6038_) == 0)
{
lean_object* v___x_6039_; 
lean_dec_ref(v___x_6038_);
v___x_6039_ = lean_box(0);
v_as_x27_6028_ = v_tail_6037_;
v_b_6029_ = v___x_6039_;
goto _start;
}
else
{
lean_dec(v_tail_6037_);
lean_dec(v_recMap_6027_);
lean_dec_ref(v_sizeOfFns_6026_);
lean_dec_ref(v_a_6025_);
return v___x_6038_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorems_spec__0___redArg___boxed(lean_object* v_a_6041_, lean_object* v_sizeOfFns_6042_, lean_object* v_recMap_6043_, lean_object* v_as_x27_6044_, lean_object* v_b_6045_, lean_object* v___y_6046_, lean_object* v___y_6047_, lean_object* v___y_6048_, lean_object* v___y_6049_, lean_object* v___y_6050_){
_start:
{
lean_object* v_res_6051_; 
v_res_6051_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorems_spec__0___redArg(v_a_6041_, v_sizeOfFns_6042_, v_recMap_6043_, v_as_x27_6044_, v_b_6045_, v___y_6046_, v___y_6047_, v___y_6048_, v___y_6049_);
lean_dec(v___y_6049_);
lean_dec_ref(v___y_6048_);
lean_dec(v___y_6047_);
lean_dec_ref(v___y_6046_);
return v_res_6051_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorems_spec__1(lean_object* v_sizeOfFns_6052_, lean_object* v_recMap_6053_, lean_object* v_as_6054_, size_t v_sz_6055_, size_t v_i_6056_, lean_object* v_b_6057_, lean_object* v___y_6058_, lean_object* v___y_6059_, lean_object* v___y_6060_, lean_object* v___y_6061_){
_start:
{
uint8_t v___x_6063_; 
v___x_6063_ = lean_usize_dec_lt(v_i_6056_, v_sz_6055_);
if (v___x_6063_ == 0)
{
lean_object* v___x_6064_; 
lean_dec(v_recMap_6053_);
lean_dec_ref(v_sizeOfFns_6052_);
v___x_6064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6064_, 0, v_b_6057_);
return v___x_6064_;
}
else
{
lean_object* v_a_6065_; lean_object* v___x_6066_; 
v_a_6065_ = lean_array_uget_borrowed(v_as_6054_, v_i_6056_);
lean_inc(v_a_6065_);
v___x_6066_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSizeOfFns_spec__0(v_a_6065_, v___y_6058_, v___y_6059_, v___y_6060_, v___y_6061_);
if (lean_obj_tag(v___x_6066_) == 0)
{
lean_object* v_a_6067_; lean_object* v_ctors_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; 
v_a_6067_ = lean_ctor_get(v___x_6066_, 0);
lean_inc(v_a_6067_);
lean_dec_ref(v___x_6066_);
v_ctors_6068_ = lean_ctor_get(v_a_6067_, 4);
lean_inc(v_ctors_6068_);
v___x_6069_ = lean_box(0);
lean_inc(v_recMap_6053_);
lean_inc_ref(v_sizeOfFns_6052_);
v___x_6070_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorems_spec__0___redArg(v_a_6067_, v_sizeOfFns_6052_, v_recMap_6053_, v_ctors_6068_, v___x_6069_, v___y_6058_, v___y_6059_, v___y_6060_, v___y_6061_);
if (lean_obj_tag(v___x_6070_) == 0)
{
size_t v___x_6071_; size_t v___x_6072_; 
lean_dec_ref(v___x_6070_);
v___x_6071_ = ((size_t)1ULL);
v___x_6072_ = lean_usize_add(v_i_6056_, v___x_6071_);
v_i_6056_ = v___x_6072_;
v_b_6057_ = v___x_6069_;
goto _start;
}
else
{
lean_dec(v_recMap_6053_);
lean_dec_ref(v_sizeOfFns_6052_);
return v___x_6070_;
}
}
else
{
lean_object* v_a_6074_; lean_object* v___x_6076_; uint8_t v_isShared_6077_; uint8_t v_isSharedCheck_6081_; 
lean_dec(v_recMap_6053_);
lean_dec_ref(v_sizeOfFns_6052_);
v_a_6074_ = lean_ctor_get(v___x_6066_, 0);
v_isSharedCheck_6081_ = !lean_is_exclusive(v___x_6066_);
if (v_isSharedCheck_6081_ == 0)
{
v___x_6076_ = v___x_6066_;
v_isShared_6077_ = v_isSharedCheck_6081_;
goto v_resetjp_6075_;
}
else
{
lean_inc(v_a_6074_);
lean_dec(v___x_6066_);
v___x_6076_ = lean_box(0);
v_isShared_6077_ = v_isSharedCheck_6081_;
goto v_resetjp_6075_;
}
v_resetjp_6075_:
{
lean_object* v___x_6079_; 
if (v_isShared_6077_ == 0)
{
v___x_6079_ = v___x_6076_;
goto v_reusejp_6078_;
}
else
{
lean_object* v_reuseFailAlloc_6080_; 
v_reuseFailAlloc_6080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6080_, 0, v_a_6074_);
v___x_6079_ = v_reuseFailAlloc_6080_;
goto v_reusejp_6078_;
}
v_reusejp_6078_:
{
return v___x_6079_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorems_spec__1___boxed(lean_object* v_sizeOfFns_6082_, lean_object* v_recMap_6083_, lean_object* v_as_6084_, lean_object* v_sz_6085_, lean_object* v_i_6086_, lean_object* v_b_6087_, lean_object* v___y_6088_, lean_object* v___y_6089_, lean_object* v___y_6090_, lean_object* v___y_6091_, lean_object* v___y_6092_){
_start:
{
size_t v_sz_boxed_6093_; size_t v_i_boxed_6094_; lean_object* v_res_6095_; 
v_sz_boxed_6093_ = lean_unbox_usize(v_sz_6085_);
lean_dec(v_sz_6085_);
v_i_boxed_6094_ = lean_unbox_usize(v_i_6086_);
lean_dec(v_i_6086_);
v_res_6095_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorems_spec__1(v_sizeOfFns_6082_, v_recMap_6083_, v_as_6084_, v_sz_boxed_6093_, v_i_boxed_6094_, v_b_6087_, v___y_6088_, v___y_6089_, v___y_6090_, v___y_6091_);
lean_dec(v___y_6091_);
lean_dec_ref(v___y_6090_);
lean_dec(v___y_6089_);
lean_dec_ref(v___y_6088_);
lean_dec_ref(v_as_6084_);
return v_res_6095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorems(lean_object* v_indTypeNames_6096_, lean_object* v_sizeOfFns_6097_, lean_object* v_recMap_6098_, lean_object* v_a_6099_, lean_object* v_a_6100_, lean_object* v_a_6101_, lean_object* v_a_6102_){
_start:
{
lean_object* v___x_6104_; size_t v_sz_6105_; size_t v___x_6106_; lean_object* v___x_6107_; 
v___x_6104_ = lean_box(0);
v_sz_6105_ = lean_array_size(v_indTypeNames_6096_);
v___x_6106_ = ((size_t)0ULL);
v___x_6107_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorems_spec__1(v_sizeOfFns_6097_, v_recMap_6098_, v_indTypeNames_6096_, v_sz_6105_, v___x_6106_, v___x_6104_, v_a_6099_, v_a_6100_, v_a_6101_, v_a_6102_);
if (lean_obj_tag(v___x_6107_) == 0)
{
lean_object* v___x_6109_; uint8_t v_isShared_6110_; uint8_t v_isSharedCheck_6114_; 
v_isSharedCheck_6114_ = !lean_is_exclusive(v___x_6107_);
if (v_isSharedCheck_6114_ == 0)
{
lean_object* v_unused_6115_; 
v_unused_6115_ = lean_ctor_get(v___x_6107_, 0);
lean_dec(v_unused_6115_);
v___x_6109_ = v___x_6107_;
v_isShared_6110_ = v_isSharedCheck_6114_;
goto v_resetjp_6108_;
}
else
{
lean_dec(v___x_6107_);
v___x_6109_ = lean_box(0);
v_isShared_6110_ = v_isSharedCheck_6114_;
goto v_resetjp_6108_;
}
v_resetjp_6108_:
{
lean_object* v___x_6112_; 
if (v_isShared_6110_ == 0)
{
lean_ctor_set(v___x_6109_, 0, v___x_6104_);
v___x_6112_ = v___x_6109_;
goto v_reusejp_6111_;
}
else
{
lean_object* v_reuseFailAlloc_6113_; 
v_reuseFailAlloc_6113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6113_, 0, v___x_6104_);
v___x_6112_ = v_reuseFailAlloc_6113_;
goto v_reusejp_6111_;
}
v_reusejp_6111_:
{
return v___x_6112_;
}
}
}
else
{
return v___x_6107_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorems___boxed(lean_object* v_indTypeNames_6116_, lean_object* v_sizeOfFns_6117_, lean_object* v_recMap_6118_, lean_object* v_a_6119_, lean_object* v_a_6120_, lean_object* v_a_6121_, lean_object* v_a_6122_, lean_object* v_a_6123_){
_start:
{
lean_object* v_res_6124_; 
v_res_6124_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorems(v_indTypeNames_6116_, v_sizeOfFns_6117_, v_recMap_6118_, v_a_6119_, v_a_6120_, v_a_6121_, v_a_6122_);
lean_dec(v_a_6122_);
lean_dec_ref(v_a_6121_);
lean_dec(v_a_6120_);
lean_dec_ref(v_a_6119_);
lean_dec_ref(v_indTypeNames_6116_);
return v_res_6124_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorems_spec__0(lean_object* v_a_6125_, lean_object* v_sizeOfFns_6126_, lean_object* v_recMap_6127_, lean_object* v_as_6128_, lean_object* v_as_x27_6129_, lean_object* v_b_6130_, lean_object* v_a_6131_, lean_object* v___y_6132_, lean_object* v___y_6133_, lean_object* v___y_6134_, lean_object* v___y_6135_){
_start:
{
lean_object* v___x_6137_; 
v___x_6137_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorems_spec__0___redArg(v_a_6125_, v_sizeOfFns_6126_, v_recMap_6127_, v_as_x27_6129_, v_b_6130_, v___y_6132_, v___y_6133_, v___y_6134_, v___y_6135_);
return v___x_6137_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorems_spec__0___boxed(lean_object* v_a_6138_, lean_object* v_sizeOfFns_6139_, lean_object* v_recMap_6140_, lean_object* v_as_6141_, lean_object* v_as_x27_6142_, lean_object* v_b_6143_, lean_object* v_a_6144_, lean_object* v___y_6145_, lean_object* v___y_6146_, lean_object* v___y_6147_, lean_object* v___y_6148_, lean_object* v___y_6149_){
_start:
{
lean_object* v_res_6150_; 
v_res_6150_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorems_spec__0(v_a_6138_, v_sizeOfFns_6139_, v_recMap_6140_, v_as_6141_, v_as_x27_6142_, v_b_6143_, v_a_6144_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_);
lean_dec(v___y_6148_);
lean_dec_ref(v___y_6147_);
lean_dec(v___y_6146_);
lean_dec_ref(v___y_6145_);
lean_dec(v_as_6141_);
return v_res_6150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4__spec__0(lean_object* v_name_6151_, lean_object* v_decl_6152_, lean_object* v_ref_6153_){
_start:
{
lean_object* v_defValue_6155_; lean_object* v_descr_6156_; lean_object* v___x_6158_; uint8_t v_isShared_6159_; uint8_t v_isSharedCheck_6183_; 
v_defValue_6155_ = lean_ctor_get(v_decl_6152_, 0);
v_descr_6156_ = lean_ctor_get(v_decl_6152_, 1);
v_isSharedCheck_6183_ = !lean_is_exclusive(v_decl_6152_);
if (v_isSharedCheck_6183_ == 0)
{
v___x_6158_ = v_decl_6152_;
v_isShared_6159_ = v_isSharedCheck_6183_;
goto v_resetjp_6157_;
}
else
{
lean_inc(v_descr_6156_);
lean_inc(v_defValue_6155_);
lean_dec(v_decl_6152_);
v___x_6158_ = lean_box(0);
v_isShared_6159_ = v_isSharedCheck_6183_;
goto v_resetjp_6157_;
}
v_resetjp_6157_:
{
lean_object* v___x_6160_; uint8_t v___x_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; 
v___x_6160_ = lean_alloc_ctor(1, 0, 1);
v___x_6161_ = lean_unbox(v_defValue_6155_);
lean_ctor_set_uint8(v___x_6160_, 0, v___x_6161_);
lean_inc(v_name_6151_);
v___x_6162_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6162_, 0, v_name_6151_);
lean_ctor_set(v___x_6162_, 1, v_ref_6153_);
lean_ctor_set(v___x_6162_, 2, v___x_6160_);
lean_ctor_set(v___x_6162_, 3, v_descr_6156_);
lean_inc(v_name_6151_);
v___x_6163_ = lean_register_option(v_name_6151_, v___x_6162_);
if (lean_obj_tag(v___x_6163_) == 0)
{
lean_object* v___x_6165_; uint8_t v_isShared_6166_; uint8_t v_isSharedCheck_6173_; 
v_isSharedCheck_6173_ = !lean_is_exclusive(v___x_6163_);
if (v_isSharedCheck_6173_ == 0)
{
lean_object* v_unused_6174_; 
v_unused_6174_ = lean_ctor_get(v___x_6163_, 0);
lean_dec(v_unused_6174_);
v___x_6165_ = v___x_6163_;
v_isShared_6166_ = v_isSharedCheck_6173_;
goto v_resetjp_6164_;
}
else
{
lean_dec(v___x_6163_);
v___x_6165_ = lean_box(0);
v_isShared_6166_ = v_isSharedCheck_6173_;
goto v_resetjp_6164_;
}
v_resetjp_6164_:
{
lean_object* v___x_6168_; 
if (v_isShared_6159_ == 0)
{
lean_ctor_set(v___x_6158_, 1, v_defValue_6155_);
lean_ctor_set(v___x_6158_, 0, v_name_6151_);
v___x_6168_ = v___x_6158_;
goto v_reusejp_6167_;
}
else
{
lean_object* v_reuseFailAlloc_6172_; 
v_reuseFailAlloc_6172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6172_, 0, v_name_6151_);
lean_ctor_set(v_reuseFailAlloc_6172_, 1, v_defValue_6155_);
v___x_6168_ = v_reuseFailAlloc_6172_;
goto v_reusejp_6167_;
}
v_reusejp_6167_:
{
lean_object* v___x_6170_; 
if (v_isShared_6166_ == 0)
{
lean_ctor_set(v___x_6165_, 0, v___x_6168_);
v___x_6170_ = v___x_6165_;
goto v_reusejp_6169_;
}
else
{
lean_object* v_reuseFailAlloc_6171_; 
v_reuseFailAlloc_6171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6171_, 0, v___x_6168_);
v___x_6170_ = v_reuseFailAlloc_6171_;
goto v_reusejp_6169_;
}
v_reusejp_6169_:
{
return v___x_6170_;
}
}
}
}
else
{
lean_object* v_a_6175_; lean_object* v___x_6177_; uint8_t v_isShared_6178_; uint8_t v_isSharedCheck_6182_; 
lean_del_object(v___x_6158_);
lean_dec(v_defValue_6155_);
lean_dec(v_name_6151_);
v_a_6175_ = lean_ctor_get(v___x_6163_, 0);
v_isSharedCheck_6182_ = !lean_is_exclusive(v___x_6163_);
if (v_isSharedCheck_6182_ == 0)
{
v___x_6177_ = v___x_6163_;
v_isShared_6178_ = v_isSharedCheck_6182_;
goto v_resetjp_6176_;
}
else
{
lean_inc(v_a_6175_);
lean_dec(v___x_6163_);
v___x_6177_ = lean_box(0);
v_isShared_6178_ = v_isSharedCheck_6182_;
goto v_resetjp_6176_;
}
v_resetjp_6176_:
{
lean_object* v___x_6180_; 
if (v_isShared_6178_ == 0)
{
v___x_6180_ = v___x_6177_;
goto v_reusejp_6179_;
}
else
{
lean_object* v_reuseFailAlloc_6181_; 
v_reuseFailAlloc_6181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6181_, 0, v_a_6175_);
v___x_6180_ = v_reuseFailAlloc_6181_;
goto v_reusejp_6179_;
}
v_reusejp_6179_:
{
return v___x_6180_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_6184_, lean_object* v_decl_6185_, lean_object* v_ref_6186_, lean_object* v_a_6187_){
_start:
{
lean_object* v_res_6188_; 
v_res_6188_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4__spec__0(v_name_6184_, v_decl_6185_, v_ref_6186_);
return v_res_6188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_6202_; lean_object* v___x_6203_; lean_object* v___x_6204_; lean_object* v___x_6205_; 
v___x_6202_ = ((lean_object*)(l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4_));
v___x_6203_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4_));
v___x_6204_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4_));
v___x_6205_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4__spec__0(v___x_6202_, v___x_6203_, v___x_6204_);
return v___x_6205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4____boxed(lean_object* v_a_6206_){
_start:
{
lean_object* v_res_6207_; 
v_res_6207_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4_();
return v_res_6207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_SizeOf_3847602515____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_6221_; lean_object* v___x_6222_; lean_object* v___x_6223_; lean_object* v___x_6224_; 
v___x_6221_ = ((lean_object*)(l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_SizeOf_3847602515____hygCtx___hyg_4_));
v___x_6222_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_SizeOf_3847602515____hygCtx___hyg_4_));
v___x_6223_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_SizeOf_3847602515____hygCtx___hyg_4_));
v___x_6224_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4__spec__0(v___x_6221_, v___x_6222_, v___x_6223_);
return v___x_6224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_SizeOf_3847602515____hygCtx___hyg_4____boxed(lean_object* v_a_6225_){
_start:
{
lean_object* v_res_6226_; 
v_res_6226_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_SizeOf_3847602515____hygCtx___hyg_4_();
return v_res_6226_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_mkSizeOfInstances_spec__1(lean_object* v_opts_6227_, lean_object* v_opt_6228_){
_start:
{
lean_object* v_name_6229_; lean_object* v_defValue_6230_; lean_object* v_map_6231_; lean_object* v___x_6232_; 
v_name_6229_ = lean_ctor_get(v_opt_6228_, 0);
v_defValue_6230_ = lean_ctor_get(v_opt_6228_, 1);
v_map_6231_ = lean_ctor_get(v_opts_6227_, 0);
v___x_6232_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6231_, v_name_6229_);
if (lean_obj_tag(v___x_6232_) == 0)
{
uint8_t v___x_6233_; 
v___x_6233_ = lean_unbox(v_defValue_6230_);
return v___x_6233_;
}
else
{
lean_object* v_val_6234_; 
v_val_6234_ = lean_ctor_get(v___x_6232_, 0);
lean_inc(v_val_6234_);
lean_dec_ref(v___x_6232_);
if (lean_obj_tag(v_val_6234_) == 1)
{
uint8_t v_v_6235_; 
v_v_6235_ = lean_ctor_get_uint8(v_val_6234_, 0);
lean_dec_ref(v_val_6234_);
return v_v_6235_;
}
else
{
uint8_t v___x_6236_; 
lean_dec(v_val_6234_);
v___x_6236_ = lean_unbox(v_defValue_6230_);
return v___x_6236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_mkSizeOfInstances_spec__1___boxed(lean_object* v_opts_6237_, lean_object* v_opt_6238_){
_start:
{
uint8_t v_res_6239_; lean_object* v_r_6240_; 
v_res_6239_ = l_Lean_Option_get___at___00Lean_Meta_mkSizeOfInstances_spec__1(v_opts_6237_, v_opt_6238_);
lean_dec_ref(v_opt_6238_);
lean_dec_ref(v_opts_6237_);
v_r_6240_ = lean_box(v_res_6239_);
return v_r_6240_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_mkSizeOfInstances_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_6241_; lean_object* v___x_6242_; lean_object* v___x_6243_; 
v___x_6241_ = lean_unsigned_to_nat(32u);
v___x_6242_ = lean_mk_empty_array_with_capacity(v___x_6241_);
v___x_6243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6243_, 0, v___x_6242_);
return v___x_6243_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_mkSizeOfInstances_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_6244_; lean_object* v___x_6245_; lean_object* v___x_6246_; lean_object* v___x_6247_; lean_object* v___x_6248_; lean_object* v___x_6249_; 
v___x_6244_ = ((size_t)5ULL);
v___x_6245_ = lean_unsigned_to_nat(0u);
v___x_6246_ = lean_unsigned_to_nat(32u);
v___x_6247_ = lean_mk_empty_array_with_capacity(v___x_6246_);
v___x_6248_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_mkSizeOfInstances_spec__4___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_mkSizeOfInstances_spec__4___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_mkSizeOfInstances_spec__4___redArg___closed__0);
v___x_6249_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6249_, 0, v___x_6248_);
lean_ctor_set(v___x_6249_, 1, v___x_6247_);
lean_ctor_set(v___x_6249_, 2, v___x_6245_);
lean_ctor_set(v___x_6249_, 3, v___x_6245_);
lean_ctor_set_usize(v___x_6249_, 4, v___x_6244_);
return v___x_6249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_mkSizeOfInstances_spec__4___redArg(lean_object* v___y_6250_){
_start:
{
lean_object* v___x_6252_; lean_object* v_traceState_6253_; lean_object* v_traces_6254_; lean_object* v___x_6255_; lean_object* v_traceState_6256_; lean_object* v_env_6257_; lean_object* v_nextMacroScope_6258_; lean_object* v_ngen_6259_; lean_object* v_auxDeclNGen_6260_; lean_object* v_cache_6261_; lean_object* v_messages_6262_; lean_object* v_infoState_6263_; lean_object* v_snapshotTasks_6264_; lean_object* v___x_6266_; uint8_t v_isShared_6267_; uint8_t v_isSharedCheck_6283_; 
v___x_6252_ = lean_st_ref_get(v___y_6250_);
v_traceState_6253_ = lean_ctor_get(v___x_6252_, 4);
lean_inc_ref(v_traceState_6253_);
lean_dec(v___x_6252_);
v_traces_6254_ = lean_ctor_get(v_traceState_6253_, 0);
lean_inc_ref(v_traces_6254_);
lean_dec_ref(v_traceState_6253_);
v___x_6255_ = lean_st_ref_take(v___y_6250_);
v_traceState_6256_ = lean_ctor_get(v___x_6255_, 4);
v_env_6257_ = lean_ctor_get(v___x_6255_, 0);
v_nextMacroScope_6258_ = lean_ctor_get(v___x_6255_, 1);
v_ngen_6259_ = lean_ctor_get(v___x_6255_, 2);
v_auxDeclNGen_6260_ = lean_ctor_get(v___x_6255_, 3);
v_cache_6261_ = lean_ctor_get(v___x_6255_, 5);
v_messages_6262_ = lean_ctor_get(v___x_6255_, 6);
v_infoState_6263_ = lean_ctor_get(v___x_6255_, 7);
v_snapshotTasks_6264_ = lean_ctor_get(v___x_6255_, 8);
v_isSharedCheck_6283_ = !lean_is_exclusive(v___x_6255_);
if (v_isSharedCheck_6283_ == 0)
{
v___x_6266_ = v___x_6255_;
v_isShared_6267_ = v_isSharedCheck_6283_;
goto v_resetjp_6265_;
}
else
{
lean_inc(v_snapshotTasks_6264_);
lean_inc(v_infoState_6263_);
lean_inc(v_messages_6262_);
lean_inc(v_cache_6261_);
lean_inc(v_traceState_6256_);
lean_inc(v_auxDeclNGen_6260_);
lean_inc(v_ngen_6259_);
lean_inc(v_nextMacroScope_6258_);
lean_inc(v_env_6257_);
lean_dec(v___x_6255_);
v___x_6266_ = lean_box(0);
v_isShared_6267_ = v_isSharedCheck_6283_;
goto v_resetjp_6265_;
}
v_resetjp_6265_:
{
uint64_t v_tid_6268_; lean_object* v___x_6270_; uint8_t v_isShared_6271_; uint8_t v_isSharedCheck_6281_; 
v_tid_6268_ = lean_ctor_get_uint64(v_traceState_6256_, sizeof(void*)*1);
v_isSharedCheck_6281_ = !lean_is_exclusive(v_traceState_6256_);
if (v_isSharedCheck_6281_ == 0)
{
lean_object* v_unused_6282_; 
v_unused_6282_ = lean_ctor_get(v_traceState_6256_, 0);
lean_dec(v_unused_6282_);
v___x_6270_ = v_traceState_6256_;
v_isShared_6271_ = v_isSharedCheck_6281_;
goto v_resetjp_6269_;
}
else
{
lean_dec(v_traceState_6256_);
v___x_6270_ = lean_box(0);
v_isShared_6271_ = v_isSharedCheck_6281_;
goto v_resetjp_6269_;
}
v_resetjp_6269_:
{
lean_object* v___x_6272_; lean_object* v___x_6274_; 
v___x_6272_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_mkSizeOfInstances_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_mkSizeOfInstances_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_mkSizeOfInstances_spec__4___redArg___closed__1);
if (v_isShared_6271_ == 0)
{
lean_ctor_set(v___x_6270_, 0, v___x_6272_);
v___x_6274_ = v___x_6270_;
goto v_reusejp_6273_;
}
else
{
lean_object* v_reuseFailAlloc_6280_; 
v_reuseFailAlloc_6280_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6280_, 0, v___x_6272_);
lean_ctor_set_uint64(v_reuseFailAlloc_6280_, sizeof(void*)*1, v_tid_6268_);
v___x_6274_ = v_reuseFailAlloc_6280_;
goto v_reusejp_6273_;
}
v_reusejp_6273_:
{
lean_object* v___x_6276_; 
if (v_isShared_6267_ == 0)
{
lean_ctor_set(v___x_6266_, 4, v___x_6274_);
v___x_6276_ = v___x_6266_;
goto v_reusejp_6275_;
}
else
{
lean_object* v_reuseFailAlloc_6279_; 
v_reuseFailAlloc_6279_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6279_, 0, v_env_6257_);
lean_ctor_set(v_reuseFailAlloc_6279_, 1, v_nextMacroScope_6258_);
lean_ctor_set(v_reuseFailAlloc_6279_, 2, v_ngen_6259_);
lean_ctor_set(v_reuseFailAlloc_6279_, 3, v_auxDeclNGen_6260_);
lean_ctor_set(v_reuseFailAlloc_6279_, 4, v___x_6274_);
lean_ctor_set(v_reuseFailAlloc_6279_, 5, v_cache_6261_);
lean_ctor_set(v_reuseFailAlloc_6279_, 6, v_messages_6262_);
lean_ctor_set(v_reuseFailAlloc_6279_, 7, v_infoState_6263_);
lean_ctor_set(v_reuseFailAlloc_6279_, 8, v_snapshotTasks_6264_);
v___x_6276_ = v_reuseFailAlloc_6279_;
goto v_reusejp_6275_;
}
v_reusejp_6275_:
{
lean_object* v___x_6277_; lean_object* v___x_6278_; 
v___x_6277_ = lean_st_ref_set(v___y_6250_, v___x_6276_);
v___x_6278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6278_, 0, v_traces_6254_);
return v___x_6278_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_mkSizeOfInstances_spec__4___redArg___boxed(lean_object* v___y_6284_, lean_object* v___y_6285_){
_start:
{
lean_object* v_res_6286_; 
v_res_6286_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_mkSizeOfInstances_spec__4___redArg(v___y_6284_);
lean_dec(v___y_6284_);
return v_res_6286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_mkSizeOfInstances_spec__4(lean_object* v___y_6287_, lean_object* v___y_6288_, lean_object* v___y_6289_, lean_object* v___y_6290_){
_start:
{
lean_object* v___x_6292_; 
v___x_6292_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_mkSizeOfInstances_spec__4___redArg(v___y_6290_);
return v___x_6292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_mkSizeOfInstances_spec__4___boxed(lean_object* v___y_6293_, lean_object* v___y_6294_, lean_object* v___y_6295_, lean_object* v___y_6296_, lean_object* v___y_6297_){
_start:
{
lean_object* v_res_6298_; 
v_res_6298_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_mkSizeOfInstances_spec__4(v___y_6293_, v___y_6294_, v___y_6295_, v___y_6296_);
lean_dec(v___y_6296_);
lean_dec_ref(v___y_6295_);
lean_dec(v___y_6294_);
lean_dec_ref(v___y_6293_);
return v_res_6298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfInstances___lam__0(lean_object* v_typeName_6299_, lean_object* v_x_6300_, lean_object* v___y_6301_, lean_object* v___y_6302_, lean_object* v___y_6303_, lean_object* v___y_6304_){
_start:
{
lean_object* v___x_6306_; lean_object* v___x_6307_; 
v___x_6306_ = l_Lean_MessageData_ofName(v_typeName_6299_);
v___x_6307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6307_, 0, v___x_6306_);
return v___x_6307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfInstances___lam__0___boxed(lean_object* v_typeName_6308_, lean_object* v_x_6309_, lean_object* v___y_6310_, lean_object* v___y_6311_, lean_object* v___y_6312_, lean_object* v___y_6313_, lean_object* v___y_6314_){
_start:
{
lean_object* v_res_6315_; 
v_res_6315_ = l_Lean_Meta_mkSizeOfInstances___lam__0(v_typeName_6308_, v_x_6309_, v___y_6310_, v___y_6311_, v___y_6312_, v___y_6313_);
lean_dec(v___y_6313_);
lean_dec_ref(v___y_6312_);
lean_dec(v___y_6311_);
lean_dec_ref(v___y_6310_);
lean_dec_ref(v_x_6309_);
return v_res_6315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfInstances___lam__1(lean_object* v___x_6316_, lean_object* v_e_6317_){
_start:
{
lean_object* v___x_6318_; lean_object* v___x_6319_; 
v___x_6318_ = l_Lean_indentD(v_e_6317_);
v___x_6319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6319_, 0, v___x_6316_);
lean_ctor_set(v___x_6319_, 1, v___x_6318_);
return v___x_6319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSizeOfInstances_spec__2___redArg(lean_object* v_name_6320_, lean_object* v_type_6321_, lean_object* v_k_6322_, lean_object* v___y_6323_, lean_object* v___y_6324_, lean_object* v___y_6325_, lean_object* v___y_6326_){
_start:
{
uint8_t v___x_6328_; uint8_t v___x_6329_; lean_object* v___x_6330_; 
v___x_6328_ = 0;
v___x_6329_ = 0;
v___x_6330_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__1___redArg(v_name_6320_, v___x_6328_, v_type_6321_, v_k_6322_, v___x_6329_, v___y_6323_, v___y_6324_, v___y_6325_, v___y_6326_);
return v___x_6330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSizeOfInstances_spec__2___redArg___boxed(lean_object* v_name_6331_, lean_object* v_type_6332_, lean_object* v_k_6333_, lean_object* v___y_6334_, lean_object* v___y_6335_, lean_object* v___y_6336_, lean_object* v___y_6337_, lean_object* v___y_6338_){
_start:
{
lean_object* v_res_6339_; 
v_res_6339_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSizeOfInstances_spec__2___redArg(v_name_6331_, v_type_6332_, v_k_6333_, v___y_6334_, v___y_6335_, v___y_6336_, v___y_6337_);
lean_dec(v___y_6337_);
lean_dec_ref(v___y_6336_);
lean_dec(v___y_6335_);
lean_dec_ref(v___y_6334_);
return v_res_6339_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__0(lean_object* v___x_6340_, uint8_t v___x_6341_, lean_object* v___y_6342_, lean_object* v___y_6343_, lean_object* v___y_6344_, lean_object* v___y_6345_){
_start:
{
lean_object* v___x_6347_; 
v___x_6347_ = l_Lean_addDecl(v___x_6340_, v___x_6341_, v___y_6344_, v___y_6345_);
return v___x_6347_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__0___boxed(lean_object* v___x_6348_, lean_object* v___x_6349_, lean_object* v___y_6350_, lean_object* v___y_6351_, lean_object* v___y_6352_, lean_object* v___y_6353_, lean_object* v___y_6354_){
_start:
{
uint8_t v___x_17753__boxed_6355_; lean_object* v_res_6356_; 
v___x_17753__boxed_6355_ = lean_unbox(v___x_6349_);
v_res_6356_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__0(v___x_6348_, v___x_17753__boxed_6355_, v___y_6350_, v___y_6351_, v___y_6352_, v___y_6353_);
lean_dec(v___y_6353_);
lean_dec_ref(v___y_6352_);
lean_dec(v___y_6351_);
lean_dec_ref(v___y_6350_);
return v_res_6356_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__1___closed__2(void){
_start:
{
lean_object* v___x_6359_; lean_object* v___x_6360_; 
v___x_6359_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__1___closed__1));
v___x_6360_ = l_Lean_stringToMessageData(v___x_6359_);
return v___x_6360_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__1___closed__4(void){
_start:
{
lean_object* v___x_6362_; lean_object* v___x_6363_; 
v___x_6362_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__1___closed__3));
v___x_6363_ = l_Lean_stringToMessageData(v___x_6362_);
return v___x_6363_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__1(lean_object* v___x_6364_, lean_object* v___x_6365_, lean_object* v___x_6366_, lean_object* v___x_6367_, lean_object* v_localInsts_6368_, lean_object* v___x_6369_, uint8_t v___x_6370_, uint8_t v___x_6371_, lean_object* v___x_6372_, lean_object* v_xs_6373_, lean_object* v_a_6374_, lean_object* v___x_6375_, lean_object* v_head_6376_, lean_object* v_levelParams_6377_, lean_object* v_m_6378_, lean_object* v___y_6379_, lean_object* v___y_6380_, lean_object* v___y_6381_, lean_object* v___y_6382_){
_start:
{
lean_object* v___x_6384_; lean_object* v___x_6385_; lean_object* v___x_6386_; lean_object* v___x_6387_; lean_object* v___x_6388_; lean_object* v___x_6389_; lean_object* v___x_6390_; uint8_t v___x_6391_; lean_object* v___x_6392_; 
lean_inc_ref(v___x_6364_);
v___x_6384_ = lean_array_push(v___x_6364_, v_m_6378_);
v___x_6385_ = l_Lean_mkConst(v___x_6365_, v___x_6366_);
v___x_6386_ = l_Array_append___redArg(v___x_6367_, v_localInsts_6368_);
v___x_6387_ = l_Subarray_copy___redArg(v___x_6369_);
v___x_6388_ = l_Array_append___redArg(v___x_6386_, v___x_6387_);
lean_dec_ref(v___x_6387_);
v___x_6389_ = l_Array_append___redArg(v___x_6388_, v___x_6384_);
v___x_6390_ = l_Lean_mkAppN(v___x_6385_, v___x_6389_);
lean_dec_ref(v___x_6389_);
v___x_6391_ = 1;
v___x_6392_ = l_Lean_Meta_mkLambdaFVars(v___x_6384_, v___x_6390_, v___x_6370_, v___x_6371_, v___x_6370_, v___x_6371_, v___x_6391_, v___y_6379_, v___y_6380_, v___y_6381_, v___y_6382_);
lean_dec_ref(v___x_6384_);
if (lean_obj_tag(v___x_6392_) == 0)
{
lean_object* v_a_6393_; lean_object* v___x_6394_; lean_object* v___x_6395_; lean_object* v___x_6396_; lean_object* v___x_6397_; 
v_a_6393_ = lean_ctor_get(v___x_6392_, 0);
lean_inc(v_a_6393_);
lean_dec_ref(v___x_6392_);
v___x_6394_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__1___closed__0));
v___x_6395_ = l_Lean_Name_mkStr2(v___x_6372_, v___x_6394_);
v___x_6396_ = lean_array_push(v___x_6364_, v_a_6393_);
v___x_6397_ = l_Lean_Meta_mkAppM(v___x_6395_, v___x_6396_, v___y_6379_, v___y_6380_, v___y_6381_, v___y_6382_);
if (lean_obj_tag(v___x_6397_) == 0)
{
lean_object* v_a_6398_; lean_object* v___x_6399_; lean_object* v___x_6400_; 
v_a_6398_ = lean_ctor_get(v___x_6397_, 0);
lean_inc(v_a_6398_);
lean_dec_ref(v___x_6397_);
v___x_6399_ = l_Array_append___redArg(v_xs_6373_, v_localInsts_6368_);
v___x_6400_ = l_Lean_Meta_mkForallFVars(v___x_6399_, v_a_6374_, v___x_6370_, v___x_6371_, v___x_6371_, v___x_6391_, v___y_6379_, v___y_6380_, v___y_6381_, v___y_6382_);
if (lean_obj_tag(v___x_6400_) == 0)
{
lean_object* v_a_6401_; lean_object* v___x_6402_; 
v_a_6401_ = lean_ctor_get(v___x_6400_, 0);
lean_inc(v_a_6401_);
lean_dec_ref(v___x_6400_);
v___x_6402_ = l_Lean_Meta_mkLambdaFVars(v___x_6399_, v_a_6398_, v___x_6370_, v___x_6371_, v___x_6370_, v___x_6371_, v___x_6391_, v___y_6379_, v___y_6380_, v___y_6381_, v___y_6382_);
lean_dec_ref(v___x_6399_);
if (lean_obj_tag(v___x_6402_) == 0)
{
lean_object* v_a_6403_; lean_object* v___x_6404_; lean_object* v_a_6405_; lean_object* v___x_6407_; uint8_t v_isShared_6408_; uint8_t v_isSharedCheck_6441_; 
v_a_6403_ = lean_ctor_get(v___x_6402_, 0);
lean_inc(v_a_6403_);
lean_dec_ref(v___x_6402_);
lean_inc(v___x_6375_);
v___x_6404_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__0___redArg(v___x_6375_, v___y_6381_);
v_a_6405_ = lean_ctor_get(v___x_6404_, 0);
v_isSharedCheck_6441_ = !lean_is_exclusive(v___x_6404_);
if (v_isSharedCheck_6441_ == 0)
{
v___x_6407_ = v___x_6404_;
v_isShared_6408_ = v_isSharedCheck_6441_;
goto v_resetjp_6406_;
}
else
{
lean_inc(v_a_6405_);
lean_dec(v___x_6404_);
v___x_6407_ = lean_box(0);
v_isShared_6408_ = v_isSharedCheck_6441_;
goto v_resetjp_6406_;
}
v_resetjp_6406_:
{
lean_object* v___x_6409_; lean_object* v___x_6410_; lean_object* v___y_6412_; lean_object* v___y_6413_; lean_object* v___y_6414_; lean_object* v___y_6415_; uint8_t v___x_6432_; 
v___x_6409_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorem___lam__0___closed__9));
v___x_6410_ = l_Lean_Name_append(v_head_6376_, v___x_6409_);
v___x_6432_ = lean_unbox(v_a_6405_);
lean_dec(v_a_6405_);
if (v___x_6432_ == 0)
{
lean_dec(v___x_6375_);
v___y_6412_ = v___y_6379_;
v___y_6413_ = v___y_6380_;
v___y_6414_ = v___y_6381_;
v___y_6415_ = v___y_6382_;
goto v___jp_6411_;
}
else
{
lean_object* v___x_6433_; lean_object* v___x_6434_; lean_object* v___x_6435_; lean_object* v___x_6436_; lean_object* v___x_6437_; lean_object* v___x_6438_; lean_object* v___x_6439_; lean_object* v___x_6440_; 
v___x_6433_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__1___closed__2, &l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__1___closed__2_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__1___closed__2);
lean_inc(v___x_6410_);
v___x_6434_ = l_Lean_MessageData_ofName(v___x_6410_);
v___x_6435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6435_, 0, v___x_6433_);
lean_ctor_set(v___x_6435_, 1, v___x_6434_);
v___x_6436_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__1___closed__4, &l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__1___closed__4_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__1___closed__4);
v___x_6437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6437_, 0, v___x_6435_);
lean_ctor_set(v___x_6437_, 1, v___x_6436_);
lean_inc(v_a_6401_);
v___x_6438_ = l_Lean_MessageData_ofExpr(v_a_6401_);
v___x_6439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6439_, 0, v___x_6437_);
lean_ctor_set(v___x_6439_, 1, v___x_6438_);
v___x_6440_ = l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1(v___x_6375_, v___x_6439_, v___y_6379_, v___y_6380_, v___y_6381_, v___y_6382_);
if (lean_obj_tag(v___x_6440_) == 0)
{
lean_dec_ref(v___x_6440_);
v___y_6412_ = v___y_6379_;
v___y_6413_ = v___y_6380_;
v___y_6414_ = v___y_6381_;
v___y_6415_ = v___y_6382_;
goto v___jp_6411_;
}
else
{
lean_dec(v___x_6410_);
lean_del_object(v___x_6407_);
lean_dec(v_a_6403_);
lean_dec(v_a_6401_);
lean_dec(v_levelParams_6377_);
return v___x_6440_;
}
}
v___jp_6411_:
{
lean_object* v___x_6416_; lean_object* v___x_6417_; uint8_t v___x_6418_; lean_object* v___x_6419_; lean_object* v___x_6420_; lean_object* v___x_6421_; lean_object* v___x_6423_; 
lean_inc(v___x_6410_);
v___x_6416_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6416_, 0, v___x_6410_);
lean_ctor_set(v___x_6416_, 1, v_levelParams_6377_);
lean_ctor_set(v___x_6416_, 2, v_a_6401_);
v___x_6417_ = lean_box(1);
v___x_6418_ = 1;
v___x_6419_ = lean_box(0);
lean_inc(v___x_6410_);
v___x_6420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6420_, 0, v___x_6410_);
lean_ctor_set(v___x_6420_, 1, v___x_6419_);
v___x_6421_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_6421_, 0, v___x_6416_);
lean_ctor_set(v___x_6421_, 1, v_a_6403_);
lean_ctor_set(v___x_6421_, 2, v___x_6417_);
lean_ctor_set(v___x_6421_, 3, v___x_6420_);
lean_ctor_set_uint8(v___x_6421_, sizeof(void*)*4, v___x_6418_);
if (v_isShared_6408_ == 0)
{
lean_ctor_set_tag(v___x_6407_, 1);
lean_ctor_set(v___x_6407_, 0, v___x_6421_);
v___x_6423_ = v___x_6407_;
goto v_reusejp_6422_;
}
else
{
lean_object* v_reuseFailAlloc_6431_; 
v_reuseFailAlloc_6431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6431_, 0, v___x_6421_);
v___x_6423_ = v_reuseFailAlloc_6431_;
goto v_reusejp_6422_;
}
v_reusejp_6422_:
{
lean_object* v___x_6424_; lean_object* v___f_6425_; lean_object* v___x_6426_; 
v___x_6424_ = lean_box(v___x_6370_);
v___f_6425_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_6425_, 0, v___x_6423_);
lean_closure_set(v___f_6425_, 1, v___x_6424_);
v___x_6426_ = l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg(v___f_6425_, v___x_6371_, v___y_6412_, v___y_6413_, v___y_6414_, v___y_6415_);
if (lean_obj_tag(v___x_6426_) == 0)
{
uint8_t v___x_6427_; lean_object* v___x_6428_; lean_object* v___x_6429_; 
lean_dec_ref(v___x_6426_);
v___x_6427_ = 0;
v___x_6428_ = lean_unsigned_to_nat(1000u);
lean_inc(v___x_6410_);
v___x_6429_ = l_Lean_Meta_registerInstance(v___x_6410_, v___x_6427_, v___x_6428_, v___y_6412_, v___y_6413_, v___y_6414_, v___y_6415_);
if (lean_obj_tag(v___x_6429_) == 0)
{
lean_object* v___x_6430_; 
lean_dec_ref(v___x_6429_);
lean_inc_ref(v___y_6414_);
v___x_6430_ = l_Lean_enableRealizationsForConst(v___x_6410_, v___y_6414_, v___y_6415_);
return v___x_6430_;
}
else
{
lean_dec(v___x_6410_);
return v___x_6429_;
}
}
else
{
lean_dec(v___x_6410_);
return v___x_6426_;
}
}
}
}
}
else
{
lean_object* v_a_6442_; lean_object* v___x_6444_; uint8_t v_isShared_6445_; uint8_t v_isSharedCheck_6449_; 
lean_dec(v_a_6401_);
lean_dec(v_levelParams_6377_);
lean_dec(v_head_6376_);
lean_dec(v___x_6375_);
v_a_6442_ = lean_ctor_get(v___x_6402_, 0);
v_isSharedCheck_6449_ = !lean_is_exclusive(v___x_6402_);
if (v_isSharedCheck_6449_ == 0)
{
v___x_6444_ = v___x_6402_;
v_isShared_6445_ = v_isSharedCheck_6449_;
goto v_resetjp_6443_;
}
else
{
lean_inc(v_a_6442_);
lean_dec(v___x_6402_);
v___x_6444_ = lean_box(0);
v_isShared_6445_ = v_isSharedCheck_6449_;
goto v_resetjp_6443_;
}
v_resetjp_6443_:
{
lean_object* v___x_6447_; 
if (v_isShared_6445_ == 0)
{
v___x_6447_ = v___x_6444_;
goto v_reusejp_6446_;
}
else
{
lean_object* v_reuseFailAlloc_6448_; 
v_reuseFailAlloc_6448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6448_, 0, v_a_6442_);
v___x_6447_ = v_reuseFailAlloc_6448_;
goto v_reusejp_6446_;
}
v_reusejp_6446_:
{
return v___x_6447_;
}
}
}
}
else
{
lean_object* v_a_6450_; lean_object* v___x_6452_; uint8_t v_isShared_6453_; uint8_t v_isSharedCheck_6457_; 
lean_dec_ref(v___x_6399_);
lean_dec(v_a_6398_);
lean_dec(v_levelParams_6377_);
lean_dec(v_head_6376_);
lean_dec(v___x_6375_);
v_a_6450_ = lean_ctor_get(v___x_6400_, 0);
v_isSharedCheck_6457_ = !lean_is_exclusive(v___x_6400_);
if (v_isSharedCheck_6457_ == 0)
{
v___x_6452_ = v___x_6400_;
v_isShared_6453_ = v_isSharedCheck_6457_;
goto v_resetjp_6451_;
}
else
{
lean_inc(v_a_6450_);
lean_dec(v___x_6400_);
v___x_6452_ = lean_box(0);
v_isShared_6453_ = v_isSharedCheck_6457_;
goto v_resetjp_6451_;
}
v_resetjp_6451_:
{
lean_object* v___x_6455_; 
if (v_isShared_6453_ == 0)
{
v___x_6455_ = v___x_6452_;
goto v_reusejp_6454_;
}
else
{
lean_object* v_reuseFailAlloc_6456_; 
v_reuseFailAlloc_6456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6456_, 0, v_a_6450_);
v___x_6455_ = v_reuseFailAlloc_6456_;
goto v_reusejp_6454_;
}
v_reusejp_6454_:
{
return v___x_6455_;
}
}
}
}
else
{
lean_object* v_a_6458_; lean_object* v___x_6460_; uint8_t v_isShared_6461_; uint8_t v_isSharedCheck_6465_; 
lean_dec(v_levelParams_6377_);
lean_dec(v_head_6376_);
lean_dec(v___x_6375_);
lean_dec_ref(v_a_6374_);
lean_dec_ref(v_xs_6373_);
v_a_6458_ = lean_ctor_get(v___x_6397_, 0);
v_isSharedCheck_6465_ = !lean_is_exclusive(v___x_6397_);
if (v_isSharedCheck_6465_ == 0)
{
v___x_6460_ = v___x_6397_;
v_isShared_6461_ = v_isSharedCheck_6465_;
goto v_resetjp_6459_;
}
else
{
lean_inc(v_a_6458_);
lean_dec(v___x_6397_);
v___x_6460_ = lean_box(0);
v_isShared_6461_ = v_isSharedCheck_6465_;
goto v_resetjp_6459_;
}
v_resetjp_6459_:
{
lean_object* v___x_6463_; 
if (v_isShared_6461_ == 0)
{
v___x_6463_ = v___x_6460_;
goto v_reusejp_6462_;
}
else
{
lean_object* v_reuseFailAlloc_6464_; 
v_reuseFailAlloc_6464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6464_, 0, v_a_6458_);
v___x_6463_ = v_reuseFailAlloc_6464_;
goto v_reusejp_6462_;
}
v_reusejp_6462_:
{
return v___x_6463_;
}
}
}
}
else
{
lean_object* v_a_6466_; lean_object* v___x_6468_; uint8_t v_isShared_6469_; uint8_t v_isSharedCheck_6473_; 
lean_dec(v_levelParams_6377_);
lean_dec(v_head_6376_);
lean_dec(v___x_6375_);
lean_dec_ref(v_a_6374_);
lean_dec_ref(v_xs_6373_);
lean_dec_ref(v___x_6372_);
lean_dec_ref(v___x_6364_);
v_a_6466_ = lean_ctor_get(v___x_6392_, 0);
v_isSharedCheck_6473_ = !lean_is_exclusive(v___x_6392_);
if (v_isSharedCheck_6473_ == 0)
{
v___x_6468_ = v___x_6392_;
v_isShared_6469_ = v_isSharedCheck_6473_;
goto v_resetjp_6467_;
}
else
{
lean_inc(v_a_6466_);
lean_dec(v___x_6392_);
v___x_6468_ = lean_box(0);
v_isShared_6469_ = v_isSharedCheck_6473_;
goto v_resetjp_6467_;
}
v_resetjp_6467_:
{
lean_object* v___x_6471_; 
if (v_isShared_6469_ == 0)
{
v___x_6471_ = v___x_6468_;
goto v_reusejp_6470_;
}
else
{
lean_object* v_reuseFailAlloc_6472_; 
v_reuseFailAlloc_6472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6472_, 0, v_a_6466_);
v___x_6471_ = v_reuseFailAlloc_6472_;
goto v_reusejp_6470_;
}
v_reusejp_6470_:
{
return v___x_6471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_6474_ = _args[0];
lean_object* v___x_6475_ = _args[1];
lean_object* v___x_6476_ = _args[2];
lean_object* v___x_6477_ = _args[3];
lean_object* v_localInsts_6478_ = _args[4];
lean_object* v___x_6479_ = _args[5];
lean_object* v___x_6480_ = _args[6];
lean_object* v___x_6481_ = _args[7];
lean_object* v___x_6482_ = _args[8];
lean_object* v_xs_6483_ = _args[9];
lean_object* v_a_6484_ = _args[10];
lean_object* v___x_6485_ = _args[11];
lean_object* v_head_6486_ = _args[12];
lean_object* v_levelParams_6487_ = _args[13];
lean_object* v_m_6488_ = _args[14];
lean_object* v___y_6489_ = _args[15];
lean_object* v___y_6490_ = _args[16];
lean_object* v___y_6491_ = _args[17];
lean_object* v___y_6492_ = _args[18];
lean_object* v___y_6493_ = _args[19];
_start:
{
uint8_t v___x_17797__boxed_6494_; uint8_t v___x_17798__boxed_6495_; lean_object* v_res_6496_; 
v___x_17797__boxed_6494_ = lean_unbox(v___x_6480_);
v___x_17798__boxed_6495_ = lean_unbox(v___x_6481_);
v_res_6496_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__1(v___x_6474_, v___x_6475_, v___x_6476_, v___x_6477_, v_localInsts_6478_, v___x_6479_, v___x_17797__boxed_6494_, v___x_17798__boxed_6495_, v___x_6482_, v_xs_6483_, v_a_6484_, v___x_6485_, v_head_6486_, v_levelParams_6487_, v_m_6488_, v___y_6489_, v___y_6490_, v___y_6491_, v___y_6492_);
lean_dec(v___y_6492_);
lean_dec_ref(v___y_6491_);
lean_dec(v___y_6490_);
lean_dec_ref(v___y_6489_);
lean_dec_ref(v_localInsts_6478_);
return v_res_6496_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__2(lean_object* v_levelParams_6500_, lean_object* v_head_6501_, lean_object* v_xs_6502_, lean_object* v___x_6503_, lean_object* v___x_6504_, lean_object* v___x_6505_, lean_object* v___x_6506_, uint8_t v___x_6507_, uint8_t v___x_6508_, lean_object* v___x_6509_, lean_object* v___x_6510_, lean_object* v_localInsts_6511_, lean_object* v___y_6512_, lean_object* v___y_6513_, lean_object* v___y_6514_, lean_object* v___y_6515_){
_start:
{
lean_object* v___x_6517_; lean_object* v___x_6518_; lean_object* v___x_6519_; lean_object* v___x_6520_; lean_object* v___x_6521_; lean_object* v___x_6522_; lean_object* v___x_6523_; lean_object* v___x_6524_; 
v___x_6517_ = lean_box(0);
lean_inc(v_levelParams_6500_);
v___x_6518_ = l_List_mapTR_loop___at___00Lean_Meta_mkSizeOfFn_spec__1(v_levelParams_6500_, v___x_6517_);
lean_inc(v___x_6518_);
lean_inc(v_head_6501_);
v___x_6519_ = l_Lean_mkConst(v_head_6501_, v___x_6518_);
v___x_6520_ = l_Lean_mkAppN(v___x_6519_, v_xs_6502_);
v___x_6521_ = lean_unsigned_to_nat(1u);
v___x_6522_ = lean_mk_empty_array_with_capacity(v___x_6521_);
lean_inc_ref(v___x_6520_);
lean_inc_ref(v___x_6522_);
v___x_6523_ = lean_array_push(v___x_6522_, v___x_6520_);
v___x_6524_ = l_Lean_Meta_mkAppM(v___x_6503_, v___x_6523_, v___y_6512_, v___y_6513_, v___y_6514_, v___y_6515_);
if (lean_obj_tag(v___x_6524_) == 0)
{
lean_object* v_a_6525_; lean_object* v___x_6526_; lean_object* v___x_6527_; lean_object* v___f_6528_; lean_object* v___x_6529_; lean_object* v___x_6530_; 
v_a_6525_ = lean_ctor_get(v___x_6524_, 0);
lean_inc(v_a_6525_);
lean_dec_ref(v___x_6524_);
v___x_6526_ = lean_box(v___x_6507_);
v___x_6527_ = lean_box(v___x_6508_);
v___f_6528_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__1___boxed), 20, 14);
lean_closure_set(v___f_6528_, 0, v___x_6522_);
lean_closure_set(v___f_6528_, 1, v___x_6504_);
lean_closure_set(v___f_6528_, 2, v___x_6518_);
lean_closure_set(v___f_6528_, 3, v___x_6505_);
lean_closure_set(v___f_6528_, 4, v_localInsts_6511_);
lean_closure_set(v___f_6528_, 5, v___x_6506_);
lean_closure_set(v___f_6528_, 6, v___x_6526_);
lean_closure_set(v___f_6528_, 7, v___x_6527_);
lean_closure_set(v___f_6528_, 8, v___x_6509_);
lean_closure_set(v___f_6528_, 9, v_xs_6502_);
lean_closure_set(v___f_6528_, 10, v_a_6525_);
lean_closure_set(v___f_6528_, 11, v___x_6510_);
lean_closure_set(v___f_6528_, 12, v_head_6501_);
lean_closure_set(v___f_6528_, 13, v_levelParams_6500_);
v___x_6529_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__2___closed__1));
v___x_6530_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSizeOfInstances_spec__2___redArg(v___x_6529_, v___x_6520_, v___f_6528_, v___y_6512_, v___y_6513_, v___y_6514_, v___y_6515_);
return v___x_6530_;
}
else
{
lean_object* v_a_6531_; lean_object* v___x_6533_; uint8_t v_isShared_6534_; uint8_t v_isSharedCheck_6538_; 
lean_dec_ref(v___x_6522_);
lean_dec_ref(v___x_6520_);
lean_dec(v___x_6518_);
lean_dec_ref(v_localInsts_6511_);
lean_dec(v___x_6510_);
lean_dec_ref(v___x_6509_);
lean_dec_ref(v___x_6506_);
lean_dec_ref(v___x_6505_);
lean_dec(v___x_6504_);
lean_dec_ref(v_xs_6502_);
lean_dec(v_head_6501_);
lean_dec(v_levelParams_6500_);
v_a_6531_ = lean_ctor_get(v___x_6524_, 0);
v_isSharedCheck_6538_ = !lean_is_exclusive(v___x_6524_);
if (v_isSharedCheck_6538_ == 0)
{
v___x_6533_ = v___x_6524_;
v_isShared_6534_ = v_isSharedCheck_6538_;
goto v_resetjp_6532_;
}
else
{
lean_inc(v_a_6531_);
lean_dec(v___x_6524_);
v___x_6533_ = lean_box(0);
v_isShared_6534_ = v_isSharedCheck_6538_;
goto v_resetjp_6532_;
}
v_resetjp_6532_:
{
lean_object* v___x_6536_; 
if (v_isShared_6534_ == 0)
{
v___x_6536_ = v___x_6533_;
goto v_reusejp_6535_;
}
else
{
lean_object* v_reuseFailAlloc_6537_; 
v_reuseFailAlloc_6537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6537_, 0, v_a_6531_);
v___x_6536_ = v_reuseFailAlloc_6537_;
goto v_reusejp_6535_;
}
v_reusejp_6535_:
{
return v___x_6536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__2___boxed(lean_object** _args){
lean_object* v_levelParams_6539_ = _args[0];
lean_object* v_head_6540_ = _args[1];
lean_object* v_xs_6541_ = _args[2];
lean_object* v___x_6542_ = _args[3];
lean_object* v___x_6543_ = _args[4];
lean_object* v___x_6544_ = _args[5];
lean_object* v___x_6545_ = _args[6];
lean_object* v___x_6546_ = _args[7];
lean_object* v___x_6547_ = _args[8];
lean_object* v___x_6548_ = _args[9];
lean_object* v___x_6549_ = _args[10];
lean_object* v_localInsts_6550_ = _args[11];
lean_object* v___y_6551_ = _args[12];
lean_object* v___y_6552_ = _args[13];
lean_object* v___y_6553_ = _args[14];
lean_object* v___y_6554_ = _args[15];
lean_object* v___y_6555_ = _args[16];
_start:
{
uint8_t v___x_18045__boxed_6556_; uint8_t v___x_18046__boxed_6557_; lean_object* v_res_6558_; 
v___x_18045__boxed_6556_ = lean_unbox(v___x_6546_);
v___x_18046__boxed_6557_ = lean_unbox(v___x_6547_);
v_res_6558_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__2(v_levelParams_6539_, v_head_6540_, v_xs_6541_, v___x_6542_, v___x_6543_, v___x_6544_, v___x_6545_, v___x_18045__boxed_6556_, v___x_18046__boxed_6557_, v___x_6548_, v___x_6549_, v_localInsts_6550_, v___y_6551_, v___y_6552_, v___y_6553_, v___y_6554_);
lean_dec(v___y_6554_);
lean_dec_ref(v___y_6553_);
lean_dec(v___y_6552_);
lean_dec_ref(v___y_6551_);
return v_res_6558_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__3(lean_object* v_numParams_6559_, lean_object* v_levelParams_6560_, lean_object* v_head_6561_, lean_object* v___x_6562_, lean_object* v___x_6563_, uint8_t v___x_6564_, uint8_t v___x_6565_, lean_object* v___x_6566_, lean_object* v___x_6567_, lean_object* v_xs_6568_, lean_object* v_x_6569_, lean_object* v___y_6570_, lean_object* v___y_6571_, lean_object* v___y_6572_, lean_object* v___y_6573_){
_start:
{
lean_object* v___x_6575_; lean_object* v___x_6576_; lean_object* v___x_6577_; lean_object* v_lower_6579_; lean_object* v_upper_6580_; lean_object* v___x_6587_; uint8_t v___x_6588_; 
v___x_6575_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_6559_);
lean_inc_ref(v_xs_6568_);
v___x_6576_ = l_Array_toSubarray___redArg(v_xs_6568_, v___x_6575_, v_numParams_6559_);
v___x_6577_ = l_Subarray_copy___redArg(v___x_6576_);
v___x_6587_ = lean_array_get_size(v_xs_6568_);
v___x_6588_ = lean_nat_dec_le(v_numParams_6559_, v___x_6575_);
if (v___x_6588_ == 0)
{
v_lower_6579_ = v_numParams_6559_;
v_upper_6580_ = v___x_6587_;
goto v___jp_6578_;
}
else
{
lean_dec(v_numParams_6559_);
v_lower_6579_ = v___x_6575_;
v_upper_6580_ = v___x_6587_;
goto v___jp_6578_;
}
v___jp_6578_:
{
lean_object* v___x_6581_; lean_object* v___x_6582_; lean_object* v___x_6583_; lean_object* v___f_6584_; lean_object* v___x_6585_; lean_object* v___x_6586_; 
lean_inc_ref(v_xs_6568_);
v___x_6581_ = l_Array_toSubarray___redArg(v_xs_6568_, v_lower_6579_, v_upper_6580_);
v___x_6582_ = lean_box(v___x_6564_);
v___x_6583_ = lean_box(v___x_6565_);
lean_inc_ref(v___x_6577_);
v___f_6584_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__2___boxed), 17, 11);
lean_closure_set(v___f_6584_, 0, v_levelParams_6560_);
lean_closure_set(v___f_6584_, 1, v_head_6561_);
lean_closure_set(v___f_6584_, 2, v_xs_6568_);
lean_closure_set(v___f_6584_, 3, v___x_6562_);
lean_closure_set(v___f_6584_, 4, v___x_6563_);
lean_closure_set(v___f_6584_, 5, v___x_6577_);
lean_closure_set(v___f_6584_, 6, v___x_6581_);
lean_closure_set(v___f_6584_, 7, v___x_6582_);
lean_closure_set(v___f_6584_, 8, v___x_6583_);
lean_closure_set(v___f_6584_, 9, v___x_6566_);
lean_closure_set(v___f_6584_, 10, v___x_6567_);
lean_inc_ref(v___x_6577_);
v___x_6585_ = lean_alloc_closure((void*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances___boxed), 8, 3);
lean_closure_set(v___x_6585_, 0, lean_box(0));
lean_closure_set(v___x_6585_, 1, v___x_6577_);
lean_closure_set(v___x_6585_, 2, v___f_6584_);
v___x_6586_ = l_Lean_Meta_withInstImplicitAsImplicit___redArg(v___x_6577_, v___x_6585_, v___y_6570_, v___y_6571_, v___y_6572_, v___y_6573_);
lean_dec_ref(v___x_6577_);
return v___x_6586_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__3___boxed(lean_object* v_numParams_6589_, lean_object* v_levelParams_6590_, lean_object* v_head_6591_, lean_object* v___x_6592_, lean_object* v___x_6593_, lean_object* v___x_6594_, lean_object* v___x_6595_, lean_object* v___x_6596_, lean_object* v___x_6597_, lean_object* v_xs_6598_, lean_object* v_x_6599_, lean_object* v___y_6600_, lean_object* v___y_6601_, lean_object* v___y_6602_, lean_object* v___y_6603_, lean_object* v___y_6604_){
_start:
{
uint8_t v___x_18132__boxed_6605_; uint8_t v___x_18133__boxed_6606_; lean_object* v_res_6607_; 
v___x_18132__boxed_6605_ = lean_unbox(v___x_6594_);
v___x_18133__boxed_6606_ = lean_unbox(v___x_6595_);
v_res_6607_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__3(v_numParams_6589_, v_levelParams_6590_, v_head_6591_, v___x_6592_, v___x_6593_, v___x_18132__boxed_6605_, v___x_18133__boxed_6606_, v___x_6596_, v___x_6597_, v_xs_6598_, v_x_6599_, v___y_6600_, v___y_6601_, v___y_6602_, v___y_6603_);
lean_dec(v___y_6603_);
lean_dec_ref(v___y_6602_);
lean_dec(v___y_6601_);
lean_dec_ref(v___y_6600_);
lean_dec_ref(v_x_6599_);
return v_res_6607_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg(lean_object* v_as_x27_6608_, lean_object* v_b_6609_, lean_object* v___y_6610_, lean_object* v___y_6611_, lean_object* v___y_6612_, lean_object* v___y_6613_){
_start:
{
if (lean_obj_tag(v_as_x27_6608_) == 0)
{
lean_object* v___x_6615_; 
v___x_6615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6615_, 0, v_b_6609_);
return v___x_6615_;
}
else
{
lean_object* v_head_6616_; lean_object* v_tail_6617_; lean_object* v_array_6618_; lean_object* v_start_6619_; lean_object* v_stop_6620_; uint8_t v___x_6621_; 
v_head_6616_ = lean_ctor_get(v_as_x27_6608_, 0);
lean_inc(v_head_6616_);
v_tail_6617_ = lean_ctor_get(v_as_x27_6608_, 1);
lean_inc(v_tail_6617_);
lean_dec_ref(v_as_x27_6608_);
v_array_6618_ = lean_ctor_get(v_b_6609_, 0);
v_start_6619_ = lean_ctor_get(v_b_6609_, 1);
v_stop_6620_ = lean_ctor_get(v_b_6609_, 2);
v___x_6621_ = lean_nat_dec_lt(v_start_6619_, v_stop_6620_);
if (v___x_6621_ == 0)
{
lean_object* v___x_6622_; 
lean_dec(v_tail_6617_);
lean_dec(v_head_6616_);
v___x_6622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6622_, 0, v_b_6609_);
return v___x_6622_;
}
else
{
lean_object* v___x_6624_; uint8_t v_isShared_6625_; uint8_t v_isSharedCheck_6663_; 
lean_inc(v_stop_6620_);
lean_inc(v_start_6619_);
lean_inc_ref(v_array_6618_);
v_isSharedCheck_6663_ = !lean_is_exclusive(v_b_6609_);
if (v_isSharedCheck_6663_ == 0)
{
lean_object* v_unused_6664_; lean_object* v_unused_6665_; lean_object* v_unused_6666_; 
v_unused_6664_ = lean_ctor_get(v_b_6609_, 2);
lean_dec(v_unused_6664_);
v_unused_6665_ = lean_ctor_get(v_b_6609_, 1);
lean_dec(v_unused_6665_);
v_unused_6666_ = lean_ctor_get(v_b_6609_, 0);
lean_dec(v_unused_6666_);
v___x_6624_ = v_b_6609_;
v_isShared_6625_ = v_isSharedCheck_6663_;
goto v_resetjp_6623_;
}
else
{
lean_dec(v_b_6609_);
v___x_6624_ = lean_box(0);
v_isShared_6625_ = v_isSharedCheck_6663_;
goto v_resetjp_6623_;
}
v_resetjp_6623_:
{
lean_object* v___x_6626_; 
lean_inc(v_head_6616_);
v___x_6626_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSizeOfFns_spec__0(v_head_6616_, v___y_6610_, v___y_6611_, v___y_6612_, v___y_6613_);
if (lean_obj_tag(v___x_6626_) == 0)
{
lean_object* v_a_6627_; lean_object* v_toConstantVal_6628_; lean_object* v_numParams_6629_; lean_object* v_levelParams_6630_; lean_object* v_type_6631_; lean_object* v___x_6632_; lean_object* v___x_6633_; uint8_t v___x_6634_; lean_object* v___x_6635_; lean_object* v___x_6636_; lean_object* v___x_6637_; lean_object* v___x_6638_; lean_object* v___f_6639_; lean_object* v___x_6640_; 
v_a_6627_ = lean_ctor_get(v___x_6626_, 0);
lean_inc(v_a_6627_);
lean_dec_ref(v___x_6626_);
v_toConstantVal_6628_ = lean_ctor_get(v_a_6627_, 0);
lean_inc_ref(v_toConstantVal_6628_);
v_numParams_6629_ = lean_ctor_get(v_a_6627_, 1);
lean_inc(v_numParams_6629_);
lean_dec(v_a_6627_);
v_levelParams_6630_ = lean_ctor_get(v_toConstantVal_6628_, 1);
lean_inc(v_levelParams_6630_);
v_type_6631_ = lean_ctor_get(v_toConstantVal_6628_, 2);
lean_inc_ref(v_type_6631_);
lean_dec_ref(v_toConstantVal_6628_);
v___x_6632_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___lam__0___closed__0));
v___x_6633_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___lam__0___closed__1));
v___x_6634_ = 0;
v___x_6635_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__2));
v___x_6636_ = lean_array_fget_borrowed(v_array_6618_, v_start_6619_);
v___x_6637_ = lean_box(v___x_6634_);
v___x_6638_ = lean_box(v___x_6621_);
lean_inc(v___x_6636_);
v___f_6639_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___lam__3___boxed), 16, 9);
lean_closure_set(v___f_6639_, 0, v_numParams_6629_);
lean_closure_set(v___f_6639_, 1, v_levelParams_6630_);
lean_closure_set(v___f_6639_, 2, v_head_6616_);
lean_closure_set(v___f_6639_, 3, v___x_6633_);
lean_closure_set(v___f_6639_, 4, v___x_6636_);
lean_closure_set(v___f_6639_, 5, v___x_6637_);
lean_closure_set(v___f_6639_, 6, v___x_6638_);
lean_closure_set(v___f_6639_, 7, v___x_6632_);
lean_closure_set(v___f_6639_, 8, v___x_6635_);
v___x_6640_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop_spec__0___redArg(v_type_6631_, v___f_6639_, v___x_6634_, v___x_6634_, v___y_6610_, v___y_6611_, v___y_6612_, v___y_6613_);
if (lean_obj_tag(v___x_6640_) == 0)
{
lean_object* v___x_6641_; lean_object* v___x_6642_; lean_object* v___x_6644_; 
lean_dec_ref(v___x_6640_);
v___x_6641_ = lean_unsigned_to_nat(1u);
v___x_6642_ = lean_nat_add(v_start_6619_, v___x_6641_);
lean_dec(v_start_6619_);
if (v_isShared_6625_ == 0)
{
lean_ctor_set(v___x_6624_, 1, v___x_6642_);
v___x_6644_ = v___x_6624_;
goto v_reusejp_6643_;
}
else
{
lean_object* v_reuseFailAlloc_6646_; 
v_reuseFailAlloc_6646_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6646_, 0, v_array_6618_);
lean_ctor_set(v_reuseFailAlloc_6646_, 1, v___x_6642_);
lean_ctor_set(v_reuseFailAlloc_6646_, 2, v_stop_6620_);
v___x_6644_ = v_reuseFailAlloc_6646_;
goto v_reusejp_6643_;
}
v_reusejp_6643_:
{
v_as_x27_6608_ = v_tail_6617_;
v_b_6609_ = v___x_6644_;
goto _start;
}
}
else
{
lean_object* v_a_6647_; lean_object* v___x_6649_; uint8_t v_isShared_6650_; uint8_t v_isSharedCheck_6654_; 
lean_del_object(v___x_6624_);
lean_dec(v_stop_6620_);
lean_dec(v_start_6619_);
lean_dec_ref(v_array_6618_);
lean_dec(v_tail_6617_);
v_a_6647_ = lean_ctor_get(v___x_6640_, 0);
v_isSharedCheck_6654_ = !lean_is_exclusive(v___x_6640_);
if (v_isSharedCheck_6654_ == 0)
{
v___x_6649_ = v___x_6640_;
v_isShared_6650_ = v_isSharedCheck_6654_;
goto v_resetjp_6648_;
}
else
{
lean_inc(v_a_6647_);
lean_dec(v___x_6640_);
v___x_6649_ = lean_box(0);
v_isShared_6650_ = v_isSharedCheck_6654_;
goto v_resetjp_6648_;
}
v_resetjp_6648_:
{
lean_object* v___x_6652_; 
if (v_isShared_6650_ == 0)
{
v___x_6652_ = v___x_6649_;
goto v_reusejp_6651_;
}
else
{
lean_object* v_reuseFailAlloc_6653_; 
v_reuseFailAlloc_6653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6653_, 0, v_a_6647_);
v___x_6652_ = v_reuseFailAlloc_6653_;
goto v_reusejp_6651_;
}
v_reusejp_6651_:
{
return v___x_6652_;
}
}
}
}
else
{
lean_object* v_a_6655_; lean_object* v___x_6657_; uint8_t v_isShared_6658_; uint8_t v_isSharedCheck_6662_; 
lean_del_object(v___x_6624_);
lean_dec(v_stop_6620_);
lean_dec(v_start_6619_);
lean_dec_ref(v_array_6618_);
lean_dec(v_tail_6617_);
lean_dec(v_head_6616_);
v_a_6655_ = lean_ctor_get(v___x_6626_, 0);
v_isSharedCheck_6662_ = !lean_is_exclusive(v___x_6626_);
if (v_isSharedCheck_6662_ == 0)
{
v___x_6657_ = v___x_6626_;
v_isShared_6658_ = v_isSharedCheck_6662_;
goto v_resetjp_6656_;
}
else
{
lean_inc(v_a_6655_);
lean_dec(v___x_6626_);
v___x_6657_ = lean_box(0);
v_isShared_6658_ = v_isSharedCheck_6662_;
goto v_resetjp_6656_;
}
v_resetjp_6656_:
{
lean_object* v___x_6660_; 
if (v_isShared_6658_ == 0)
{
v___x_6660_ = v___x_6657_;
goto v_reusejp_6659_;
}
else
{
lean_object* v_reuseFailAlloc_6661_; 
v_reuseFailAlloc_6661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6661_, 0, v_a_6655_);
v___x_6660_ = v_reuseFailAlloc_6661_;
goto v_reusejp_6659_;
}
v_reusejp_6659_:
{
return v___x_6660_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg___boxed(lean_object* v_as_x27_6667_, lean_object* v_b_6668_, lean_object* v___y_6669_, lean_object* v___y_6670_, lean_object* v___y_6671_, lean_object* v___y_6672_, lean_object* v___y_6673_){
_start:
{
lean_object* v_res_6674_; 
v_res_6674_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg(v_as_x27_6667_, v_b_6668_, v___y_6669_, v___y_6670_, v___y_6671_, v___y_6672_);
lean_dec(v___y_6672_);
lean_dec_ref(v___y_6671_);
lean_dec(v___y_6670_);
lean_dec_ref(v___y_6669_);
return v_res_6674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfInstances___lam__2(uint8_t v_isUnsafe_6675_, lean_object* v_typeName_6676_, lean_object* v_all_6677_, lean_object* v___y_6678_, lean_object* v___y_6679_, lean_object* v___y_6680_, lean_object* v___y_6681_){
_start:
{
if (v_isUnsafe_6675_ == 0)
{
lean_object* v___x_6683_; 
v___x_6683_ = l_Lean_Meta_mkSizeOfFns(v_typeName_6676_, v___y_6678_, v___y_6679_, v___y_6680_, v___y_6681_);
if (lean_obj_tag(v___x_6683_) == 0)
{
lean_object* v_a_6684_; lean_object* v_fst_6685_; lean_object* v_snd_6686_; lean_object* v___x_6687_; lean_object* v___x_6688_; lean_object* v___x_6689_; lean_object* v___x_6690_; 
v_a_6684_ = lean_ctor_get(v___x_6683_, 0);
lean_inc(v_a_6684_);
lean_dec_ref(v___x_6683_);
v_fst_6685_ = lean_ctor_get(v_a_6684_, 0);
lean_inc(v_fst_6685_);
v_snd_6686_ = lean_ctor_get(v_a_6684_, 1);
lean_inc(v_snd_6686_);
lean_dec(v_a_6684_);
v___x_6687_ = lean_unsigned_to_nat(0u);
v___x_6688_ = lean_array_get_size(v_fst_6685_);
lean_inc(v_fst_6685_);
v___x_6689_ = l_Array_toSubarray___redArg(v_fst_6685_, v___x_6687_, v___x_6688_);
lean_inc(v_all_6677_);
v___x_6690_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg(v_all_6677_, v___x_6689_, v___y_6678_, v___y_6679_, v___y_6680_, v___y_6681_);
if (lean_obj_tag(v___x_6690_) == 0)
{
lean_object* v___x_6692_; uint8_t v_isShared_6693_; uint8_t v_isSharedCheck_6703_; 
v_isSharedCheck_6703_ = !lean_is_exclusive(v___x_6690_);
if (v_isSharedCheck_6703_ == 0)
{
lean_object* v_unused_6704_; 
v_unused_6704_ = lean_ctor_get(v___x_6690_, 0);
lean_dec(v_unused_6704_);
v___x_6692_ = v___x_6690_;
v_isShared_6693_ = v_isSharedCheck_6703_;
goto v_resetjp_6691_;
}
else
{
lean_dec(v___x_6690_);
v___x_6692_ = lean_box(0);
v_isShared_6693_ = v_isSharedCheck_6703_;
goto v_resetjp_6691_;
}
v_resetjp_6691_:
{
lean_object* v_options_6694_; lean_object* v___x_6695_; uint8_t v___x_6696_; 
v_options_6694_ = lean_ctor_get(v___y_6680_, 2);
v___x_6695_ = l_Lean_Meta_genSizeOfSpec;
v___x_6696_ = l_Lean_Option_get___at___00Lean_Meta_mkSizeOfInstances_spec__1(v_options_6694_, v___x_6695_);
if (v___x_6696_ == 0)
{
lean_object* v___x_6697_; lean_object* v___x_6699_; 
lean_dec(v_snd_6686_);
lean_dec(v_fst_6685_);
lean_dec(v_all_6677_);
v___x_6697_ = lean_box(0);
if (v_isShared_6693_ == 0)
{
lean_ctor_set(v___x_6692_, 0, v___x_6697_);
v___x_6699_ = v___x_6692_;
goto v_reusejp_6698_;
}
else
{
lean_object* v_reuseFailAlloc_6700_; 
v_reuseFailAlloc_6700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6700_, 0, v___x_6697_);
v___x_6699_ = v_reuseFailAlloc_6700_;
goto v_reusejp_6698_;
}
v_reusejp_6698_:
{
return v___x_6699_;
}
}
else
{
lean_object* v___x_6701_; lean_object* v___x_6702_; 
lean_del_object(v___x_6692_);
v___x_6701_ = lean_array_mk(v_all_6677_);
v___x_6702_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfSpecTheorems(v___x_6701_, v_fst_6685_, v_snd_6686_, v___y_6678_, v___y_6679_, v___y_6680_, v___y_6681_);
lean_dec_ref(v___x_6701_);
return v___x_6702_;
}
}
}
else
{
lean_object* v_a_6705_; lean_object* v___x_6707_; uint8_t v_isShared_6708_; uint8_t v_isSharedCheck_6712_; 
lean_dec(v_snd_6686_);
lean_dec(v_fst_6685_);
lean_dec(v_all_6677_);
v_a_6705_ = lean_ctor_get(v___x_6690_, 0);
v_isSharedCheck_6712_ = !lean_is_exclusive(v___x_6690_);
if (v_isSharedCheck_6712_ == 0)
{
v___x_6707_ = v___x_6690_;
v_isShared_6708_ = v_isSharedCheck_6712_;
goto v_resetjp_6706_;
}
else
{
lean_inc(v_a_6705_);
lean_dec(v___x_6690_);
v___x_6707_ = lean_box(0);
v_isShared_6708_ = v_isSharedCheck_6712_;
goto v_resetjp_6706_;
}
v_resetjp_6706_:
{
lean_object* v___x_6710_; 
if (v_isShared_6708_ == 0)
{
v___x_6710_ = v___x_6707_;
goto v_reusejp_6709_;
}
else
{
lean_object* v_reuseFailAlloc_6711_; 
v_reuseFailAlloc_6711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6711_, 0, v_a_6705_);
v___x_6710_ = v_reuseFailAlloc_6711_;
goto v_reusejp_6709_;
}
v_reusejp_6709_:
{
return v___x_6710_;
}
}
}
}
else
{
lean_object* v_a_6713_; lean_object* v___x_6715_; uint8_t v_isShared_6716_; uint8_t v_isSharedCheck_6720_; 
lean_dec(v_all_6677_);
v_a_6713_ = lean_ctor_get(v___x_6683_, 0);
v_isSharedCheck_6720_ = !lean_is_exclusive(v___x_6683_);
if (v_isSharedCheck_6720_ == 0)
{
v___x_6715_ = v___x_6683_;
v_isShared_6716_ = v_isSharedCheck_6720_;
goto v_resetjp_6714_;
}
else
{
lean_inc(v_a_6713_);
lean_dec(v___x_6683_);
v___x_6715_ = lean_box(0);
v_isShared_6716_ = v_isSharedCheck_6720_;
goto v_resetjp_6714_;
}
v_resetjp_6714_:
{
lean_object* v___x_6718_; 
if (v_isShared_6716_ == 0)
{
v___x_6718_ = v___x_6715_;
goto v_reusejp_6717_;
}
else
{
lean_object* v_reuseFailAlloc_6719_; 
v_reuseFailAlloc_6719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6719_, 0, v_a_6713_);
v___x_6718_ = v_reuseFailAlloc_6719_;
goto v_reusejp_6717_;
}
v_reusejp_6717_:
{
return v___x_6718_;
}
}
}
}
else
{
lean_object* v___x_6721_; lean_object* v___x_6722_; 
lean_dec(v_all_6677_);
lean_dec(v_typeName_6676_);
v___x_6721_ = lean_box(0);
v___x_6722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6722_, 0, v___x_6721_);
return v___x_6722_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfInstances___lam__2___boxed(lean_object* v_isUnsafe_6723_, lean_object* v_typeName_6724_, lean_object* v_all_6725_, lean_object* v___y_6726_, lean_object* v___y_6727_, lean_object* v___y_6728_, lean_object* v___y_6729_, lean_object* v___y_6730_){
_start:
{
uint8_t v_isUnsafe_boxed_6731_; lean_object* v_res_6732_; 
v_isUnsafe_boxed_6731_ = lean_unbox(v_isUnsafe_6723_);
v_res_6732_ = l_Lean_Meta_mkSizeOfInstances___lam__2(v_isUnsafe_boxed_6731_, v_typeName_6724_, v_all_6725_, v___y_6726_, v___y_6727_, v___y_6728_, v___y_6729_);
lean_dec(v___y_6729_);
lean_dec_ref(v___y_6728_);
lean_dec(v___y_6727_);
lean_dec_ref(v___y_6726_);
return v_res_6732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__6_spec__7(size_t v_sz_6733_, size_t v_i_6734_, lean_object* v_bs_6735_){
_start:
{
uint8_t v___x_6736_; 
v___x_6736_ = lean_usize_dec_lt(v_i_6734_, v_sz_6733_);
if (v___x_6736_ == 0)
{
return v_bs_6735_;
}
else
{
lean_object* v_v_6737_; lean_object* v_msg_6738_; lean_object* v___x_6739_; lean_object* v_bs_x27_6740_; size_t v___x_6741_; size_t v___x_6742_; lean_object* v___x_6743_; 
v_v_6737_ = lean_array_uget_borrowed(v_bs_6735_, v_i_6734_);
v_msg_6738_ = lean_ctor_get(v_v_6737_, 1);
lean_inc_ref(v_msg_6738_);
v___x_6739_ = lean_unsigned_to_nat(0u);
v_bs_x27_6740_ = lean_array_uset(v_bs_6735_, v_i_6734_, v___x_6739_);
v___x_6741_ = ((size_t)1ULL);
v___x_6742_ = lean_usize_add(v_i_6734_, v___x_6741_);
v___x_6743_ = lean_array_uset(v_bs_x27_6740_, v_i_6734_, v_msg_6738_);
v_i_6734_ = v___x_6742_;
v_bs_6735_ = v___x_6743_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__6_spec__7___boxed(lean_object* v_sz_6745_, lean_object* v_i_6746_, lean_object* v_bs_6747_){
_start:
{
size_t v_sz_boxed_6748_; size_t v_i_boxed_6749_; lean_object* v_res_6750_; 
v_sz_boxed_6748_ = lean_unbox_usize(v_sz_6745_);
lean_dec(v_sz_6745_);
v_i_boxed_6749_ = lean_unbox_usize(v_i_6746_);
lean_dec(v_i_6746_);
v_res_6750_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__6_spec__7(v_sz_boxed_6748_, v_i_boxed_6749_, v_bs_6747_);
return v_res_6750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__6(lean_object* v_oldTraces_6751_, lean_object* v_data_6752_, lean_object* v_ref_6753_, lean_object* v_msg_6754_, lean_object* v___y_6755_, lean_object* v___y_6756_, lean_object* v___y_6757_, lean_object* v___y_6758_){
_start:
{
lean_object* v_fileName_6760_; lean_object* v_fileMap_6761_; lean_object* v_options_6762_; lean_object* v_currRecDepth_6763_; lean_object* v_maxRecDepth_6764_; lean_object* v_ref_6765_; lean_object* v_currNamespace_6766_; lean_object* v_openDecls_6767_; lean_object* v_initHeartbeats_6768_; lean_object* v_maxHeartbeats_6769_; lean_object* v_quotContext_6770_; lean_object* v_currMacroScope_6771_; uint8_t v_diag_6772_; lean_object* v_cancelTk_x3f_6773_; uint8_t v_suppressElabErrors_6774_; lean_object* v_inheritedTraceOptions_6775_; lean_object* v___x_6776_; lean_object* v_traceState_6777_; lean_object* v_traces_6778_; lean_object* v_ref_6779_; lean_object* v___x_6780_; lean_object* v___x_6781_; size_t v_sz_6782_; size_t v___x_6783_; lean_object* v___x_6784_; lean_object* v_msg_6785_; lean_object* v___x_6786_; lean_object* v_a_6787_; lean_object* v___x_6789_; uint8_t v_isShared_6790_; uint8_t v_isSharedCheck_6824_; 
v_fileName_6760_ = lean_ctor_get(v___y_6757_, 0);
v_fileMap_6761_ = lean_ctor_get(v___y_6757_, 1);
v_options_6762_ = lean_ctor_get(v___y_6757_, 2);
v_currRecDepth_6763_ = lean_ctor_get(v___y_6757_, 3);
v_maxRecDepth_6764_ = lean_ctor_get(v___y_6757_, 4);
v_ref_6765_ = lean_ctor_get(v___y_6757_, 5);
v_currNamespace_6766_ = lean_ctor_get(v___y_6757_, 6);
v_openDecls_6767_ = lean_ctor_get(v___y_6757_, 7);
v_initHeartbeats_6768_ = lean_ctor_get(v___y_6757_, 8);
v_maxHeartbeats_6769_ = lean_ctor_get(v___y_6757_, 9);
v_quotContext_6770_ = lean_ctor_get(v___y_6757_, 10);
v_currMacroScope_6771_ = lean_ctor_get(v___y_6757_, 11);
v_diag_6772_ = lean_ctor_get_uint8(v___y_6757_, sizeof(void*)*14);
v_cancelTk_x3f_6773_ = lean_ctor_get(v___y_6757_, 12);
v_suppressElabErrors_6774_ = lean_ctor_get_uint8(v___y_6757_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_6775_ = lean_ctor_get(v___y_6757_, 13);
v___x_6776_ = lean_st_ref_get(v___y_6758_);
v_traceState_6777_ = lean_ctor_get(v___x_6776_, 4);
lean_inc_ref(v_traceState_6777_);
lean_dec(v___x_6776_);
v_traces_6778_ = lean_ctor_get(v_traceState_6777_, 0);
lean_inc_ref(v_traces_6778_);
lean_dec_ref(v_traceState_6777_);
v_ref_6779_ = l_Lean_replaceRef(v_ref_6753_, v_ref_6765_);
lean_inc_ref(v_inheritedTraceOptions_6775_);
lean_inc(v_cancelTk_x3f_6773_);
lean_inc(v_currMacroScope_6771_);
lean_inc(v_quotContext_6770_);
lean_inc(v_maxHeartbeats_6769_);
lean_inc(v_initHeartbeats_6768_);
lean_inc(v_openDecls_6767_);
lean_inc(v_currNamespace_6766_);
lean_inc(v_maxRecDepth_6764_);
lean_inc(v_currRecDepth_6763_);
lean_inc_ref(v_options_6762_);
lean_inc_ref(v_fileMap_6761_);
lean_inc_ref(v_fileName_6760_);
v___x_6780_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_6780_, 0, v_fileName_6760_);
lean_ctor_set(v___x_6780_, 1, v_fileMap_6761_);
lean_ctor_set(v___x_6780_, 2, v_options_6762_);
lean_ctor_set(v___x_6780_, 3, v_currRecDepth_6763_);
lean_ctor_set(v___x_6780_, 4, v_maxRecDepth_6764_);
lean_ctor_set(v___x_6780_, 5, v_ref_6779_);
lean_ctor_set(v___x_6780_, 6, v_currNamespace_6766_);
lean_ctor_set(v___x_6780_, 7, v_openDecls_6767_);
lean_ctor_set(v___x_6780_, 8, v_initHeartbeats_6768_);
lean_ctor_set(v___x_6780_, 9, v_maxHeartbeats_6769_);
lean_ctor_set(v___x_6780_, 10, v_quotContext_6770_);
lean_ctor_set(v___x_6780_, 11, v_currMacroScope_6771_);
lean_ctor_set(v___x_6780_, 12, v_cancelTk_x3f_6773_);
lean_ctor_set(v___x_6780_, 13, v_inheritedTraceOptions_6775_);
lean_ctor_set_uint8(v___x_6780_, sizeof(void*)*14, v_diag_6772_);
lean_ctor_set_uint8(v___x_6780_, sizeof(void*)*14 + 1, v_suppressElabErrors_6774_);
v___x_6781_ = l_Lean_PersistentArray_toArray___redArg(v_traces_6778_);
lean_dec_ref(v_traces_6778_);
v_sz_6782_ = lean_array_size(v___x_6781_);
v___x_6783_ = ((size_t)0ULL);
v___x_6784_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__6_spec__7(v_sz_6782_, v___x_6783_, v___x_6781_);
v_msg_6785_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_6785_, 0, v_data_6752_);
lean_ctor_set(v_msg_6785_, 1, v_msg_6754_);
lean_ctor_set(v_msg_6785_, 2, v___x_6784_);
v___x_6786_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1_spec__1(v_msg_6785_, v___y_6755_, v___y_6756_, v___x_6780_, v___y_6758_);
lean_dec_ref(v___x_6780_);
v_a_6787_ = lean_ctor_get(v___x_6786_, 0);
v_isSharedCheck_6824_ = !lean_is_exclusive(v___x_6786_);
if (v_isSharedCheck_6824_ == 0)
{
v___x_6789_ = v___x_6786_;
v_isShared_6790_ = v_isSharedCheck_6824_;
goto v_resetjp_6788_;
}
else
{
lean_inc(v_a_6787_);
lean_dec(v___x_6786_);
v___x_6789_ = lean_box(0);
v_isShared_6790_ = v_isSharedCheck_6824_;
goto v_resetjp_6788_;
}
v_resetjp_6788_:
{
lean_object* v___x_6791_; lean_object* v_traceState_6792_; lean_object* v_env_6793_; lean_object* v_nextMacroScope_6794_; lean_object* v_ngen_6795_; lean_object* v_auxDeclNGen_6796_; lean_object* v_cache_6797_; lean_object* v_messages_6798_; lean_object* v_infoState_6799_; lean_object* v_snapshotTasks_6800_; lean_object* v___x_6802_; uint8_t v_isShared_6803_; uint8_t v_isSharedCheck_6823_; 
v___x_6791_ = lean_st_ref_take(v___y_6758_);
v_traceState_6792_ = lean_ctor_get(v___x_6791_, 4);
v_env_6793_ = lean_ctor_get(v___x_6791_, 0);
v_nextMacroScope_6794_ = lean_ctor_get(v___x_6791_, 1);
v_ngen_6795_ = lean_ctor_get(v___x_6791_, 2);
v_auxDeclNGen_6796_ = lean_ctor_get(v___x_6791_, 3);
v_cache_6797_ = lean_ctor_get(v___x_6791_, 5);
v_messages_6798_ = lean_ctor_get(v___x_6791_, 6);
v_infoState_6799_ = lean_ctor_get(v___x_6791_, 7);
v_snapshotTasks_6800_ = lean_ctor_get(v___x_6791_, 8);
v_isSharedCheck_6823_ = !lean_is_exclusive(v___x_6791_);
if (v_isSharedCheck_6823_ == 0)
{
v___x_6802_ = v___x_6791_;
v_isShared_6803_ = v_isSharedCheck_6823_;
goto v_resetjp_6801_;
}
else
{
lean_inc(v_snapshotTasks_6800_);
lean_inc(v_infoState_6799_);
lean_inc(v_messages_6798_);
lean_inc(v_cache_6797_);
lean_inc(v_traceState_6792_);
lean_inc(v_auxDeclNGen_6796_);
lean_inc(v_ngen_6795_);
lean_inc(v_nextMacroScope_6794_);
lean_inc(v_env_6793_);
lean_dec(v___x_6791_);
v___x_6802_ = lean_box(0);
v_isShared_6803_ = v_isSharedCheck_6823_;
goto v_resetjp_6801_;
}
v_resetjp_6801_:
{
uint64_t v_tid_6804_; lean_object* v___x_6806_; uint8_t v_isShared_6807_; uint8_t v_isSharedCheck_6821_; 
v_tid_6804_ = lean_ctor_get_uint64(v_traceState_6792_, sizeof(void*)*1);
v_isSharedCheck_6821_ = !lean_is_exclusive(v_traceState_6792_);
if (v_isSharedCheck_6821_ == 0)
{
lean_object* v_unused_6822_; 
v_unused_6822_ = lean_ctor_get(v_traceState_6792_, 0);
lean_dec(v_unused_6822_);
v___x_6806_ = v_traceState_6792_;
v_isShared_6807_ = v_isSharedCheck_6821_;
goto v_resetjp_6805_;
}
else
{
lean_dec(v_traceState_6792_);
v___x_6806_ = lean_box(0);
v_isShared_6807_ = v_isSharedCheck_6821_;
goto v_resetjp_6805_;
}
v_resetjp_6805_:
{
lean_object* v___x_6808_; lean_object* v___x_6809_; lean_object* v___x_6811_; 
v___x_6808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6808_, 0, v_ref_6753_);
lean_ctor_set(v___x_6808_, 1, v_a_6787_);
v___x_6809_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_6751_, v___x_6808_);
if (v_isShared_6807_ == 0)
{
lean_ctor_set(v___x_6806_, 0, v___x_6809_);
v___x_6811_ = v___x_6806_;
goto v_reusejp_6810_;
}
else
{
lean_object* v_reuseFailAlloc_6820_; 
v_reuseFailAlloc_6820_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6820_, 0, v___x_6809_);
lean_ctor_set_uint64(v_reuseFailAlloc_6820_, sizeof(void*)*1, v_tid_6804_);
v___x_6811_ = v_reuseFailAlloc_6820_;
goto v_reusejp_6810_;
}
v_reusejp_6810_:
{
lean_object* v___x_6813_; 
if (v_isShared_6803_ == 0)
{
lean_ctor_set(v___x_6802_, 4, v___x_6811_);
v___x_6813_ = v___x_6802_;
goto v_reusejp_6812_;
}
else
{
lean_object* v_reuseFailAlloc_6819_; 
v_reuseFailAlloc_6819_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6819_, 0, v_env_6793_);
lean_ctor_set(v_reuseFailAlloc_6819_, 1, v_nextMacroScope_6794_);
lean_ctor_set(v_reuseFailAlloc_6819_, 2, v_ngen_6795_);
lean_ctor_set(v_reuseFailAlloc_6819_, 3, v_auxDeclNGen_6796_);
lean_ctor_set(v_reuseFailAlloc_6819_, 4, v___x_6811_);
lean_ctor_set(v_reuseFailAlloc_6819_, 5, v_cache_6797_);
lean_ctor_set(v_reuseFailAlloc_6819_, 6, v_messages_6798_);
lean_ctor_set(v_reuseFailAlloc_6819_, 7, v_infoState_6799_);
lean_ctor_set(v_reuseFailAlloc_6819_, 8, v_snapshotTasks_6800_);
v___x_6813_ = v_reuseFailAlloc_6819_;
goto v_reusejp_6812_;
}
v_reusejp_6812_:
{
lean_object* v___x_6814_; lean_object* v___x_6815_; lean_object* v___x_6817_; 
v___x_6814_ = lean_st_ref_set(v___y_6758_, v___x_6813_);
v___x_6815_ = lean_box(0);
if (v_isShared_6790_ == 0)
{
lean_ctor_set(v___x_6789_, 0, v___x_6815_);
v___x_6817_ = v___x_6789_;
goto v_reusejp_6816_;
}
else
{
lean_object* v_reuseFailAlloc_6818_; 
v_reuseFailAlloc_6818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6818_, 0, v___x_6815_);
v___x_6817_ = v_reuseFailAlloc_6818_;
goto v_reusejp_6816_;
}
v_reusejp_6816_:
{
return v___x_6817_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__6___boxed(lean_object* v_oldTraces_6825_, lean_object* v_data_6826_, lean_object* v_ref_6827_, lean_object* v_msg_6828_, lean_object* v___y_6829_, lean_object* v___y_6830_, lean_object* v___y_6831_, lean_object* v___y_6832_, lean_object* v___y_6833_){
_start:
{
lean_object* v_res_6834_; 
v_res_6834_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__6(v_oldTraces_6825_, v_data_6826_, v_ref_6827_, v_msg_6828_, v___y_6829_, v___y_6830_, v___y_6831_, v___y_6832_);
lean_dec(v___y_6832_);
lean_dec_ref(v___y_6831_);
lean_dec(v___y_6830_);
lean_dec_ref(v___y_6829_);
return v_res_6834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__8(lean_object* v_opts_6835_, lean_object* v_opt_6836_){
_start:
{
lean_object* v_name_6837_; lean_object* v_defValue_6838_; lean_object* v_map_6839_; lean_object* v___x_6840_; 
v_name_6837_ = lean_ctor_get(v_opt_6836_, 0);
v_defValue_6838_ = lean_ctor_get(v_opt_6836_, 1);
v_map_6839_ = lean_ctor_get(v_opts_6835_, 0);
v___x_6840_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6839_, v_name_6837_);
if (lean_obj_tag(v___x_6840_) == 0)
{
lean_inc(v_defValue_6838_);
return v_defValue_6838_;
}
else
{
lean_object* v_val_6841_; 
v_val_6841_ = lean_ctor_get(v___x_6840_, 0);
lean_inc(v_val_6841_);
lean_dec_ref(v___x_6840_);
if (lean_obj_tag(v_val_6841_) == 3)
{
lean_object* v_v_6842_; 
v_v_6842_ = lean_ctor_get(v_val_6841_, 0);
lean_inc(v_v_6842_);
lean_dec_ref(v_val_6841_);
return v_v_6842_;
}
else
{
lean_dec(v_val_6841_);
lean_inc(v_defValue_6838_);
return v_defValue_6838_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__8___boxed(lean_object* v_opts_6843_, lean_object* v_opt_6844_){
_start:
{
lean_object* v_res_6845_; 
v_res_6845_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__8(v_opts_6843_, v_opt_6844_);
lean_dec_ref(v_opt_6844_);
lean_dec_ref(v_opts_6843_);
return v_res_6845_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__7___redArg(lean_object* v_x_6846_){
_start:
{
if (lean_obj_tag(v_x_6846_) == 0)
{
lean_object* v_a_6848_; lean_object* v___x_6850_; uint8_t v_isShared_6851_; uint8_t v_isSharedCheck_6855_; 
v_a_6848_ = lean_ctor_get(v_x_6846_, 0);
v_isSharedCheck_6855_ = !lean_is_exclusive(v_x_6846_);
if (v_isSharedCheck_6855_ == 0)
{
v___x_6850_ = v_x_6846_;
v_isShared_6851_ = v_isSharedCheck_6855_;
goto v_resetjp_6849_;
}
else
{
lean_inc(v_a_6848_);
lean_dec(v_x_6846_);
v___x_6850_ = lean_box(0);
v_isShared_6851_ = v_isSharedCheck_6855_;
goto v_resetjp_6849_;
}
v_resetjp_6849_:
{
lean_object* v___x_6853_; 
if (v_isShared_6851_ == 0)
{
lean_ctor_set_tag(v___x_6850_, 1);
v___x_6853_ = v___x_6850_;
goto v_reusejp_6852_;
}
else
{
lean_object* v_reuseFailAlloc_6854_; 
v_reuseFailAlloc_6854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6854_, 0, v_a_6848_);
v___x_6853_ = v_reuseFailAlloc_6854_;
goto v_reusejp_6852_;
}
v_reusejp_6852_:
{
return v___x_6853_;
}
}
}
else
{
lean_object* v_a_6856_; lean_object* v___x_6858_; uint8_t v_isShared_6859_; uint8_t v_isSharedCheck_6863_; 
v_a_6856_ = lean_ctor_get(v_x_6846_, 0);
v_isSharedCheck_6863_ = !lean_is_exclusive(v_x_6846_);
if (v_isSharedCheck_6863_ == 0)
{
v___x_6858_ = v_x_6846_;
v_isShared_6859_ = v_isSharedCheck_6863_;
goto v_resetjp_6857_;
}
else
{
lean_inc(v_a_6856_);
lean_dec(v_x_6846_);
v___x_6858_ = lean_box(0);
v_isShared_6859_ = v_isSharedCheck_6863_;
goto v_resetjp_6857_;
}
v_resetjp_6857_:
{
lean_object* v___x_6861_; 
if (v_isShared_6859_ == 0)
{
lean_ctor_set_tag(v___x_6858_, 0);
v___x_6861_ = v___x_6858_;
goto v_reusejp_6860_;
}
else
{
lean_object* v_reuseFailAlloc_6862_; 
v_reuseFailAlloc_6862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6862_, 0, v_a_6856_);
v___x_6861_ = v_reuseFailAlloc_6862_;
goto v_reusejp_6860_;
}
v_reusejp_6860_:
{
return v___x_6861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__7___redArg___boxed(lean_object* v_x_6864_, lean_object* v___y_6865_){
_start:
{
lean_object* v_res_6866_; 
v_res_6866_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__7___redArg(v_x_6864_);
return v_res_6866_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__5(lean_object* v_e_6867_){
_start:
{
if (lean_obj_tag(v_e_6867_) == 0)
{
uint8_t v___x_6868_; 
v___x_6868_ = 2;
return v___x_6868_;
}
else
{
uint8_t v___x_6869_; 
v___x_6869_ = 0;
return v___x_6869_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__5___boxed(lean_object* v_e_6870_){
_start:
{
uint8_t v_res_6871_; lean_object* v_r_6872_; 
v_res_6871_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__5(v_e_6870_);
lean_dec_ref(v_e_6870_);
v_r_6872_ = lean_box(v_res_6871_);
return v_r_6872_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5___closed__1(void){
_start:
{
lean_object* v___x_6874_; lean_object* v___x_6875_; 
v___x_6874_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5___closed__0));
v___x_6875_ = l_Lean_stringToMessageData(v___x_6874_);
return v___x_6875_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5___closed__3(void){
_start:
{
lean_object* v___x_6877_; lean_object* v___x_6878_; 
v___x_6877_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5___closed__2));
v___x_6878_ = l_Lean_stringToMessageData(v___x_6877_);
return v___x_6878_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5___closed__4(void){
_start:
{
lean_object* v___x_6879_; double v___x_6880_; 
v___x_6879_ = lean_unsigned_to_nat(1000u);
v___x_6880_ = lean_float_of_nat(v___x_6879_);
return v___x_6880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5(lean_object* v_cls_6881_, uint8_t v_collapsed_6882_, lean_object* v_tag_6883_, lean_object* v_opts_6884_, uint8_t v_clsEnabled_6885_, lean_object* v_oldTraces_6886_, lean_object* v_msg_6887_, lean_object* v_resStartStop_6888_, lean_object* v___y_6889_, lean_object* v___y_6890_, lean_object* v___y_6891_, lean_object* v___y_6892_){
_start:
{
lean_object* v_fst_6894_; lean_object* v_snd_6895_; lean_object* v___x_6897_; uint8_t v_isShared_6898_; uint8_t v_isSharedCheck_6985_; 
v_fst_6894_ = lean_ctor_get(v_resStartStop_6888_, 0);
v_snd_6895_ = lean_ctor_get(v_resStartStop_6888_, 1);
v_isSharedCheck_6985_ = !lean_is_exclusive(v_resStartStop_6888_);
if (v_isSharedCheck_6985_ == 0)
{
v___x_6897_ = v_resStartStop_6888_;
v_isShared_6898_ = v_isSharedCheck_6985_;
goto v_resetjp_6896_;
}
else
{
lean_inc(v_snd_6895_);
lean_inc(v_fst_6894_);
lean_dec(v_resStartStop_6888_);
v___x_6897_ = lean_box(0);
v_isShared_6898_ = v_isSharedCheck_6985_;
goto v_resetjp_6896_;
}
v_resetjp_6896_:
{
lean_object* v___y_6900_; lean_object* v___y_6901_; lean_object* v_data_6902_; lean_object* v_fst_6905_; lean_object* v_snd_6906_; lean_object* v___x_6908_; uint8_t v_isShared_6909_; uint8_t v_isSharedCheck_6984_; 
v_fst_6905_ = lean_ctor_get(v_snd_6895_, 0);
v_snd_6906_ = lean_ctor_get(v_snd_6895_, 1);
v_isSharedCheck_6984_ = !lean_is_exclusive(v_snd_6895_);
if (v_isSharedCheck_6984_ == 0)
{
v___x_6908_ = v_snd_6895_;
v_isShared_6909_ = v_isSharedCheck_6984_;
goto v_resetjp_6907_;
}
else
{
lean_inc(v_snd_6906_);
lean_inc(v_fst_6905_);
lean_dec(v_snd_6895_);
v___x_6908_ = lean_box(0);
v_isShared_6909_ = v_isSharedCheck_6984_;
goto v_resetjp_6907_;
}
v___jp_6899_:
{
lean_object* v___x_6903_; 
lean_inc(v___y_6901_);
v___x_6903_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__6(v_oldTraces_6886_, v_data_6902_, v___y_6901_, v___y_6900_, v___y_6889_, v___y_6890_, v___y_6891_, v___y_6892_);
if (lean_obj_tag(v___x_6903_) == 0)
{
lean_object* v___x_6904_; 
lean_dec_ref(v___x_6903_);
v___x_6904_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__7___redArg(v_fst_6894_);
return v___x_6904_;
}
else
{
lean_dec(v_fst_6894_);
return v___x_6903_;
}
}
v_resetjp_6907_:
{
lean_object* v___x_6910_; uint8_t v___x_6911_; lean_object* v___y_6913_; lean_object* v_a_6914_; uint8_t v___y_6938_; double v___y_6969_; 
v___x_6910_ = l_Lean_trace_profiler;
v___x_6911_ = l_Lean_Option_get___at___00Lean_Meta_mkSizeOfInstances_spec__1(v_opts_6884_, v___x_6910_);
if (v___x_6911_ == 0)
{
v___y_6938_ = v___x_6911_;
goto v___jp_6937_;
}
else
{
lean_object* v___x_6974_; uint8_t v___x_6975_; 
v___x_6974_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6975_ = l_Lean_Option_get___at___00Lean_Meta_mkSizeOfInstances_spec__1(v_opts_6884_, v___x_6974_);
if (v___x_6975_ == 0)
{
lean_object* v___x_6976_; lean_object* v___x_6977_; double v___x_6978_; double v___x_6979_; double v___x_6980_; 
v___x_6976_ = l_Lean_trace_profiler_threshold;
v___x_6977_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__8(v_opts_6884_, v___x_6976_);
v___x_6978_ = lean_float_of_nat(v___x_6977_);
v___x_6979_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5___closed__4);
v___x_6980_ = lean_float_div(v___x_6978_, v___x_6979_);
v___y_6969_ = v___x_6980_;
goto v___jp_6968_;
}
else
{
lean_object* v___x_6981_; lean_object* v___x_6982_; double v___x_6983_; 
v___x_6981_ = l_Lean_trace_profiler_threshold;
v___x_6982_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__8(v_opts_6884_, v___x_6981_);
v___x_6983_ = lean_float_of_nat(v___x_6982_);
v___y_6969_ = v___x_6983_;
goto v___jp_6968_;
}
}
v___jp_6912_:
{
uint8_t v_result_6915_; lean_object* v___x_6916_; lean_object* v___x_6917_; lean_object* v___x_6918_; lean_object* v___x_6920_; 
v_result_6915_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__5(v_fst_6894_);
v___x_6916_ = l_Lean_TraceResult_toEmoji(v_result_6915_);
v___x_6917_ = l_Lean_stringToMessageData(v___x_6916_);
v___x_6918_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5___closed__1);
if (v_isShared_6909_ == 0)
{
lean_ctor_set_tag(v___x_6908_, 7);
lean_ctor_set(v___x_6908_, 1, v___x_6918_);
lean_ctor_set(v___x_6908_, 0, v___x_6917_);
v___x_6920_ = v___x_6908_;
goto v_reusejp_6919_;
}
else
{
lean_object* v_reuseFailAlloc_6931_; 
v_reuseFailAlloc_6931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6931_, 0, v___x_6917_);
lean_ctor_set(v_reuseFailAlloc_6931_, 1, v___x_6918_);
v___x_6920_ = v_reuseFailAlloc_6931_;
goto v_reusejp_6919_;
}
v_reusejp_6919_:
{
lean_object* v_m_6922_; 
if (v_isShared_6898_ == 0)
{
lean_ctor_set_tag(v___x_6897_, 7);
lean_ctor_set(v___x_6897_, 1, v_a_6914_);
lean_ctor_set(v___x_6897_, 0, v___x_6920_);
v_m_6922_ = v___x_6897_;
goto v_reusejp_6921_;
}
else
{
lean_object* v_reuseFailAlloc_6930_; 
v_reuseFailAlloc_6930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6930_, 0, v___x_6920_);
lean_ctor_set(v_reuseFailAlloc_6930_, 1, v_a_6914_);
v_m_6922_ = v_reuseFailAlloc_6930_;
goto v_reusejp_6921_;
}
v_reusejp_6921_:
{
lean_object* v___x_6923_; lean_object* v___x_6924_; double v___x_6925_; lean_object* v_data_6926_; 
v___x_6923_ = lean_box(v_result_6915_);
v___x_6924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6924_, 0, v___x_6923_);
v___x_6925_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1___closed__0);
lean_inc_ref(v_tag_6883_);
lean_inc_ref(v___x_6924_);
lean_inc(v_cls_6881_);
v_data_6926_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6926_, 0, v_cls_6881_);
lean_ctor_set(v_data_6926_, 1, v___x_6924_);
lean_ctor_set(v_data_6926_, 2, v_tag_6883_);
lean_ctor_set_float(v_data_6926_, sizeof(void*)*3, v___x_6925_);
lean_ctor_set_float(v_data_6926_, sizeof(void*)*3 + 8, v___x_6925_);
lean_ctor_set_uint8(v_data_6926_, sizeof(void*)*3 + 16, v_collapsed_6882_);
if (v___x_6911_ == 0)
{
lean_dec_ref(v___x_6924_);
lean_dec(v_snd_6906_);
lean_dec(v_fst_6905_);
lean_dec_ref(v_tag_6883_);
lean_dec(v_cls_6881_);
v___y_6900_ = v_m_6922_;
v___y_6901_ = v___y_6913_;
v_data_6902_ = v_data_6926_;
goto v___jp_6899_;
}
else
{
lean_object* v_data_6927_; double v___x_6928_; double v___x_6929_; 
lean_dec_ref(v_data_6926_);
v_data_6927_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6927_, 0, v_cls_6881_);
lean_ctor_set(v_data_6927_, 1, v___x_6924_);
lean_ctor_set(v_data_6927_, 2, v_tag_6883_);
v___x_6928_ = lean_unbox_float(v_fst_6905_);
lean_dec(v_fst_6905_);
lean_ctor_set_float(v_data_6927_, sizeof(void*)*3, v___x_6928_);
v___x_6929_ = lean_unbox_float(v_snd_6906_);
lean_dec(v_snd_6906_);
lean_ctor_set_float(v_data_6927_, sizeof(void*)*3 + 8, v___x_6929_);
lean_ctor_set_uint8(v_data_6927_, sizeof(void*)*3 + 16, v_collapsed_6882_);
v___y_6900_ = v_m_6922_;
v___y_6901_ = v___y_6913_;
v_data_6902_ = v_data_6927_;
goto v___jp_6899_;
}
}
}
}
v___jp_6932_:
{
lean_object* v_ref_6933_; lean_object* v___x_6934_; 
v_ref_6933_ = lean_ctor_get(v___y_6891_, 5);
lean_inc(v___y_6892_);
lean_inc_ref(v___y_6891_);
lean_inc(v___y_6890_);
lean_inc_ref(v___y_6889_);
lean_inc(v_fst_6894_);
v___x_6934_ = lean_apply_6(v_msg_6887_, v_fst_6894_, v___y_6889_, v___y_6890_, v___y_6891_, v___y_6892_, lean_box(0));
if (lean_obj_tag(v___x_6934_) == 0)
{
lean_object* v_a_6935_; 
v_a_6935_ = lean_ctor_get(v___x_6934_, 0);
lean_inc(v_a_6935_);
lean_dec_ref(v___x_6934_);
v___y_6913_ = v_ref_6933_;
v_a_6914_ = v_a_6935_;
goto v___jp_6912_;
}
else
{
lean_object* v___x_6936_; 
lean_dec_ref(v___x_6934_);
v___x_6936_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5___closed__3);
v___y_6913_ = v_ref_6933_;
v_a_6914_ = v___x_6936_;
goto v___jp_6912_;
}
}
v___jp_6937_:
{
if (v_clsEnabled_6885_ == 0)
{
if (v___y_6938_ == 0)
{
lean_object* v___x_6939_; lean_object* v_traceState_6940_; lean_object* v_env_6941_; lean_object* v_nextMacroScope_6942_; lean_object* v_ngen_6943_; lean_object* v_auxDeclNGen_6944_; lean_object* v_cache_6945_; lean_object* v_messages_6946_; lean_object* v_infoState_6947_; lean_object* v_snapshotTasks_6948_; lean_object* v___x_6950_; uint8_t v_isShared_6951_; uint8_t v_isSharedCheck_6967_; 
lean_del_object(v___x_6908_);
lean_dec(v_snd_6906_);
lean_dec(v_fst_6905_);
lean_del_object(v___x_6897_);
lean_dec_ref(v_msg_6887_);
lean_dec_ref(v_tag_6883_);
lean_dec(v_cls_6881_);
v___x_6939_ = lean_st_ref_take(v___y_6892_);
v_traceState_6940_ = lean_ctor_get(v___x_6939_, 4);
v_env_6941_ = lean_ctor_get(v___x_6939_, 0);
v_nextMacroScope_6942_ = lean_ctor_get(v___x_6939_, 1);
v_ngen_6943_ = lean_ctor_get(v___x_6939_, 2);
v_auxDeclNGen_6944_ = lean_ctor_get(v___x_6939_, 3);
v_cache_6945_ = lean_ctor_get(v___x_6939_, 5);
v_messages_6946_ = lean_ctor_get(v___x_6939_, 6);
v_infoState_6947_ = lean_ctor_get(v___x_6939_, 7);
v_snapshotTasks_6948_ = lean_ctor_get(v___x_6939_, 8);
v_isSharedCheck_6967_ = !lean_is_exclusive(v___x_6939_);
if (v_isSharedCheck_6967_ == 0)
{
v___x_6950_ = v___x_6939_;
v_isShared_6951_ = v_isSharedCheck_6967_;
goto v_resetjp_6949_;
}
else
{
lean_inc(v_snapshotTasks_6948_);
lean_inc(v_infoState_6947_);
lean_inc(v_messages_6946_);
lean_inc(v_cache_6945_);
lean_inc(v_traceState_6940_);
lean_inc(v_auxDeclNGen_6944_);
lean_inc(v_ngen_6943_);
lean_inc(v_nextMacroScope_6942_);
lean_inc(v_env_6941_);
lean_dec(v___x_6939_);
v___x_6950_ = lean_box(0);
v_isShared_6951_ = v_isSharedCheck_6967_;
goto v_resetjp_6949_;
}
v_resetjp_6949_:
{
uint64_t v_tid_6952_; lean_object* v_traces_6953_; lean_object* v___x_6955_; uint8_t v_isShared_6956_; uint8_t v_isSharedCheck_6966_; 
v_tid_6952_ = lean_ctor_get_uint64(v_traceState_6940_, sizeof(void*)*1);
v_traces_6953_ = lean_ctor_get(v_traceState_6940_, 0);
v_isSharedCheck_6966_ = !lean_is_exclusive(v_traceState_6940_);
if (v_isSharedCheck_6966_ == 0)
{
v___x_6955_ = v_traceState_6940_;
v_isShared_6956_ = v_isSharedCheck_6966_;
goto v_resetjp_6954_;
}
else
{
lean_inc(v_traces_6953_);
lean_dec(v_traceState_6940_);
v___x_6955_ = lean_box(0);
v_isShared_6956_ = v_isSharedCheck_6966_;
goto v_resetjp_6954_;
}
v_resetjp_6954_:
{
lean_object* v___x_6957_; lean_object* v___x_6959_; 
v___x_6957_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_6886_, v_traces_6953_);
lean_dec_ref(v_traces_6953_);
if (v_isShared_6956_ == 0)
{
lean_ctor_set(v___x_6955_, 0, v___x_6957_);
v___x_6959_ = v___x_6955_;
goto v_reusejp_6958_;
}
else
{
lean_object* v_reuseFailAlloc_6965_; 
v_reuseFailAlloc_6965_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6965_, 0, v___x_6957_);
lean_ctor_set_uint64(v_reuseFailAlloc_6965_, sizeof(void*)*1, v_tid_6952_);
v___x_6959_ = v_reuseFailAlloc_6965_;
goto v_reusejp_6958_;
}
v_reusejp_6958_:
{
lean_object* v___x_6961_; 
if (v_isShared_6951_ == 0)
{
lean_ctor_set(v___x_6950_, 4, v___x_6959_);
v___x_6961_ = v___x_6950_;
goto v_reusejp_6960_;
}
else
{
lean_object* v_reuseFailAlloc_6964_; 
v_reuseFailAlloc_6964_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6964_, 0, v_env_6941_);
lean_ctor_set(v_reuseFailAlloc_6964_, 1, v_nextMacroScope_6942_);
lean_ctor_set(v_reuseFailAlloc_6964_, 2, v_ngen_6943_);
lean_ctor_set(v_reuseFailAlloc_6964_, 3, v_auxDeclNGen_6944_);
lean_ctor_set(v_reuseFailAlloc_6964_, 4, v___x_6959_);
lean_ctor_set(v_reuseFailAlloc_6964_, 5, v_cache_6945_);
lean_ctor_set(v_reuseFailAlloc_6964_, 6, v_messages_6946_);
lean_ctor_set(v_reuseFailAlloc_6964_, 7, v_infoState_6947_);
lean_ctor_set(v_reuseFailAlloc_6964_, 8, v_snapshotTasks_6948_);
v___x_6961_ = v_reuseFailAlloc_6964_;
goto v_reusejp_6960_;
}
v_reusejp_6960_:
{
lean_object* v___x_6962_; lean_object* v___x_6963_; 
v___x_6962_ = lean_st_ref_set(v___y_6892_, v___x_6961_);
v___x_6963_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__7___redArg(v_fst_6894_);
return v___x_6963_;
}
}
}
}
}
else
{
goto v___jp_6932_;
}
}
else
{
goto v___jp_6932_;
}
}
v___jp_6968_:
{
double v___x_6970_; double v___x_6971_; double v___x_6972_; uint8_t v___x_6973_; 
v___x_6970_ = lean_unbox_float(v_snd_6906_);
v___x_6971_ = lean_unbox_float(v_fst_6905_);
v___x_6972_ = lean_float_sub(v___x_6970_, v___x_6971_);
v___x_6973_ = lean_float_decLt(v___y_6969_, v___x_6972_);
v___y_6938_ = v___x_6973_;
goto v___jp_6937_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5___boxed(lean_object* v_cls_6986_, lean_object* v_collapsed_6987_, lean_object* v_tag_6988_, lean_object* v_opts_6989_, lean_object* v_clsEnabled_6990_, lean_object* v_oldTraces_6991_, lean_object* v_msg_6992_, lean_object* v_resStartStop_6993_, lean_object* v___y_6994_, lean_object* v___y_6995_, lean_object* v___y_6996_, lean_object* v___y_6997_, lean_object* v___y_6998_){
_start:
{
uint8_t v_collapsed_boxed_6999_; uint8_t v_clsEnabled_boxed_7000_; lean_object* v_res_7001_; 
v_collapsed_boxed_6999_ = lean_unbox(v_collapsed_6987_);
v_clsEnabled_boxed_7000_ = lean_unbox(v_clsEnabled_6990_);
v_res_7001_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5(v_cls_6986_, v_collapsed_boxed_6999_, v_tag_6988_, v_opts_6989_, v_clsEnabled_boxed_7000_, v_oldTraces_6991_, v_msg_6992_, v_resStartStop_6993_, v___y_6994_, v___y_6995_, v___y_6996_, v___y_6997_);
lean_dec(v___y_6997_);
lean_dec_ref(v___y_6996_);
lean_dec(v___y_6995_);
lean_dec_ref(v___y_6994_);
lean_dec_ref(v_opts_6989_);
return v_res_7001_;
}
}
static double _init_l_Lean_Meta_mkSizeOfInstances___lam__3___closed__0(void){
_start:
{
lean_object* v___x_7002_; double v___x_7003_; 
v___x_7002_ = lean_unsigned_to_nat(1000000000u);
v___x_7003_ = lean_float_of_nat(v___x_7002_);
return v___x_7003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfInstances___lam__3(lean_object* v_typeName_7004_, uint8_t v___x_7005_, lean_object* v_a_7006_, lean_object* v___f_7007_, lean_object* v___y_7008_, lean_object* v___y_7009_, lean_object* v___y_7010_, lean_object* v___y_7011_){
_start:
{
lean_object* v___x_7013_; lean_object* v___x_7014_; 
v___x_7013_ = lean_st_ref_get(v___y_7011_);
lean_inc(v_typeName_7004_);
v___x_7014_ = l_Lean_Meta_isInductivePredicate(v_typeName_7004_, v___y_7008_, v___y_7009_, v___y_7010_, v___y_7011_);
if (lean_obj_tag(v___x_7014_) == 0)
{
lean_object* v_a_7015_; lean_object* v___x_7017_; uint8_t v_isShared_7018_; uint8_t v_isSharedCheck_7115_; 
v_a_7015_ = lean_ctor_get(v___x_7014_, 0);
v_isSharedCheck_7115_ = !lean_is_exclusive(v___x_7014_);
if (v_isSharedCheck_7115_ == 0)
{
v___x_7017_ = v___x_7014_;
v_isShared_7018_ = v_isSharedCheck_7115_;
goto v_resetjp_7016_;
}
else
{
lean_inc(v_a_7015_);
lean_dec(v___x_7014_);
v___x_7017_ = lean_box(0);
v_isShared_7018_ = v_isSharedCheck_7115_;
goto v_resetjp_7016_;
}
v_resetjp_7016_:
{
lean_object* v_env_7024_; lean_object* v___x_7025_; uint8_t v___x_7026_; 
v_env_7024_ = lean_ctor_get(v___x_7013_, 0);
lean_inc_ref(v_env_7024_);
lean_dec(v___x_7013_);
v___x_7025_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkLocalInstances_loop___redArg___lam__0___closed__1));
v___x_7026_ = l_Lean_Environment_contains(v_env_7024_, v___x_7025_, v___x_7005_);
if (v___x_7026_ == 0)
{
lean_dec(v_a_7015_);
lean_dec_ref(v___f_7007_);
lean_dec_ref(v_a_7006_);
lean_dec(v_typeName_7004_);
goto v___jp_7019_;
}
else
{
lean_object* v_options_7027_; lean_object* v___x_7028_; uint8_t v___x_7029_; 
v_options_7027_ = lean_ctor_get(v___y_7010_, 2);
v___x_7028_ = l_Lean_Meta_genSizeOf;
v___x_7029_ = l_Lean_Option_get___at___00Lean_Meta_mkSizeOfInstances_spec__1(v_options_7027_, v___x_7028_);
if (v___x_7029_ == 0)
{
lean_dec(v_a_7015_);
lean_dec_ref(v___f_7007_);
lean_dec_ref(v_a_7006_);
lean_dec(v_typeName_7004_);
goto v___jp_7019_;
}
else
{
uint8_t v___x_7030_; 
v___x_7030_ = lean_unbox(v_a_7015_);
lean_dec(v_a_7015_);
if (v___x_7030_ == 0)
{
uint8_t v_hasTrace_7031_; 
lean_del_object(v___x_7017_);
v_hasTrace_7031_ = lean_ctor_get_uint8(v_options_7027_, sizeof(void*)*1);
if (v_hasTrace_7031_ == 0)
{
lean_object* v_all_7032_; uint8_t v_isUnsafe_7033_; lean_object* v___x_7034_; 
lean_dec_ref(v___f_7007_);
v_all_7032_ = lean_ctor_get(v_a_7006_, 3);
lean_inc(v_all_7032_);
v_isUnsafe_7033_ = lean_ctor_get_uint8(v_a_7006_, sizeof(void*)*6 + 1);
lean_dec_ref(v_a_7006_);
v___x_7034_ = l_Lean_Meta_mkSizeOfInstances___lam__2(v_isUnsafe_7033_, v_typeName_7004_, v_all_7032_, v___y_7008_, v___y_7009_, v___y_7010_, v___y_7011_);
return v___x_7034_;
}
else
{
lean_object* v_all_7035_; uint8_t v_isUnsafe_7036_; lean_object* v___x_7037_; lean_object* v___x_7038_; lean_object* v_a_7039_; lean_object* v___x_7040_; lean_object* v___y_7042_; lean_object* v___y_7043_; lean_object* v_a_7044_; lean_object* v___y_7058_; lean_object* v___y_7059_; lean_object* v_a_7060_; uint8_t v___x_7111_; 
v_all_7035_ = lean_ctor_get(v_a_7006_, 3);
lean_inc(v_all_7035_);
v_isUnsafe_7036_ = lean_ctor_get_uint8(v_a_7006_, sizeof(void*)*6 + 1);
lean_dec_ref(v_a_7006_);
v___x_7037_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__2));
v___x_7038_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__0___redArg(v___x_7037_, v___y_7010_);
v_a_7039_ = lean_ctor_get(v___x_7038_, 0);
lean_inc(v_a_7039_);
lean_dec_ref(v___x_7038_);
v___x_7040_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop_spec__1___closed__1));
v___x_7111_ = lean_unbox(v_a_7039_);
if (v___x_7111_ == 0)
{
lean_object* v___x_7112_; uint8_t v___x_7113_; 
v___x_7112_ = l_Lean_trace_profiler;
v___x_7113_ = l_Lean_Option_get___at___00Lean_Meta_mkSizeOfInstances_spec__1(v_options_7027_, v___x_7112_);
if (v___x_7113_ == 0)
{
lean_object* v___x_7114_; 
lean_dec(v_a_7039_);
lean_dec_ref(v___f_7007_);
v___x_7114_ = l_Lean_Meta_mkSizeOfInstances___lam__2(v_isUnsafe_7036_, v_typeName_7004_, v_all_7035_, v___y_7008_, v___y_7009_, v___y_7010_, v___y_7011_);
return v___x_7114_;
}
else
{
goto v___jp_7070_;
}
}
else
{
goto v___jp_7070_;
}
v___jp_7041_:
{
lean_object* v___x_7045_; double v___x_7046_; double v___x_7047_; double v___x_7048_; double v___x_7049_; double v___x_7050_; lean_object* v___x_7051_; lean_object* v___x_7052_; lean_object* v___x_7053_; lean_object* v___x_7054_; uint8_t v___x_7055_; lean_object* v___x_7056_; 
v___x_7045_ = lean_io_mono_nanos_now();
v___x_7046_ = lean_float_of_nat(v___y_7043_);
v___x_7047_ = lean_float_once(&l_Lean_Meta_mkSizeOfInstances___lam__3___closed__0, &l_Lean_Meta_mkSizeOfInstances___lam__3___closed__0_once, _init_l_Lean_Meta_mkSizeOfInstances___lam__3___closed__0);
v___x_7048_ = lean_float_div(v___x_7046_, v___x_7047_);
v___x_7049_ = lean_float_of_nat(v___x_7045_);
v___x_7050_ = lean_float_div(v___x_7049_, v___x_7047_);
v___x_7051_ = lean_box_float(v___x_7048_);
v___x_7052_ = lean_box_float(v___x_7050_);
v___x_7053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7053_, 0, v___x_7051_);
lean_ctor_set(v___x_7053_, 1, v___x_7052_);
v___x_7054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7054_, 0, v_a_7044_);
lean_ctor_set(v___x_7054_, 1, v___x_7053_);
v___x_7055_ = lean_unbox(v_a_7039_);
lean_dec(v_a_7039_);
v___x_7056_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5(v___x_7037_, v___x_7005_, v___x_7040_, v_options_7027_, v___x_7055_, v___y_7042_, v___f_7007_, v___x_7054_, v___y_7008_, v___y_7009_, v___y_7010_, v___y_7011_);
return v___x_7056_;
}
v___jp_7057_:
{
lean_object* v___x_7061_; double v___x_7062_; double v___x_7063_; lean_object* v___x_7064_; lean_object* v___x_7065_; lean_object* v___x_7066_; lean_object* v___x_7067_; uint8_t v___x_7068_; lean_object* v___x_7069_; 
v___x_7061_ = lean_io_get_num_heartbeats();
v___x_7062_ = lean_float_of_nat(v___y_7059_);
v___x_7063_ = lean_float_of_nat(v___x_7061_);
v___x_7064_ = lean_box_float(v___x_7062_);
v___x_7065_ = lean_box_float(v___x_7063_);
v___x_7066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7066_, 0, v___x_7064_);
lean_ctor_set(v___x_7066_, 1, v___x_7065_);
v___x_7067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7067_, 0, v_a_7060_);
lean_ctor_set(v___x_7067_, 1, v___x_7066_);
v___x_7068_ = lean_unbox(v_a_7039_);
lean_dec(v_a_7039_);
v___x_7069_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5(v___x_7037_, v___x_7005_, v___x_7040_, v_options_7027_, v___x_7068_, v___y_7058_, v___f_7007_, v___x_7067_, v___y_7008_, v___y_7009_, v___y_7010_, v___y_7011_);
return v___x_7069_;
}
v___jp_7070_:
{
lean_object* v___x_7071_; lean_object* v_a_7072_; lean_object* v___x_7073_; uint8_t v___x_7074_; 
v___x_7071_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_mkSizeOfInstances_spec__4___redArg(v___y_7011_);
v_a_7072_ = lean_ctor_get(v___x_7071_, 0);
lean_inc(v_a_7072_);
lean_dec_ref(v___x_7071_);
v___x_7073_ = l_Lean_trace_profiler_useHeartbeats;
v___x_7074_ = l_Lean_Option_get___at___00Lean_Meta_mkSizeOfInstances_spec__1(v_options_7027_, v___x_7073_);
if (v___x_7074_ == 0)
{
lean_object* v___x_7075_; lean_object* v___x_7076_; 
v___x_7075_ = lean_io_mono_nanos_now();
v___x_7076_ = l_Lean_Meta_mkSizeOfInstances___lam__2(v_isUnsafe_7036_, v_typeName_7004_, v_all_7035_, v___y_7008_, v___y_7009_, v___y_7010_, v___y_7011_);
if (lean_obj_tag(v___x_7076_) == 0)
{
lean_object* v_a_7077_; lean_object* v___x_7079_; uint8_t v_isShared_7080_; uint8_t v_isSharedCheck_7084_; 
v_a_7077_ = lean_ctor_get(v___x_7076_, 0);
v_isSharedCheck_7084_ = !lean_is_exclusive(v___x_7076_);
if (v_isSharedCheck_7084_ == 0)
{
v___x_7079_ = v___x_7076_;
v_isShared_7080_ = v_isSharedCheck_7084_;
goto v_resetjp_7078_;
}
else
{
lean_inc(v_a_7077_);
lean_dec(v___x_7076_);
v___x_7079_ = lean_box(0);
v_isShared_7080_ = v_isSharedCheck_7084_;
goto v_resetjp_7078_;
}
v_resetjp_7078_:
{
lean_object* v___x_7082_; 
if (v_isShared_7080_ == 0)
{
lean_ctor_set_tag(v___x_7079_, 1);
v___x_7082_ = v___x_7079_;
goto v_reusejp_7081_;
}
else
{
lean_object* v_reuseFailAlloc_7083_; 
v_reuseFailAlloc_7083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7083_, 0, v_a_7077_);
v___x_7082_ = v_reuseFailAlloc_7083_;
goto v_reusejp_7081_;
}
v_reusejp_7081_:
{
v___y_7042_ = v_a_7072_;
v___y_7043_ = v___x_7075_;
v_a_7044_ = v___x_7082_;
goto v___jp_7041_;
}
}
}
else
{
lean_object* v_a_7085_; lean_object* v___x_7087_; uint8_t v_isShared_7088_; uint8_t v_isSharedCheck_7092_; 
v_a_7085_ = lean_ctor_get(v___x_7076_, 0);
v_isSharedCheck_7092_ = !lean_is_exclusive(v___x_7076_);
if (v_isSharedCheck_7092_ == 0)
{
v___x_7087_ = v___x_7076_;
v_isShared_7088_ = v_isSharedCheck_7092_;
goto v_resetjp_7086_;
}
else
{
lean_inc(v_a_7085_);
lean_dec(v___x_7076_);
v___x_7087_ = lean_box(0);
v_isShared_7088_ = v_isSharedCheck_7092_;
goto v_resetjp_7086_;
}
v_resetjp_7086_:
{
lean_object* v___x_7090_; 
if (v_isShared_7088_ == 0)
{
lean_ctor_set_tag(v___x_7087_, 0);
v___x_7090_ = v___x_7087_;
goto v_reusejp_7089_;
}
else
{
lean_object* v_reuseFailAlloc_7091_; 
v_reuseFailAlloc_7091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7091_, 0, v_a_7085_);
v___x_7090_ = v_reuseFailAlloc_7091_;
goto v_reusejp_7089_;
}
v_reusejp_7089_:
{
v___y_7042_ = v_a_7072_;
v___y_7043_ = v___x_7075_;
v_a_7044_ = v___x_7090_;
goto v___jp_7041_;
}
}
}
}
else
{
lean_object* v___x_7093_; lean_object* v___x_7094_; 
v___x_7093_ = lean_io_get_num_heartbeats();
v___x_7094_ = l_Lean_Meta_mkSizeOfInstances___lam__2(v_isUnsafe_7036_, v_typeName_7004_, v_all_7035_, v___y_7008_, v___y_7009_, v___y_7010_, v___y_7011_);
if (lean_obj_tag(v___x_7094_) == 0)
{
lean_object* v_a_7095_; lean_object* v___x_7097_; uint8_t v_isShared_7098_; uint8_t v_isSharedCheck_7102_; 
v_a_7095_ = lean_ctor_get(v___x_7094_, 0);
v_isSharedCheck_7102_ = !lean_is_exclusive(v___x_7094_);
if (v_isSharedCheck_7102_ == 0)
{
v___x_7097_ = v___x_7094_;
v_isShared_7098_ = v_isSharedCheck_7102_;
goto v_resetjp_7096_;
}
else
{
lean_inc(v_a_7095_);
lean_dec(v___x_7094_);
v___x_7097_ = lean_box(0);
v_isShared_7098_ = v_isSharedCheck_7102_;
goto v_resetjp_7096_;
}
v_resetjp_7096_:
{
lean_object* v___x_7100_; 
if (v_isShared_7098_ == 0)
{
lean_ctor_set_tag(v___x_7097_, 1);
v___x_7100_ = v___x_7097_;
goto v_reusejp_7099_;
}
else
{
lean_object* v_reuseFailAlloc_7101_; 
v_reuseFailAlloc_7101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7101_, 0, v_a_7095_);
v___x_7100_ = v_reuseFailAlloc_7101_;
goto v_reusejp_7099_;
}
v_reusejp_7099_:
{
v___y_7058_ = v_a_7072_;
v___y_7059_ = v___x_7093_;
v_a_7060_ = v___x_7100_;
goto v___jp_7057_;
}
}
}
else
{
lean_object* v_a_7103_; lean_object* v___x_7105_; uint8_t v_isShared_7106_; uint8_t v_isSharedCheck_7110_; 
v_a_7103_ = lean_ctor_get(v___x_7094_, 0);
v_isSharedCheck_7110_ = !lean_is_exclusive(v___x_7094_);
if (v_isSharedCheck_7110_ == 0)
{
v___x_7105_ = v___x_7094_;
v_isShared_7106_ = v_isSharedCheck_7110_;
goto v_resetjp_7104_;
}
else
{
lean_inc(v_a_7103_);
lean_dec(v___x_7094_);
v___x_7105_ = lean_box(0);
v_isShared_7106_ = v_isSharedCheck_7110_;
goto v_resetjp_7104_;
}
v_resetjp_7104_:
{
lean_object* v___x_7108_; 
if (v_isShared_7106_ == 0)
{
lean_ctor_set_tag(v___x_7105_, 0);
v___x_7108_ = v___x_7105_;
goto v_reusejp_7107_;
}
else
{
lean_object* v_reuseFailAlloc_7109_; 
v_reuseFailAlloc_7109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7109_, 0, v_a_7103_);
v___x_7108_ = v_reuseFailAlloc_7109_;
goto v_reusejp_7107_;
}
v_reusejp_7107_:
{
v___y_7058_ = v_a_7072_;
v___y_7059_ = v___x_7093_;
v_a_7060_ = v___x_7108_;
goto v___jp_7057_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___f_7007_);
lean_dec_ref(v_a_7006_);
lean_dec(v_typeName_7004_);
goto v___jp_7019_;
}
}
}
v___jp_7019_:
{
lean_object* v___x_7020_; lean_object* v___x_7022_; 
v___x_7020_ = lean_box(0);
if (v_isShared_7018_ == 0)
{
lean_ctor_set(v___x_7017_, 0, v___x_7020_);
v___x_7022_ = v___x_7017_;
goto v_reusejp_7021_;
}
else
{
lean_object* v_reuseFailAlloc_7023_; 
v_reuseFailAlloc_7023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7023_, 0, v___x_7020_);
v___x_7022_ = v_reuseFailAlloc_7023_;
goto v_reusejp_7021_;
}
v_reusejp_7021_:
{
return v___x_7022_;
}
}
}
}
else
{
lean_object* v_a_7116_; lean_object* v___x_7118_; uint8_t v_isShared_7119_; uint8_t v_isSharedCheck_7123_; 
lean_dec(v___x_7013_);
lean_dec_ref(v___f_7007_);
lean_dec_ref(v_a_7006_);
lean_dec(v_typeName_7004_);
v_a_7116_ = lean_ctor_get(v___x_7014_, 0);
v_isSharedCheck_7123_ = !lean_is_exclusive(v___x_7014_);
if (v_isSharedCheck_7123_ == 0)
{
v___x_7118_ = v___x_7014_;
v_isShared_7119_ = v_isSharedCheck_7123_;
goto v_resetjp_7117_;
}
else
{
lean_inc(v_a_7116_);
lean_dec(v___x_7014_);
v___x_7118_ = lean_box(0);
v_isShared_7119_ = v_isSharedCheck_7123_;
goto v_resetjp_7117_;
}
v_resetjp_7117_:
{
lean_object* v___x_7121_; 
if (v_isShared_7119_ == 0)
{
v___x_7121_ = v___x_7118_;
goto v_reusejp_7120_;
}
else
{
lean_object* v_reuseFailAlloc_7122_; 
v_reuseFailAlloc_7122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7122_, 0, v_a_7116_);
v___x_7121_ = v_reuseFailAlloc_7122_;
goto v_reusejp_7120_;
}
v_reusejp_7120_:
{
return v___x_7121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfInstances___lam__3___boxed(lean_object* v_typeName_7124_, lean_object* v___x_7125_, lean_object* v_a_7126_, lean_object* v___f_7127_, lean_object* v___y_7128_, lean_object* v___y_7129_, lean_object* v___y_7130_, lean_object* v___y_7131_, lean_object* v___y_7132_){
_start:
{
uint8_t v___x_18754__boxed_7133_; lean_object* v_res_7134_; 
v___x_18754__boxed_7133_ = lean_unbox(v___x_7125_);
v_res_7134_ = l_Lean_Meta_mkSizeOfInstances___lam__3(v_typeName_7124_, v___x_18754__boxed_7133_, v_a_7126_, v___f_7127_, v___y_7128_, v___y_7129_, v___y_7130_, v___y_7131_);
lean_dec(v___y_7131_);
lean_dec_ref(v___y_7130_);
lean_dec(v___y_7129_);
lean_dec_ref(v___y_7128_);
return v_res_7134_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkSizeOfInstances_spec__0___redArg(lean_object* v_x_7135_, uint8_t v_when_7136_, lean_object* v___y_7137_, lean_object* v___y_7138_, lean_object* v___y_7139_, lean_object* v___y_7140_){
_start:
{
if (v_when_7136_ == 0)
{
lean_object* v___x_7142_; 
lean_inc(v___y_7140_);
lean_inc_ref(v___y_7139_);
lean_inc(v___y_7138_);
lean_inc_ref(v___y_7137_);
v___x_7142_ = lean_apply_5(v_x_7135_, v___y_7137_, v___y_7138_, v___y_7139_, v___y_7140_, lean_box(0));
return v___x_7142_;
}
else
{
uint8_t v___x_7143_; lean_object* v___x_7144_; 
v___x_7143_ = 0;
v___x_7144_ = l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg(v_x_7135_, v___x_7143_, v___y_7137_, v___y_7138_, v___y_7139_, v___y_7140_);
return v___x_7144_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkSizeOfInstances_spec__0___redArg___boxed(lean_object* v_x_7145_, lean_object* v_when_7146_, lean_object* v___y_7147_, lean_object* v___y_7148_, lean_object* v___y_7149_, lean_object* v___y_7150_, lean_object* v___y_7151_){
_start:
{
uint8_t v_when_boxed_7152_; lean_object* v_res_7153_; 
v_when_boxed_7152_ = lean_unbox(v_when_7146_);
v_res_7153_ = l_Lean_withoutExporting___at___00Lean_Meta_mkSizeOfInstances_spec__0___redArg(v_x_7145_, v_when_boxed_7152_, v___y_7147_, v___y_7148_, v___y_7149_, v___y_7150_);
lean_dec(v___y_7150_);
lean_dec_ref(v___y_7149_);
lean_dec(v___y_7148_);
lean_dec_ref(v___y_7147_);
return v_res_7153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfInstances___lam__4(lean_object* v___x_7155_, uint8_t v___x_7156_, lean_object* v_typeName_7157_, lean_object* v___f_7158_, uint8_t v___x_7159_, lean_object* v___y_7160_, lean_object* v___y_7161_, lean_object* v___y_7162_, lean_object* v___y_7163_){
_start:
{
lean_object* v___x_7165_; 
v___x_7165_ = l_Lean_withoutExporting___at___00Lean_Meta_mkSizeOfInstances_spec__0___redArg(v___x_7155_, v___x_7156_, v___y_7160_, v___y_7161_, v___y_7162_, v___y_7163_);
if (lean_obj_tag(v___x_7165_) == 0)
{
lean_object* v_a_7166_; lean_object* v___x_7167_; lean_object* v___f_7168_; uint8_t v___x_7169_; 
v_a_7166_ = lean_ctor_get(v___x_7165_, 0);
lean_inc(v_a_7166_);
lean_dec_ref(v___x_7165_);
v___x_7167_ = lean_box(v___x_7156_);
lean_inc(v_a_7166_);
lean_inc(v_typeName_7157_);
v___f_7168_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSizeOfInstances___lam__3___boxed), 9, 4);
lean_closure_set(v___f_7168_, 0, v_typeName_7157_);
lean_closure_set(v___f_7168_, 1, v___x_7167_);
lean_closure_set(v___f_7168_, 2, v_a_7166_);
lean_closure_set(v___f_7168_, 3, v___f_7158_);
v___x_7169_ = l_Lean_isPrivateName(v_typeName_7157_);
lean_dec(v_typeName_7157_);
if (v___x_7169_ == 0)
{
lean_object* v_ctors_7170_; lean_object* v___x_7171_; uint8_t v___x_7172_; 
v_ctors_7170_ = lean_ctor_get(v_a_7166_, 4);
lean_inc(v_ctors_7170_);
lean_dec(v_a_7166_);
v___x_7171_ = ((lean_object*)(l_Lean_Meta_mkSizeOfInstances___lam__4___closed__0));
v___x_7172_ = l_List_any___redArg(v_ctors_7170_, v___x_7171_);
if (v___x_7172_ == 0)
{
lean_object* v___x_7173_; 
v___x_7173_ = l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg(v___f_7168_, v___x_7156_, v___y_7160_, v___y_7161_, v___y_7162_, v___y_7163_);
return v___x_7173_;
}
else
{
lean_object* v___x_7174_; 
v___x_7174_ = l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg(v___f_7168_, v___x_7169_, v___y_7160_, v___y_7161_, v___y_7162_, v___y_7163_);
return v___x_7174_;
}
}
else
{
lean_object* v___x_7175_; 
lean_dec(v_a_7166_);
v___x_7175_ = l_Lean_withExporting___at___00Lean_Meta_mkSizeOfFn_spec__2___redArg(v___f_7168_, v___x_7159_, v___y_7160_, v___y_7161_, v___y_7162_, v___y_7163_);
return v___x_7175_;
}
}
else
{
lean_object* v_a_7176_; lean_object* v___x_7178_; uint8_t v_isShared_7179_; uint8_t v_isSharedCheck_7183_; 
lean_dec_ref(v___f_7158_);
lean_dec(v_typeName_7157_);
v_a_7176_ = lean_ctor_get(v___x_7165_, 0);
v_isSharedCheck_7183_ = !lean_is_exclusive(v___x_7165_);
if (v_isSharedCheck_7183_ == 0)
{
v___x_7178_ = v___x_7165_;
v_isShared_7179_ = v_isSharedCheck_7183_;
goto v_resetjp_7177_;
}
else
{
lean_inc(v_a_7176_);
lean_dec(v___x_7165_);
v___x_7178_ = lean_box(0);
v_isShared_7179_ = v_isSharedCheck_7183_;
goto v_resetjp_7177_;
}
v_resetjp_7177_:
{
lean_object* v___x_7181_; 
if (v_isShared_7179_ == 0)
{
v___x_7181_ = v___x_7178_;
goto v_reusejp_7180_;
}
else
{
lean_object* v_reuseFailAlloc_7182_; 
v_reuseFailAlloc_7182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7182_, 0, v_a_7176_);
v___x_7181_ = v_reuseFailAlloc_7182_;
goto v_reusejp_7180_;
}
v_reusejp_7180_:
{
return v___x_7181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfInstances___lam__4___boxed(lean_object* v___x_7184_, lean_object* v___x_7185_, lean_object* v_typeName_7186_, lean_object* v___f_7187_, lean_object* v___x_7188_, lean_object* v___y_7189_, lean_object* v___y_7190_, lean_object* v___y_7191_, lean_object* v___y_7192_, lean_object* v___y_7193_){
_start:
{
uint8_t v___x_19014__boxed_7194_; uint8_t v___x_19016__boxed_7195_; lean_object* v_res_7196_; 
v___x_19014__boxed_7194_ = lean_unbox(v___x_7185_);
v___x_19016__boxed_7195_ = lean_unbox(v___x_7188_);
v_res_7196_ = l_Lean_Meta_mkSizeOfInstances___lam__4(v___x_7184_, v___x_19014__boxed_7194_, v_typeName_7186_, v___f_7187_, v___x_19016__boxed_7195_, v___y_7189_, v___y_7190_, v___y_7191_, v___y_7192_);
lean_dec(v___y_7192_);
lean_dec_ref(v___y_7191_);
lean_dec(v___y_7190_);
lean_dec_ref(v___y_7189_);
return v_res_7196_;
}
}
static lean_object* _init_l_Lean_Meta_mkSizeOfInstances___closed__1(void){
_start:
{
lean_object* v___x_7198_; lean_object* v___x_7199_; 
v___x_7198_ = ((lean_object*)(l_Lean_Meta_mkSizeOfInstances___closed__0));
v___x_7199_ = l_Lean_stringToMessageData(v___x_7198_);
return v___x_7199_;
}
}
static lean_object* _init_l_Lean_Meta_mkSizeOfInstances___closed__3(void){
_start:
{
lean_object* v___x_7201_; lean_object* v___x_7202_; 
v___x_7201_ = ((lean_object*)(l_Lean_Meta_mkSizeOfInstances___closed__2));
v___x_7202_ = l_Lean_stringToMessageData(v___x_7201_);
return v___x_7202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfInstances(lean_object* v_typeName_7203_, lean_object* v_a_7204_, lean_object* v_a_7205_, lean_object* v_a_7206_, lean_object* v_a_7207_){
_start:
{
lean_object* v___f_7209_; lean_object* v___x_7210_; uint8_t v___x_7211_; lean_object* v___x_7212_; lean_object* v___x_7213_; lean_object* v___x_7214_; lean_object* v___x_7215_; lean_object* v___f_7216_; lean_object* v___x_7217_; uint8_t v___x_7218_; lean_object* v___x_7219_; lean_object* v___x_7220_; lean_object* v___f_7221_; lean_object* v___x_7222_; 
lean_inc(v_typeName_7203_);
v___f_7209_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSizeOfInstances___lam__0___boxed), 7, 1);
lean_closure_set(v___f_7209_, 0, v_typeName_7203_);
v___x_7210_ = lean_obj_once(&l_Lean_Meta_mkSizeOfInstances___closed__1, &l_Lean_Meta_mkSizeOfInstances___closed__1_once, _init_l_Lean_Meta_mkSizeOfInstances___closed__1);
v___x_7211_ = 0;
lean_inc(v_typeName_7203_);
v___x_7212_ = l_Lean_MessageData_ofConstName(v_typeName_7203_, v___x_7211_);
v___x_7213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7213_, 0, v___x_7210_);
lean_ctor_set(v___x_7213_, 1, v___x_7212_);
v___x_7214_ = lean_obj_once(&l_Lean_Meta_mkSizeOfInstances___closed__3, &l_Lean_Meta_mkSizeOfInstances___closed__3_once, _init_l_Lean_Meta_mkSizeOfInstances___closed__3);
v___x_7215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7215_, 0, v___x_7213_);
lean_ctor_set(v___x_7215_, 1, v___x_7214_);
v___f_7216_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSizeOfInstances___lam__1), 2, 1);
lean_closure_set(v___f_7216_, 0, v___x_7215_);
lean_inc(v_typeName_7203_);
v___x_7217_ = lean_alloc_closure((void*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSizeOfFns_spec__0___boxed), 6, 1);
lean_closure_set(v___x_7217_, 0, v_typeName_7203_);
v___x_7218_ = 1;
v___x_7219_ = lean_box(v___x_7218_);
v___x_7220_ = lean_box(v___x_7211_);
v___f_7221_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSizeOfInstances___lam__4___boxed), 10, 5);
lean_closure_set(v___f_7221_, 0, v___x_7217_);
lean_closure_set(v___f_7221_, 1, v___x_7219_);
lean_closure_set(v___f_7221_, 2, v_typeName_7203_);
lean_closure_set(v___f_7221_, 3, v___f_7209_);
lean_closure_set(v___f_7221_, 4, v___x_7220_);
v___x_7222_ = l_Lean_Meta_mapErrorImp___redArg(v___f_7221_, v___f_7216_, v_a_7204_, v_a_7205_, v_a_7206_, v_a_7207_);
if (lean_obj_tag(v___x_7222_) == 0)
{
lean_object* v_a_7223_; lean_object* v___x_7225_; uint8_t v_isShared_7226_; uint8_t v_isSharedCheck_7230_; 
v_a_7223_ = lean_ctor_get(v___x_7222_, 0);
v_isSharedCheck_7230_ = !lean_is_exclusive(v___x_7222_);
if (v_isSharedCheck_7230_ == 0)
{
v___x_7225_ = v___x_7222_;
v_isShared_7226_ = v_isSharedCheck_7230_;
goto v_resetjp_7224_;
}
else
{
lean_inc(v_a_7223_);
lean_dec(v___x_7222_);
v___x_7225_ = lean_box(0);
v_isShared_7226_ = v_isSharedCheck_7230_;
goto v_resetjp_7224_;
}
v_resetjp_7224_:
{
lean_object* v___x_7228_; 
if (v_isShared_7226_ == 0)
{
v___x_7228_ = v___x_7225_;
goto v_reusejp_7227_;
}
else
{
lean_object* v_reuseFailAlloc_7229_; 
v_reuseFailAlloc_7229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7229_, 0, v_a_7223_);
v___x_7228_ = v_reuseFailAlloc_7229_;
goto v_reusejp_7227_;
}
v_reusejp_7227_:
{
return v___x_7228_;
}
}
}
else
{
lean_object* v_a_7231_; lean_object* v___x_7233_; uint8_t v_isShared_7234_; uint8_t v_isSharedCheck_7238_; 
v_a_7231_ = lean_ctor_get(v___x_7222_, 0);
v_isSharedCheck_7238_ = !lean_is_exclusive(v___x_7222_);
if (v_isSharedCheck_7238_ == 0)
{
v___x_7233_ = v___x_7222_;
v_isShared_7234_ = v_isSharedCheck_7238_;
goto v_resetjp_7232_;
}
else
{
lean_inc(v_a_7231_);
lean_dec(v___x_7222_);
v___x_7233_ = lean_box(0);
v_isShared_7234_ = v_isSharedCheck_7238_;
goto v_resetjp_7232_;
}
v_resetjp_7232_:
{
lean_object* v___x_7236_; 
if (v_isShared_7234_ == 0)
{
v___x_7236_ = v___x_7233_;
goto v_reusejp_7235_;
}
else
{
lean_object* v_reuseFailAlloc_7237_; 
v_reuseFailAlloc_7237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7237_, 0, v_a_7231_);
v___x_7236_ = v_reuseFailAlloc_7237_;
goto v_reusejp_7235_;
}
v_reusejp_7235_:
{
return v___x_7236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSizeOfInstances___boxed(lean_object* v_typeName_7239_, lean_object* v_a_7240_, lean_object* v_a_7241_, lean_object* v_a_7242_, lean_object* v_a_7243_, lean_object* v_a_7244_){
_start:
{
lean_object* v_res_7245_; 
v_res_7245_ = l_Lean_Meta_mkSizeOfInstances(v_typeName_7239_, v_a_7240_, v_a_7241_, v_a_7242_, v_a_7243_);
lean_dec(v_a_7243_);
lean_dec_ref(v_a_7242_);
lean_dec(v_a_7241_);
lean_dec_ref(v_a_7240_);
return v_res_7245_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkSizeOfInstances_spec__0(lean_object* v_00_u03b1_7246_, lean_object* v_x_7247_, uint8_t v_when_7248_, lean_object* v___y_7249_, lean_object* v___y_7250_, lean_object* v___y_7251_, lean_object* v___y_7252_){
_start:
{
lean_object* v___x_7254_; 
v___x_7254_ = l_Lean_withoutExporting___at___00Lean_Meta_mkSizeOfInstances_spec__0___redArg(v_x_7247_, v_when_7248_, v___y_7249_, v___y_7250_, v___y_7251_, v___y_7252_);
return v___x_7254_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkSizeOfInstances_spec__0___boxed(lean_object* v_00_u03b1_7255_, lean_object* v_x_7256_, lean_object* v_when_7257_, lean_object* v___y_7258_, lean_object* v___y_7259_, lean_object* v___y_7260_, lean_object* v___y_7261_, lean_object* v___y_7262_){
_start:
{
uint8_t v_when_boxed_7263_; lean_object* v_res_7264_; 
v_when_boxed_7263_ = lean_unbox(v_when_7257_);
v_res_7264_ = l_Lean_withoutExporting___at___00Lean_Meta_mkSizeOfInstances_spec__0(v_00_u03b1_7255_, v_x_7256_, v_when_boxed_7263_, v___y_7258_, v___y_7259_, v___y_7260_, v___y_7261_);
lean_dec(v___y_7261_);
lean_dec_ref(v___y_7260_);
lean_dec(v___y_7259_);
lean_dec_ref(v___y_7258_);
return v_res_7264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSizeOfInstances_spec__2(lean_object* v_00_u03b1_7265_, lean_object* v_name_7266_, lean_object* v_type_7267_, lean_object* v_k_7268_, lean_object* v___y_7269_, lean_object* v___y_7270_, lean_object* v___y_7271_, lean_object* v___y_7272_){
_start:
{
lean_object* v___x_7274_; 
v___x_7274_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSizeOfInstances_spec__2___redArg(v_name_7266_, v_type_7267_, v_k_7268_, v___y_7269_, v___y_7270_, v___y_7271_, v___y_7272_);
return v___x_7274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSizeOfInstances_spec__2___boxed(lean_object* v_00_u03b1_7275_, lean_object* v_name_7276_, lean_object* v_type_7277_, lean_object* v_k_7278_, lean_object* v___y_7279_, lean_object* v___y_7280_, lean_object* v___y_7281_, lean_object* v___y_7282_, lean_object* v___y_7283_){
_start:
{
lean_object* v_res_7284_; 
v_res_7284_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSizeOfInstances_spec__2(v_00_u03b1_7275_, v_name_7276_, v_type_7277_, v_k_7278_, v___y_7279_, v___y_7280_, v___y_7281_, v___y_7282_);
lean_dec(v___y_7282_);
lean_dec_ref(v___y_7281_);
lean_dec(v___y_7280_);
lean_dec_ref(v___y_7279_);
return v_res_7284_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3(lean_object* v_as_7285_, lean_object* v_as_x27_7286_, lean_object* v_b_7287_, lean_object* v_a_7288_, lean_object* v___y_7289_, lean_object* v___y_7290_, lean_object* v___y_7291_, lean_object* v___y_7292_){
_start:
{
lean_object* v___x_7294_; 
v___x_7294_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___redArg(v_as_x27_7286_, v_b_7287_, v___y_7289_, v___y_7290_, v___y_7291_, v___y_7292_);
return v___x_7294_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3___boxed(lean_object* v_as_7295_, lean_object* v_as_x27_7296_, lean_object* v_b_7297_, lean_object* v_a_7298_, lean_object* v___y_7299_, lean_object* v___y_7300_, lean_object* v___y_7301_, lean_object* v___y_7302_, lean_object* v___y_7303_){
_start:
{
lean_object* v_res_7304_; 
v_res_7304_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkSizeOfInstances_spec__3(v_as_7295_, v_as_x27_7296_, v_b_7297_, v_a_7298_, v___y_7299_, v___y_7300_, v___y_7301_, v___y_7302_);
lean_dec(v___y_7302_);
lean_dec_ref(v___y_7301_);
lean_dec(v___y_7300_);
lean_dec_ref(v___y_7299_);
lean_dec(v_as_7295_);
return v_res_7304_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__7(lean_object* v_00_u03b1_7305_, lean_object* v_x_7306_, lean_object* v___y_7307_, lean_object* v___y_7308_, lean_object* v___y_7309_, lean_object* v___y_7310_){
_start:
{
lean_object* v___x_7312_; 
v___x_7312_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__7___redArg(v_x_7306_);
return v___x_7312_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__7___boxed(lean_object* v_00_u03b1_7313_, lean_object* v_x_7314_, lean_object* v___y_7315_, lean_object* v___y_7316_, lean_object* v___y_7317_, lean_object* v___y_7318_, lean_object* v___y_7319_){
_start:
{
lean_object* v_res_7320_; 
v_res_7320_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_mkSizeOfInstances_spec__5_spec__7(v_00_u03b1_7313_, v_x_7314_, v___y_7315_, v___y_7316_, v___y_7317_, v___y_7318_);
lean_dec(v___y_7318_);
lean_dec_ref(v___y_7317_);
lean_dec(v___y_7316_);
lean_dec_ref(v___y_7315_);
return v_res_7320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_7375_; uint8_t v___x_7376_; lean_object* v___x_7377_; lean_object* v___x_7378_; 
v___x_7375_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_mkSizeOfMotives_loop___redArg___closed__2));
v___x_7376_ = 0;
v___x_7377_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2_));
v___x_7378_ = l_Lean_registerTraceClass(v___x_7375_, v___x_7376_, v___x_7377_);
if (lean_obj_tag(v___x_7378_) == 0)
{
lean_object* v___x_7379_; lean_object* v___x_7380_; 
lean_dec_ref(v___x_7378_);
v___x_7379_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProof___closed__7));
v___x_7380_ = l_Lean_registerTraceClass(v___x_7379_, v___x_7376_, v___x_7377_);
if (lean_obj_tag(v___x_7380_) == 0)
{
lean_object* v___x_7381_; lean_object* v___x_7382_; 
lean_dec_ref(v___x_7380_);
v___x_7381_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkMinorProofStep___closed__2));
v___x_7382_ = l_Lean_registerTraceClass(v___x_7381_, v___x_7376_, v___x_7377_);
if (lean_obj_tag(v___x_7382_) == 0)
{
lean_object* v___x_7383_; lean_object* v___x_7384_; 
lean_dec_ref(v___x_7382_);
v___x_7383_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_mkSizeOfAuxLemma___closed__2));
v___x_7384_ = l_Lean_registerTraceClass(v___x_7383_, v___x_7376_, v___x_7377_);
if (lean_obj_tag(v___x_7384_) == 0)
{
lean_object* v___x_7385_; lean_object* v___x_7386_; 
lean_dec_ref(v___x_7384_);
v___x_7385_ = ((lean_object*)(l___private_Lean_Meta_SizeOf_0__Lean_Meta_SizeOfSpecNested_main_loop___closed__1));
v___x_7386_ = l_Lean_registerTraceClass(v___x_7385_, v___x_7376_, v___x_7377_);
return v___x_7386_;
}
else
{
return v___x_7384_;
}
}
else
{
return v___x_7382_;
}
}
else
{
return v___x_7380_;
}
}
else
{
return v___x_7378_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2____boxed(lean_object* v_a_7387_){
_start:
{
lean_object* v_res_7388_; 
v_res_7388_ = l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2_();
return v_res_7388_;
}
}
lean_object* runtime_initialize_Lean_AddDecl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_DefEqAttrib(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_SizeOf(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DefEqAttrib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_SizeOf_3942519336____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_genSizeOf = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_genSizeOf);
lean_dec_ref(res);
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_SizeOf_3847602515____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_genSizeOfSpec = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_genSizeOfSpec);
lean_dec_ref(res);
res = l___private_Lean_Meta_SizeOf_0__Lean_Meta_initFn_00___x40_Lean_Meta_SizeOf_726572898____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_SizeOf(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_AddDecl(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Lean_DefEqAttrib(uint8_t builtin);
lean_object* initialize_Lean_Meta_WHNF(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_SizeOf(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DefEqAttrib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_SizeOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_SizeOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_SizeOf(builtin);
}
#ifdef __cplusplus
}
#endif
