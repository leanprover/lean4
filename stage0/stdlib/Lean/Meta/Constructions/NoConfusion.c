// Lean compiler output
// Module: Lean.Meta.Constructions.NoConfusion
// Imports: public import Lean.Meta.Basic import Lean.AddDecl import Lean.Meta.CompletionName import Lean.Meta.Constructions.CtorIdx import Lean.Meta.Constructions.CtorElim import Lean.Meta.Tactic.Subst
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_arrowDomainsN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withPrimedNamesImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConstructorElimName(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkCtorIdxName(lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Expr_getNumHeadForalls(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_mkHEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_markNoConfusion(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addProtected(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_inlineExpr(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_Lean_Meta_isPropFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isHEq(lean_object*);
uint8_t l_Lean_Expr_isEq(lean_object*);
lean_object* l_Lean_Meta_mkHEqOfEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object*);
lean_object* l_Lean_mkCtorElimName(lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Meta_addToCompletionBlackList(lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__3___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "_eq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__1___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__1___boxed__const__1 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__1___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__1___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__1___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__1___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__1___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__3;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__5_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__6 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "backward"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "linearNoConfusionType"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(77, 196, 98, 49, 58, 220, 29, 220)}};
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(99, 138, 66, 117, 159, 86, 236, 197)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 169, .m_capacity = 169, .m_length = 168, .m_data = "use the linear-size construction for the `noConfusionType` declaration of an inductive type. Set to false to use the previous, simpler but quadratic-size construction. "};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Constructions"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(224, 107, 212, 234, 74, 49, 105, 87)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NoConfusion"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(242, 226, 189, 184, 34, 9, 145, 77)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(243, 97, 90, 160, 238, 101, 199, 199)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(222, 208, 180, 151, 219, 122, 10, 90)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(108, 188, 28, 28, 216, 178, 98, 147)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(110, 139, 60, 224, 105, 18, 245, 237)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_backward_linearNoConfusionType;
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionTypeName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "noConfusionType"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionTypeName___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionTypeName___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionTypeName(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__1___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "propIntro"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear___closed__1 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(189, 136, 38, 165, 207, 169, 133, 34)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear___closed__2 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__1;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__2 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__3;
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__4 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__4_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__5 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__6;
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dite"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__7 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__7_value),LEAN_SCALAR_PTR_LITERAL(137, 166, 197, 161, 68, 218, 116, 116)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__8 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "decEq"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__9 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__4_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__9_value),LEAN_SCALAR_PTR_LITERAL(13, 188, 70, 193, 211, 173, 121, 176)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__10 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__11;
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__12 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__12_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__13 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__13_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__3___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg___lam__0(uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__7___boxed(lean_object**);
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__0;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__1;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__2(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "P"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 230, 119, 31, 245, 11, 149, 236)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__1 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Meta.Constructions.NoConfusion"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__2 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "_private.Lean.Meta.Constructions.NoConfusion.0.Lean.mkNoConfusionType"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__3 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "unexpected universe levels on `casesOn`"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__4 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__5;
static lean_once_cell_t l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "eq"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(186, 128, 88, 209, 81, 126, 91, 90)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "assigning "};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__1;
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__3;
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " to\n"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "substituting "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "mkNoConfusion"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 254, 12, 114, 22, 254, 114, 81)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__8_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__9___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__6(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__0___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___closed__1_value)} };
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "_private.Lean.Meta.Constructions.NoConfusion.0.Lean.mkEqNDRecTelescope"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__1 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "assertion violation: xs.size == ys.size\n  "};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__2 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__3;
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "mkEqNDRecTelescope: "};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__4 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__5;
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ", xs = "};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__6 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__7;
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ", ys = "};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__8 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__9(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "unexpected equation "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = " in `mkNoConfusionCtorArg` for "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "k"};
static const lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__1___closed__0 = (const lean_object*)&l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__1___closed__0_value;
static const lean_ctor_object l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 52, 149, 243, 146, 99, 67, 163)}};
static const lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__1___closed__1 = (const lean_object*)&l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "noConfusion"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__1 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__2;
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "mkNoConfusionCoreImp for "};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__3 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__4;
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = "_private.Lean.Meta.Constructions.NoConfusion.0.Lean.mkNoConfusionCoreImp"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__5 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__6;
static lean_once_cell_t l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "mkNoConfusion: unexpected equality `"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg___closed__1;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "` as next argument to"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__1___boxed(lean_object**);
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__2___closed__0;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "unexpected number of level parameters in "};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "noConfusionTypeEnum"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 165, 206, 44, 96, 147, 97, 117)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "y"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(72, 55, 55, 9, 143, 73, 230, 150)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "v"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 108, 188, 174, 117, 112, 110, 72)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___closed__1 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "_private.Lean.Meta.Constructions.NoConfusion.0.Lean.mkNoConfusionEnum.mkNoConfusionType"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___closed__2 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__0(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__0_value;
static const lean_string_object l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "noConfusionEnum"};
static const lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__1_value;
static const lean_ctor_object l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(244, 62, 217, 237, 101, 163, 189, 62)}};
static const lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__3;
static const lean_string_object l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "p"};
static const lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__4 = (const lean_object*)&l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__4_value;
static const lean_ctor_object l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(34, 153, 146, 175, 179, 220, 230, 134)}};
static const lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__5 = (const lean_object*)&l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 84, .m_capacity = 84, .m_length = 83, .m_data = "_private.Lean.Meta.Constructions.NoConfusion.0.Lean.mkNoConfusionEnum.mkNoConfusion"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkNoConfusion___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkNoConfusion___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__3_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__6___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkNoConfusion___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_mkNoConfusion___closed__0;
LEAN_EXPORT lean_object* l_Lean_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkNoConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(147, 135, 245, 143, 96, 156, 221, 53)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 118, 170, 17, 166, 182, 54, 17)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(47, 129, 60, 177, 70, 185, 44, 157)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(79, 194, 75, 29, 5, 123, 160, 126)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(133, 95, 32, 181, 252, 235, 53, 227)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(123, 1, 25, 118, 32, 179, 240, 245)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1240126624) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(165, 56, 170, 248, 230, 143, 121, 39)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(118, 109, 207, 243, 117, 140, 36, 75)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(202, 97, 60, 203, 218, 46, 246, 159)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(115, 154, 179, 238, 63, 118, 250, 103)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__2___redArg(lean_object* v_xs_1_, lean_object* v_k_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withPrimedNamesImp(lean_box(0), v_xs_1_, v_k_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_);
if (lean_obj_tag(v___x_8_) == 0)
{
lean_object* v_a_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_16_; 
v_a_9_ = lean_ctor_get(v___x_8_, 0);
v_isSharedCheck_16_ = !lean_is_exclusive(v___x_8_);
if (v_isSharedCheck_16_ == 0)
{
v___x_11_ = v___x_8_;
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_a_9_);
lean_dec(v___x_8_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v___x_14_; 
if (v_isShared_12_ == 0)
{
v___x_14_ = v___x_11_;
goto v_reusejp_13_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v_a_9_);
v___x_14_ = v_reuseFailAlloc_15_;
goto v_reusejp_13_;
}
v_reusejp_13_:
{
return v___x_14_;
}
}
}
else
{
lean_object* v_a_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_24_; 
v_a_17_ = lean_ctor_get(v___x_8_, 0);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_8_);
if (v_isSharedCheck_24_ == 0)
{
v___x_19_ = v___x_8_;
v_isShared_20_ = v_isSharedCheck_24_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_a_17_);
lean_dec(v___x_8_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_24_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v___x_22_; 
if (v_isShared_20_ == 0)
{
v___x_22_ = v___x_19_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_a_17_);
v___x_22_ = v_reuseFailAlloc_23_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__2___redArg___boxed(lean_object* v_xs_25_, lean_object* v_k_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__2___redArg(v_xs_25_, v_k_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
lean_dec(v___y_30_);
lean_dec_ref(v___y_29_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__2(lean_object* v_00_u03b1_33_, lean_object* v_xs_34_, lean_object* v_k_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__2___redArg(v_xs_34_, v_k_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__2___boxed(lean_object* v_00_u03b1_42_, lean_object* v_xs_43_, lean_object* v_k_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__2(v_00_u03b1_42_, v_xs_43_, v_k_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec_ref(v___y_45_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__3___redArg___lam__0(lean_object* v_k_51_, lean_object* v_b_52_, lean_object* v_c_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v___x_59_; 
lean_inc(v___y_57_);
lean_inc_ref(v___y_56_);
lean_inc(v___y_55_);
lean_inc_ref(v___y_54_);
v___x_59_ = lean_apply_7(v_k_51_, v_b_52_, v_c_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, lean_box(0));
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__3___redArg___lam__0___boxed(lean_object* v_k_60_, lean_object* v_b_61_, lean_object* v_c_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__3___redArg___lam__0(v_k_60_, v_b_61_, v_c_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
lean_dec(v___y_66_);
lean_dec_ref(v___y_65_);
lean_dec(v___y_64_);
lean_dec_ref(v___y_63_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__3___redArg(lean_object* v_type_69_, lean_object* v_k_70_, uint8_t v_cleanupAnnotations_71_, uint8_t v_whnfType_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_){
_start:
{
lean_object* v___f_78_; lean_object* v___x_79_; 
v___f_78_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_78_, 0, v_k_70_);
v___x_79_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_69_, v___f_78_, v_cleanupAnnotations_71_, v_whnfType_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_);
if (lean_obj_tag(v___x_79_) == 0)
{
lean_object* v_a_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_87_; 
v_a_80_ = lean_ctor_get(v___x_79_, 0);
v_isSharedCheck_87_ = !lean_is_exclusive(v___x_79_);
if (v_isSharedCheck_87_ == 0)
{
v___x_82_ = v___x_79_;
v_isShared_83_ = v_isSharedCheck_87_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_a_80_);
lean_dec(v___x_79_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_87_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_85_; 
if (v_isShared_83_ == 0)
{
v___x_85_ = v___x_82_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v_a_80_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
else
{
lean_object* v_a_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_95_; 
v_a_88_ = lean_ctor_get(v___x_79_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_79_);
if (v_isSharedCheck_95_ == 0)
{
v___x_90_ = v___x_79_;
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_a_88_);
lean_dec(v___x_79_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_93_; 
if (v_isShared_91_ == 0)
{
v___x_93_ = v___x_90_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_a_88_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__3___redArg___boxed(lean_object* v_type_96_, lean_object* v_k_97_, lean_object* v_cleanupAnnotations_98_, lean_object* v_whnfType_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_105_; uint8_t v_whnfType_boxed_106_; lean_object* v_res_107_; 
v_cleanupAnnotations_boxed_105_ = lean_unbox(v_cleanupAnnotations_98_);
v_whnfType_boxed_106_ = lean_unbox(v_whnfType_99_);
v_res_107_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__3___redArg(v_type_96_, v_k_97_, v_cleanupAnnotations_boxed_105_, v_whnfType_boxed_106_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__3(lean_object* v_00_u03b1_108_, lean_object* v_type_109_, lean_object* v_k_110_, uint8_t v_cleanupAnnotations_111_, uint8_t v_whnfType_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__3___redArg(v_type_109_, v_k_110_, v_cleanupAnnotations_111_, v_whnfType_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__3___boxed(lean_object* v_00_u03b1_119_, lean_object* v_type_120_, lean_object* v_k_121_, lean_object* v_cleanupAnnotations_122_, lean_object* v_whnfType_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_129_; uint8_t v_whnfType_boxed_130_; lean_object* v_res_131_; 
v_cleanupAnnotations_boxed_129_ = lean_unbox(v_cleanupAnnotations_122_);
v_whnfType_boxed_130_ = lean_unbox(v_whnfType_123_);
v_res_131_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__3(v_00_u03b1_119_, v_type_120_, v_k_121_, v_cleanupAnnotations_boxed_129_, v_whnfType_boxed_130_, v___y_124_, v___y_125_, v___y_126_, v___y_127_);
lean_dec(v___y_127_);
lean_dec_ref(v___y_126_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(lean_object* v_type_132_, lean_object* v_maxFVars_x3f_133_, lean_object* v_k_134_, uint8_t v_cleanupAnnotations_135_, uint8_t v_whnfType_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v___f_142_; lean_object* v___x_143_; 
v___f_142_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_142_, 0, v_k_134_);
v___x_143_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_132_, v_maxFVars_x3f_133_, v___f_142_, v_cleanupAnnotations_135_, v_whnfType_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
if (lean_obj_tag(v___x_143_) == 0)
{
lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_151_; 
v_a_144_ = lean_ctor_get(v___x_143_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_143_);
if (v_isSharedCheck_151_ == 0)
{
v___x_146_ = v___x_143_;
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___x_143_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_149_; 
if (v_isShared_147_ == 0)
{
v___x_149_ = v___x_146_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_a_144_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
else
{
lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_159_; 
v_a_152_ = lean_ctor_get(v___x_143_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_143_);
if (v_isSharedCheck_159_ == 0)
{
v___x_154_ = v___x_143_;
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___x_143_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_157_; 
if (v_isShared_155_ == 0)
{
v___x_157_ = v___x_154_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_a_152_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg___boxed(lean_object* v_type_160_, lean_object* v_maxFVars_x3f_161_, lean_object* v_k_162_, lean_object* v_cleanupAnnotations_163_, lean_object* v_whnfType_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_170_; uint8_t v_whnfType_boxed_171_; lean_object* v_res_172_; 
v_cleanupAnnotations_boxed_170_ = lean_unbox(v_cleanupAnnotations_163_);
v_whnfType_boxed_171_ = lean_unbox(v_whnfType_164_);
v_res_172_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(v_type_160_, v_maxFVars_x3f_161_, v_k_162_, v_cleanupAnnotations_boxed_170_, v_whnfType_boxed_171_, v___y_165_, v___y_166_, v___y_167_, v___y_168_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4(lean_object* v_00_u03b1_173_, lean_object* v_type_174_, lean_object* v_maxFVars_x3f_175_, lean_object* v_k_176_, uint8_t v_cleanupAnnotations_177_, uint8_t v_whnfType_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(v_type_174_, v_maxFVars_x3f_175_, v_k_176_, v_cleanupAnnotations_177_, v_whnfType_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___boxed(lean_object* v_00_u03b1_185_, lean_object* v_type_186_, lean_object* v_maxFVars_x3f_187_, lean_object* v_k_188_, lean_object* v_cleanupAnnotations_189_, lean_object* v_whnfType_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_196_; uint8_t v_whnfType_boxed_197_; lean_object* v_res_198_; 
v_cleanupAnnotations_boxed_196_ = lean_unbox(v_cleanupAnnotations_189_);
v_whnfType_boxed_197_ = lean_unbox(v_whnfType_190_);
v_res_198_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4(v_00_u03b1_185_, v_type_186_, v_maxFVars_x3f_187_, v_k_188_, v_cleanupAnnotations_boxed_196_, v_whnfType_boxed_197_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__1(lean_object* v_as_200_, size_t v_sz_201_, size_t v_i_202_, lean_object* v_b_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v_a_210_; uint8_t v___x_214_; 
v___x_214_ = lean_usize_dec_lt(v_i_202_, v_sz_201_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; 
v___x_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_215_, 0, v_b_203_);
return v___x_215_;
}
else
{
lean_object* v_snd_216_; lean_object* v_fst_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_285_; 
v_snd_216_ = lean_ctor_get(v_b_203_, 1);
v_fst_217_ = lean_ctor_get(v_b_203_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v_b_203_);
if (v_isSharedCheck_285_ == 0)
{
v___x_219_ = v_b_203_;
v_isShared_220_ = v_isSharedCheck_285_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_snd_216_);
lean_inc(v_fst_217_);
lean_dec(v_b_203_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_285_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v_array_221_; lean_object* v_start_222_; lean_object* v_stop_223_; uint8_t v___x_224_; 
v_array_221_ = lean_ctor_get(v_snd_216_, 0);
v_start_222_ = lean_ctor_get(v_snd_216_, 1);
v_stop_223_ = lean_ctor_get(v_snd_216_, 2);
v___x_224_ = lean_nat_dec_lt(v_start_222_, v_stop_223_);
if (v___x_224_ == 0)
{
lean_object* v___x_226_; 
if (v_isShared_220_ == 0)
{
v___x_226_ = v___x_219_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_fst_217_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_snd_216_);
v___x_226_ = v_reuseFailAlloc_228_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
lean_object* v___x_227_; 
v___x_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
return v___x_227_;
}
}
else
{
lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_281_; 
lean_inc(v_stop_223_);
lean_inc(v_start_222_);
lean_inc_ref(v_array_221_);
v_isSharedCheck_281_ = !lean_is_exclusive(v_snd_216_);
if (v_isSharedCheck_281_ == 0)
{
lean_object* v_unused_282_; lean_object* v_unused_283_; lean_object* v_unused_284_; 
v_unused_282_ = lean_ctor_get(v_snd_216_, 2);
lean_dec(v_unused_282_);
v_unused_283_ = lean_ctor_get(v_snd_216_, 1);
lean_dec(v_unused_283_);
v_unused_284_ = lean_ctor_get(v_snd_216_, 0);
lean_dec(v_unused_284_);
v___x_230_ = v_snd_216_;
v_isShared_231_ = v_isSharedCheck_281_;
goto v_resetjp_229_;
}
else
{
lean_dec(v_snd_216_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_281_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v_a_232_; lean_object* v___x_233_; 
v_a_232_ = lean_array_uget_borrowed(v_as_200_, v_i_202_);
lean_inc(v_a_232_);
v___x_233_ = l_Lean_Meta_isProof(v_a_232_, v___y_204_, v___y_205_, v___y_206_, v___y_207_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_a_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
v_a_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_a_234_);
lean_dec_ref_known(v___x_233_, 1);
v___x_235_ = lean_array_fget(v_array_221_, v_start_222_);
v___x_236_ = lean_unsigned_to_nat(1u);
v___x_237_ = lean_nat_add(v_start_222_, v___x_236_);
lean_dec(v_start_222_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 1, v___x_237_);
v___x_239_ = v___x_230_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_array_221_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v___x_237_);
lean_ctor_set(v_reuseFailAlloc_272_, 2, v_stop_223_);
v___x_239_ = v_reuseFailAlloc_272_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
uint8_t v___x_240_; 
v___x_240_ = lean_unbox(v_a_234_);
lean_dec(v_a_234_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = l_Lean_Expr_fvarId_x21(v_a_232_);
v___x_242_ = l_Lean_FVarId_getUserName___redArg(v___x_241_, v___y_204_, v___y_206_, v___y_207_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_244_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
lean_inc(v_a_243_);
lean_dec_ref_known(v___x_242_, 1);
lean_inc(v_a_232_);
v___x_244_ = l_Lean_Meta_mkEqHEq(v_a_232_, v___x_235_, v___y_204_, v___y_205_, v___y_206_, v___y_207_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_a_245_; lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; lean_object* v___x_249_; lean_object* v___x_251_; 
v_a_245_ = lean_ctor_get(v___x_244_, 0);
lean_inc(v_a_245_);
lean_dec_ref_known(v___x_244_, 1);
v___x_246_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__1___closed__0));
v___x_247_ = lean_name_append_after(v_a_243_, v___x_246_);
v___x_248_ = 0;
v___x_249_ = l_Lean_mkForall(v___x_247_, v___x_248_, v_a_245_, v_fst_217_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 1, v___x_239_);
lean_ctor_set(v___x_219_, 0, v___x_249_);
v___x_251_ = v___x_219_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_249_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v___x_239_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
v_a_210_ = v___x_251_;
goto v___jp_209_;
}
}
else
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_260_; 
lean_dec(v_a_243_);
lean_dec_ref(v___x_239_);
lean_del_object(v___x_219_);
lean_dec(v_fst_217_);
v_a_253_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_260_ == 0)
{
v___x_255_ = v___x_244_;
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_244_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_256_ == 0)
{
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_253_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
lean_dec_ref(v___x_239_);
lean_dec(v___x_235_);
lean_del_object(v___x_219_);
lean_dec(v_fst_217_);
v_a_261_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_242_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_242_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_261_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
else
{
lean_object* v___x_270_; 
lean_dec(v___x_235_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 1, v___x_239_);
v___x_270_ = v___x_219_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_fst_217_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v___x_239_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
v_a_210_ = v___x_270_;
goto v___jp_209_;
}
}
}
}
else
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_280_; 
lean_del_object(v___x_230_);
lean_dec(v_stop_223_);
lean_dec(v_start_222_);
lean_dec_ref(v_array_221_);
lean_del_object(v___x_219_);
lean_dec(v_fst_217_);
v_a_273_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_280_ == 0)
{
v___x_275_ = v___x_233_;
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_233_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_276_ == 0)
{
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_a_273_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
}
}
}
v___jp_209_:
{
size_t v___x_211_; size_t v___x_212_; 
v___x_211_ = ((size_t)1ULL);
v___x_212_ = lean_usize_add(v_i_202_, v___x_211_);
v_i_202_ = v___x_212_;
v_b_203_ = v_a_210_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__1___boxed(lean_object* v_as_286_, lean_object* v_sz_287_, lean_object* v_i_288_, lean_object* v_b_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
size_t v_sz_boxed_295_; size_t v_i_boxed_296_; lean_object* v_res_297_; 
v_sz_boxed_295_ = lean_unbox_usize(v_sz_287_);
lean_dec(v_sz_287_);
v_i_boxed_296_ = lean_unbox_usize(v_i_288_);
lean_dec(v_i_288_);
v_res_297_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__1(v_as_286_, v_sz_boxed_295_, v_i_boxed_296_, v_b_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec_ref(v_as_286_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__0(lean_object* v___x_298_, size_t v_sz_299_, size_t v___x_300_, lean_object* v___x_301_, lean_object* v_xs1_302_, lean_object* v_fields1_303_, lean_object* v_xs2_304_, lean_object* v_fields2_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__1(v___x_298_, v_sz_299_, v___x_300_, v___x_301_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v_fst_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; uint8_t v___x_318_; uint8_t v___x_319_; lean_object* v___x_320_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_a_312_);
lean_dec_ref_known(v___x_311_, 1);
v_fst_313_ = lean_ctor_get(v_a_312_, 0);
lean_inc(v_fst_313_);
lean_dec(v_a_312_);
v___x_314_ = l_Array_append___redArg(v_xs1_302_, v_fields1_303_);
v___x_315_ = l_Array_append___redArg(v___x_314_, v_xs2_304_);
v___x_316_ = l_Array_append___redArg(v___x_315_, v_fields2_305_);
v___x_317_ = 0;
v___x_318_ = 1;
v___x_319_ = 1;
v___x_320_ = l_Lean_Meta_mkLambdaFVars(v___x_316_, v_fst_313_, v___x_317_, v___x_318_, v___x_317_, v___x_318_, v___x_319_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
lean_dec_ref(v___x_316_);
return v___x_320_;
}
else
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
lean_dec_ref(v_xs1_302_);
v_a_321_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_328_ == 0)
{
v___x_323_ = v___x_311_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_311_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_321_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__0___boxed(lean_object* v___x_329_, lean_object* v_sz_330_, lean_object* v___x_331_, lean_object* v___x_332_, lean_object* v_xs1_333_, lean_object* v_fields1_334_, lean_object* v_xs2_335_, lean_object* v_fields2_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
size_t v_sz_boxed_342_; size_t v___x_4598__boxed_343_; lean_object* v_res_344_; 
v_sz_boxed_342_ = lean_unbox_usize(v_sz_330_);
lean_dec(v_sz_330_);
v___x_4598__boxed_343_ = lean_unbox_usize(v___x_331_);
lean_dec(v___x_331_);
v_res_344_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__0(v___x_329_, v_sz_boxed_342_, v___x_4598__boxed_343_, v___x_332_, v_xs1_333_, v_fields1_334_, v_xs2_335_, v_fields2_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec_ref(v_fields2_336_);
lean_dec_ref(v_xs2_335_);
lean_dec_ref(v_fields1_334_);
lean_dec_ref(v___x_329_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__1(lean_object* v_fields1_347_, lean_object* v_P_348_, lean_object* v_xs1_349_, lean_object* v_xs2_350_, lean_object* v_fields2_351_, lean_object* v_x_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; size_t v_sz_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___f_367_; lean_object* v___x_368_; 
lean_inc_ref_n(v_fields2_351_, 2);
v___x_358_ = l_Array_reverse___redArg(v_fields2_351_);
v___x_359_ = lean_unsigned_to_nat(0u);
v___x_360_ = lean_array_get_size(v___x_358_);
v___x_361_ = l_Array_toSubarray___redArg(v___x_358_, v___x_359_, v___x_360_);
lean_inc_ref(v_fields1_347_);
v___x_362_ = l_Array_reverse___redArg(v_fields1_347_);
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v_P_348_);
lean_ctor_set(v___x_363_, 1, v___x_361_);
v_sz_364_ = lean_array_size(v___x_362_);
v___x_365_ = lean_box_usize(v_sz_364_);
v___x_366_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__1___boxed__const__1));
v___f_367_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_367_, 0, v___x_362_);
lean_closure_set(v___f_367_, 1, v___x_365_);
lean_closure_set(v___f_367_, 2, v___x_366_);
lean_closure_set(v___f_367_, 3, v___x_363_);
lean_closure_set(v___f_367_, 4, v_xs1_349_);
lean_closure_set(v___f_367_, 5, v_fields1_347_);
lean_closure_set(v___f_367_, 6, v_xs2_350_);
lean_closure_set(v___f_367_, 7, v_fields2_351_);
v___x_368_ = l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__2___redArg(v_fields2_351_, v___f_367_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__1___boxed(lean_object* v_fields1_369_, lean_object* v_P_370_, lean_object* v_xs1_371_, lean_object* v_xs2_372_, lean_object* v_fields2_373_, lean_object* v_x_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__1(v_fields1_369_, v_P_370_, v_xs1_371_, v_xs2_372_, v_fields2_373_, v_x_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec_ref(v_x_374_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__2(lean_object* v_fields1_381_, lean_object* v_P_382_, lean_object* v_xs1_383_, lean_object* v_xs2_384_, lean_object* v_t2_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v___f_391_; uint8_t v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
lean_inc_ref(v_xs2_384_);
v___f_391_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__1___boxed), 11, 4);
lean_closure_set(v___f_391_, 0, v_fields1_381_);
lean_closure_set(v___f_391_, 1, v_P_382_);
lean_closure_set(v___f_391_, 2, v_xs1_383_);
lean_closure_set(v___f_391_, 3, v_xs2_384_);
v___x_392_ = 0;
v___x_393_ = lean_box(v___x_392_);
v___x_394_ = lean_box(v___x_392_);
v___x_395_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__3___boxed), 10, 5);
lean_closure_set(v___x_395_, 0, lean_box(0));
lean_closure_set(v___x_395_, 1, v_t2_385_);
lean_closure_set(v___x_395_, 2, v___f_391_);
lean_closure_set(v___x_395_, 3, v___x_393_);
lean_closure_set(v___x_395_, 4, v___x_394_);
v___x_396_ = l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__2___redArg(v_xs2_384_, v___x_395_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__2___boxed(lean_object* v_fields1_397_, lean_object* v_P_398_, lean_object* v_xs1_399_, lean_object* v_xs2_400_, lean_object* v_t2_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__2(v_fields1_397_, v_P_398_, v_xs1_399_, v_xs2_400_, v_t2_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__3(lean_object* v_P_408_, lean_object* v_xs1_409_, lean_object* v_type_410_, lean_object* v___x_411_, lean_object* v_fields1_412_, lean_object* v_x_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v___f_419_; uint8_t v___x_420_; lean_object* v___x_421_; 
v___f_419_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__2___boxed), 10, 3);
lean_closure_set(v___f_419_, 0, v_fields1_412_);
lean_closure_set(v___f_419_, 1, v_P_408_);
lean_closure_set(v___f_419_, 2, v_xs1_409_);
v___x_420_ = 0;
v___x_421_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(v_type_410_, v___x_411_, v___f_419_, v___x_420_, v___x_420_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__3___boxed(lean_object* v_P_422_, lean_object* v_xs1_423_, lean_object* v_type_424_, lean_object* v___x_425_, lean_object* v_fields1_426_, lean_object* v_x_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__3(v_P_422_, v_xs1_423_, v_type_424_, v___x_425_, v_fields1_426_, v_x_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
lean_dec_ref(v_x_427_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__4(lean_object* v_P_434_, lean_object* v_type_435_, lean_object* v___x_436_, lean_object* v_xs1_437_, lean_object* v_t1_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v___f_444_; uint8_t v___x_445_; lean_object* v___x_446_; 
v___f_444_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__3___boxed), 11, 4);
lean_closure_set(v___f_444_, 0, v_P_434_);
lean_closure_set(v___f_444_, 1, v_xs1_437_);
lean_closure_set(v___f_444_, 2, v_type_435_);
lean_closure_set(v___f_444_, 3, v___x_436_);
v___x_445_ = 0;
v___x_446_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__3___redArg(v_t1_438_, v___f_444_, v___x_445_, v___x_445_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__4___boxed(lean_object* v_P_447_, lean_object* v_type_448_, lean_object* v___x_449_, lean_object* v_xs1_450_, lean_object* v_t1_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__4(v_P_447_, v_type_448_, v___x_449_, v_xs1_450_, v_t1_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
return v_res_457_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_instMonadEIO(lean_box(0));
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__1(lean_object* v_msg_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v_toApplicative_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_532_; 
v___x_469_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__1___closed__0);
v___x_470_ = l_StateRefT_x27_instMonad___redArg(v___x_469_);
v_toApplicative_471_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_532_ == 0)
{
lean_object* v_unused_533_; 
v_unused_533_ = lean_ctor_get(v___x_470_, 1);
lean_dec(v_unused_533_);
v___x_473_ = v___x_470_;
v_isShared_474_ = v_isSharedCheck_532_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_toApplicative_471_);
lean_dec(v___x_470_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_532_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v_toFunctor_475_; lean_object* v_toSeq_476_; lean_object* v_toSeqLeft_477_; lean_object* v_toSeqRight_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_530_; 
v_toFunctor_475_ = lean_ctor_get(v_toApplicative_471_, 0);
v_toSeq_476_ = lean_ctor_get(v_toApplicative_471_, 2);
v_toSeqLeft_477_ = lean_ctor_get(v_toApplicative_471_, 3);
v_toSeqRight_478_ = lean_ctor_get(v_toApplicative_471_, 4);
v_isSharedCheck_530_ = !lean_is_exclusive(v_toApplicative_471_);
if (v_isSharedCheck_530_ == 0)
{
lean_object* v_unused_531_; 
v_unused_531_ = lean_ctor_get(v_toApplicative_471_, 1);
lean_dec(v_unused_531_);
v___x_480_ = v_toApplicative_471_;
v_isShared_481_ = v_isSharedCheck_530_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_toSeqRight_478_);
lean_inc(v_toSeqLeft_477_);
lean_inc(v_toSeq_476_);
lean_inc(v_toFunctor_475_);
lean_dec(v_toApplicative_471_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_530_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___f_482_; lean_object* v___f_483_; lean_object* v___f_484_; lean_object* v___f_485_; lean_object* v___x_486_; lean_object* v___f_487_; lean_object* v___f_488_; lean_object* v___f_489_; lean_object* v___x_491_; 
v___f_482_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__1___closed__1));
v___f_483_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_475_);
v___f_484_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_484_, 0, v_toFunctor_475_);
v___f_485_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_485_, 0, v_toFunctor_475_);
v___x_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_486_, 0, v___f_484_);
lean_ctor_set(v___x_486_, 1, v___f_485_);
v___f_487_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_487_, 0, v_toSeqRight_478_);
v___f_488_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_488_, 0, v_toSeqLeft_477_);
v___f_489_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_489_, 0, v_toSeq_476_);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 4, v___f_487_);
lean_ctor_set(v___x_480_, 3, v___f_488_);
lean_ctor_set(v___x_480_, 2, v___f_489_);
lean_ctor_set(v___x_480_, 1, v___f_482_);
lean_ctor_set(v___x_480_, 0, v___x_486_);
v___x_491_ = v___x_480_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v___f_482_);
lean_ctor_set(v_reuseFailAlloc_529_, 2, v___f_489_);
lean_ctor_set(v_reuseFailAlloc_529_, 3, v___f_488_);
lean_ctor_set(v_reuseFailAlloc_529_, 4, v___f_487_);
v___x_491_ = v_reuseFailAlloc_529_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
lean_object* v___x_493_; 
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 1, v___f_483_);
lean_ctor_set(v___x_473_, 0, v___x_491_);
v___x_493_ = v___x_473_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_491_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v___f_483_);
v___x_493_ = v_reuseFailAlloc_528_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
lean_object* v___x_494_; lean_object* v_toApplicative_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_526_; 
v___x_494_ = l_StateRefT_x27_instMonad___redArg(v___x_493_);
v_toApplicative_495_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_526_ == 0)
{
lean_object* v_unused_527_; 
v_unused_527_ = lean_ctor_get(v___x_494_, 1);
lean_dec(v_unused_527_);
v___x_497_ = v___x_494_;
v_isShared_498_ = v_isSharedCheck_526_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_toApplicative_495_);
lean_dec(v___x_494_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_526_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v_toFunctor_499_; lean_object* v_toSeq_500_; lean_object* v_toSeqLeft_501_; lean_object* v_toSeqRight_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_524_; 
v_toFunctor_499_ = lean_ctor_get(v_toApplicative_495_, 0);
v_toSeq_500_ = lean_ctor_get(v_toApplicative_495_, 2);
v_toSeqLeft_501_ = lean_ctor_get(v_toApplicative_495_, 3);
v_toSeqRight_502_ = lean_ctor_get(v_toApplicative_495_, 4);
v_isSharedCheck_524_ = !lean_is_exclusive(v_toApplicative_495_);
if (v_isSharedCheck_524_ == 0)
{
lean_object* v_unused_525_; 
v_unused_525_ = lean_ctor_get(v_toApplicative_495_, 1);
lean_dec(v_unused_525_);
v___x_504_ = v_toApplicative_495_;
v_isShared_505_ = v_isSharedCheck_524_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_toSeqRight_502_);
lean_inc(v_toSeqLeft_501_);
lean_inc(v_toSeq_500_);
lean_inc(v_toFunctor_499_);
lean_dec(v_toApplicative_495_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_524_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___f_506_; lean_object* v___f_507_; lean_object* v___f_508_; lean_object* v___f_509_; lean_object* v___x_510_; lean_object* v___f_511_; lean_object* v___f_512_; lean_object* v___f_513_; lean_object* v___x_515_; 
v___f_506_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__1___closed__3));
v___f_507_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_499_);
v___f_508_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_508_, 0, v_toFunctor_499_);
v___f_509_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_509_, 0, v_toFunctor_499_);
v___x_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_510_, 0, v___f_508_);
lean_ctor_set(v___x_510_, 1, v___f_509_);
v___f_511_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_511_, 0, v_toSeqRight_502_);
v___f_512_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_512_, 0, v_toSeqLeft_501_);
v___f_513_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_513_, 0, v_toSeq_500_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 4, v___f_511_);
lean_ctor_set(v___x_504_, 3, v___f_512_);
lean_ctor_set(v___x_504_, 2, v___f_513_);
lean_ctor_set(v___x_504_, 1, v___f_506_);
lean_ctor_set(v___x_504_, 0, v___x_510_);
v___x_515_ = v___x_504_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v___f_506_);
lean_ctor_set(v_reuseFailAlloc_523_, 2, v___f_513_);
lean_ctor_set(v_reuseFailAlloc_523_, 3, v___f_512_);
lean_ctor_set(v_reuseFailAlloc_523_, 4, v___f_511_);
v___x_515_ = v_reuseFailAlloc_523_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_object* v___x_517_; 
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 1, v___f_507_);
lean_ctor_set(v___x_497_, 0, v___x_515_);
v___x_517_ = v___x_497_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v___f_507_);
v___x_517_ = v_reuseFailAlloc_522_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_3520__overap_520_; lean_object* v___x_521_; 
v___x_518_ = lean_box(0);
v___x_519_ = l_instInhabitedOfMonad___redArg(v___x_517_, v___x_518_);
v___x_3520__overap_520_ = lean_panic_fn_borrowed(v___x_519_, v_msg_463_);
lean_dec(v___x_519_);
lean_inc(v___y_467_);
lean_inc_ref(v___y_466_);
lean_inc(v___y_465_);
lean_inc_ref(v___y_464_);
v___x_521_ = lean_apply_5(v___x_3520__overap_520_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, lean_box(0));
return v___x_521_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__1___boxed(lean_object* v_msg_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__1(v_msg_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0_spec__4(lean_object* v_msgData_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v___x_547_; lean_object* v_env_548_; lean_object* v___x_549_; lean_object* v_mctx_550_; lean_object* v_lctx_551_; lean_object* v_options_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_547_ = lean_st_ref_get(v___y_545_);
v_env_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc_ref(v_env_548_);
lean_dec(v___x_547_);
v___x_549_ = lean_st_ref_get(v___y_543_);
v_mctx_550_ = lean_ctor_get(v___x_549_, 0);
lean_inc_ref(v_mctx_550_);
lean_dec(v___x_549_);
v_lctx_551_ = lean_ctor_get(v___y_542_, 2);
v_options_552_ = lean_ctor_get(v___y_544_, 2);
lean_inc_ref(v_options_552_);
lean_inc_ref(v_lctx_551_);
v___x_553_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_553_, 0, v_env_548_);
lean_ctor_set(v___x_553_, 1, v_mctx_550_);
lean_ctor_set(v___x_553_, 2, v_lctx_551_);
lean_ctor_set(v___x_553_, 3, v_options_552_);
v___x_554_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
lean_ctor_set(v___x_554_, 1, v_msgData_541_);
v___x_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0_spec__4___boxed(lean_object* v_msgData_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0_spec__4(v_msgData_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0___redArg(lean_object* v_msg_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v_ref_569_; lean_object* v___x_570_; lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_579_; 
v_ref_569_ = lean_ctor_get(v___y_566_, 5);
v___x_570_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0_spec__4(v_msg_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
v_a_571_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_579_ == 0)
{
v___x_573_ = v___x_570_;
v_isShared_574_ = v_isSharedCheck_579_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_570_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_579_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_575_; lean_object* v___x_577_; 
lean_inc(v_ref_569_);
v___x_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_575_, 0, v_ref_569_);
lean_ctor_set(v___x_575_, 1, v_a_571_);
if (v_isShared_574_ == 0)
{
lean_ctor_set_tag(v___x_573_, 1);
lean_ctor_set(v___x_573_, 0, v___x_575_);
v___x_577_ = v___x_573_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0___redArg___boxed(lean_object* v_msg_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0___redArg(v_msg_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
return v_res_586_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__1(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__0));
v___x_589_ = l_Lean_stringToMessageData(v___x_588_);
return v___x_589_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__3(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__2));
v___x_592_ = l_Lean_stringToMessageData(v___x_591_);
return v___x_592_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__7(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_596_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__6));
v___x_597_ = lean_unsigned_to_nat(11u);
v___x_598_ = lean_unsigned_to_nat(122u);
v___x_599_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__5));
v___x_600_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__4));
v___x_601_ = l_mkPanicMessageWithDecl(v___x_600_, v___x_599_, v___x_598_, v___x_597_, v___x_596_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0(lean_object* v_constName_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v___x_616_; lean_object* v_env_617_; uint8_t v___x_618_; lean_object* v___x_619_; 
v___x_616_ = lean_st_ref_get(v___y_606_);
v_env_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc_ref(v_env_617_);
lean_dec(v___x_616_);
v___x_618_ = 0;
lean_inc(v_constName_602_);
v___x_619_ = l_Lean_Environment_findAsync_x3f(v_env_617_, v_constName_602_, v___x_618_);
if (lean_obj_tag(v___x_619_) == 1)
{
lean_object* v_val_620_; uint8_t v_kind_621_; 
v_val_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_val_620_);
lean_dec_ref_known(v___x_619_, 1);
v_kind_621_ = lean_ctor_get_uint8(v_val_620_, sizeof(void*)*3);
if (v_kind_621_ == 6)
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_620_);
if (lean_obj_tag(v___x_622_) == 6)
{
lean_object* v_val_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_dec(v_constName_602_);
v_val_623_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_622_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_val_623_);
lean_dec(v___x_622_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
lean_ctor_set_tag(v___x_625_, 0);
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_val_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
else
{
lean_object* v___x_631_; lean_object* v___x_632_; 
lean_dec_ref(v___x_622_);
v___x_631_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__7);
v___x_632_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__1(v___x_631_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_641_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_641_ == 0)
{
v___x_635_ = v___x_632_;
v_isShared_636_ = v_isSharedCheck_641_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_632_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_641_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
if (lean_obj_tag(v_a_633_) == 0)
{
lean_del_object(v___x_635_);
goto v___jp_608_;
}
else
{
lean_object* v_val_637_; lean_object* v___x_639_; 
lean_dec(v_constName_602_);
v_val_637_ = lean_ctor_get(v_a_633_, 0);
lean_inc(v_val_637_);
lean_dec_ref_known(v_a_633_, 1);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v_val_637_);
v___x_639_ = v___x_635_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_val_637_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
else
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
lean_dec(v_constName_602_);
v_a_642_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_649_ == 0)
{
v___x_644_ = v___x_632_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_632_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_642_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
}
else
{
lean_dec(v_val_620_);
goto v___jp_608_;
}
}
else
{
lean_dec(v___x_619_);
goto v___jp_608_;
}
v___jp_608_:
{
lean_object* v___x_609_; uint8_t v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_609_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__1);
v___x_610_ = 0;
v___x_611_ = l_Lean_MessageData_ofConstName(v_constName_602_, v___x_610_);
v___x_612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_609_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
v___x_613_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__3);
v___x_614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_612_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
v___x_615_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0___redArg(v___x_614_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
return v___x_615_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___boxed(lean_object* v_constName_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0(v_constName_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg(lean_object* v_ctorName_657_, lean_object* v_P_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0(v_ctorName_657_, v_a_659_, v_a_660_, v_a_661_, v_a_662_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; lean_object* v_toConstantVal_666_; lean_object* v_numParams_667_; lean_object* v_type_668_; lean_object* v___x_669_; lean_object* v___f_670_; uint8_t v___x_671_; lean_object* v___x_672_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_a_665_);
lean_dec_ref_known(v___x_664_, 1);
v_toConstantVal_666_ = lean_ctor_get(v_a_665_, 0);
lean_inc_ref(v_toConstantVal_666_);
v_numParams_667_ = lean_ctor_get(v_a_665_, 3);
lean_inc(v_numParams_667_);
lean_dec(v_a_665_);
v_type_668_ = lean_ctor_get(v_toConstantVal_666_, 2);
lean_inc_ref_n(v_type_668_, 2);
lean_dec_ref(v_toConstantVal_666_);
v___x_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_669_, 0, v_numParams_667_);
lean_inc_ref(v___x_669_);
v___f_670_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__4___boxed), 10, 3);
lean_closure_set(v___f_670_, 0, v_P_658_);
lean_closure_set(v___f_670_, 1, v_type_668_);
lean_closure_set(v___f_670_, 2, v___x_669_);
v___x_671_ = 0;
v___x_672_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(v_type_668_, v___x_669_, v___f_670_, v___x_671_, v___x_671_, v_a_659_, v_a_660_, v_a_661_, v_a_662_);
return v___x_672_;
}
else
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_680_; 
lean_dec_ref(v_P_658_);
v_a_673_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_680_ == 0)
{
v___x_675_ = v___x_664_;
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_664_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
if (v_isShared_676_ == 0)
{
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_673_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___boxed(lean_object* v_ctorName_681_, lean_object* v_P_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg(v_ctorName_681_, v_P_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_);
lean_dec(v_a_686_);
lean_dec_ref(v_a_685_);
lean_dec(v_a_684_);
lean_dec_ref(v_a_683_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0(lean_object* v_00_u03b1_689_, lean_object* v_msg_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0___redArg(v_msg_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0___boxed(lean_object* v_00_u03b1_697_, lean_object* v_msg_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0(v_00_u03b1_697_, v_msg_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__spec__0(lean_object* v_name_705_, lean_object* v_decl_706_, lean_object* v_ref_707_){
_start:
{
lean_object* v_defValue_709_; lean_object* v_descr_710_; lean_object* v_deprecation_x3f_711_; lean_object* v___x_712_; uint8_t v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v_defValue_709_ = lean_ctor_get(v_decl_706_, 0);
v_descr_710_ = lean_ctor_get(v_decl_706_, 1);
v_deprecation_x3f_711_ = lean_ctor_get(v_decl_706_, 2);
v___x_712_ = lean_alloc_ctor(1, 0, 1);
v___x_713_ = lean_unbox(v_defValue_709_);
lean_ctor_set_uint8(v___x_712_, 0, v___x_713_);
lean_inc(v_deprecation_x3f_711_);
lean_inc_ref(v_descr_710_);
lean_inc_n(v_name_705_, 2);
v___x_714_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_714_, 0, v_name_705_);
lean_ctor_set(v___x_714_, 1, v_ref_707_);
lean_ctor_set(v___x_714_, 2, v___x_712_);
lean_ctor_set(v___x_714_, 3, v_descr_710_);
lean_ctor_set(v___x_714_, 4, v_deprecation_x3f_711_);
v___x_715_ = lean_register_option(v_name_705_, v___x_714_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_723_; 
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_723_ == 0)
{
lean_object* v_unused_724_; 
v_unused_724_ = lean_ctor_get(v___x_715_, 0);
lean_dec(v_unused_724_);
v___x_717_ = v___x_715_;
v_isShared_718_ = v_isSharedCheck_723_;
goto v_resetjp_716_;
}
else
{
lean_dec(v___x_715_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_723_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_719_; lean_object* v___x_721_; 
lean_inc(v_defValue_709_);
v___x_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_719_, 0, v_name_705_);
lean_ctor_set(v___x_719_, 1, v_defValue_709_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v___x_719_);
v___x_721_ = v___x_717_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec(v_name_705_);
v_a_725_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_715_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_715_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_733_, lean_object* v_decl_734_, lean_object* v_ref_735_, lean_object* v_a_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__spec__0(v_name_733_, v_decl_734_, v_ref_735_);
lean_dec_ref(v_decl_734_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_782_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4_));
v___x_783_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4_));
v___x_784_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4_));
v___x_785_ = l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__spec__0(v___x_782_, v___x_783_, v___x_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4____boxed(lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4_();
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionTypeName(lean_object* v_indName_789_){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionTypeName___closed__0));
v___x_791_ = l_Lean_Name_str___override(v_indName_789_, v___x_790_);
return v___x_791_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__0(lean_object* v_opts_792_, lean_object* v_opt_793_){
_start:
{
lean_object* v_name_794_; lean_object* v_defValue_795_; lean_object* v_map_796_; lean_object* v___x_797_; 
v_name_794_ = lean_ctor_get(v_opt_793_, 0);
v_defValue_795_ = lean_ctor_get(v_opt_793_, 1);
v_map_796_ = lean_ctor_get(v_opts_792_, 0);
v___x_797_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_796_, v_name_794_);
if (lean_obj_tag(v___x_797_) == 0)
{
uint8_t v___x_798_; 
v___x_798_ = lean_unbox(v_defValue_795_);
return v___x_798_;
}
else
{
lean_object* v_val_799_; 
v_val_799_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_val_799_);
lean_dec_ref_known(v___x_797_, 1);
if (lean_obj_tag(v_val_799_) == 1)
{
uint8_t v_v_800_; 
v_v_800_ = lean_ctor_get_uint8(v_val_799_, 0);
lean_dec_ref_known(v_val_799_, 0);
return v_v_800_;
}
else
{
uint8_t v___x_801_; 
lean_dec(v_val_799_);
v___x_801_ = lean_unbox(v_defValue_795_);
return v___x_801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__0___boxed(lean_object* v_opts_802_, lean_object* v_opt_803_){
_start:
{
uint8_t v_res_804_; lean_object* v_r_805_; 
v_res_804_ = l_Lean_Option_get___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__0(v_opts_802_, v_opt_803_);
lean_dec_ref(v_opt_803_);
lean_dec_ref(v_opts_802_);
v_r_805_ = lean_box(v_res_804_);
return v_r_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__1___redArg(lean_object* v_constName_806_, uint8_t v_skipRealize_807_, lean_object* v___y_808_){
_start:
{
lean_object* v___x_810_; lean_object* v_env_811_; uint8_t v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_810_ = lean_st_ref_get(v___y_808_);
v_env_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc_ref(v_env_811_);
lean_dec(v___x_810_);
v___x_812_ = l_Lean_Environment_contains(v_env_811_, v_constName_806_, v_skipRealize_807_);
v___x_813_ = lean_box(v___x_812_);
v___x_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__1___redArg___boxed(lean_object* v_constName_815_, lean_object* v_skipRealize_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
uint8_t v_skipRealize_boxed_819_; lean_object* v_res_820_; 
v_skipRealize_boxed_819_ = lean_unbox(v_skipRealize_816_);
v_res_820_ = l_Lean_hasConst___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__1___redArg(v_constName_815_, v_skipRealize_boxed_819_, v___y_817_);
lean_dec(v___y_817_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__1(lean_object* v_constName_821_, uint8_t v_skipRealize_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Lean_hasConst___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__1___redArg(v_constName_821_, v_skipRealize_822_, v___y_826_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__1___boxed(lean_object* v_constName_829_, lean_object* v_skipRealize_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
uint8_t v_skipRealize_boxed_836_; lean_object* v_res_837_; 
v_skipRealize_boxed_836_ = lean_unbox(v_skipRealize_830_);
v_res_837_ = l_Lean_hasConst___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__1(v_constName_829_, v_skipRealize_boxed_836_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear(lean_object* v_indName_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_){
_start:
{
lean_object* v_options_849_; lean_object* v___x_850_; uint8_t v___x_851_; 
v_options_849_ = lean_ctor_get(v_a_846_, 2);
v___x_850_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_backward_linearNoConfusionType;
v___x_851_ = l_Lean_Option_get___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__0(v_options_849_, v___x_850_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; lean_object* v___x_853_; 
lean_dec(v_indName_843_);
v___x_852_ = lean_box(v___x_851_);
v___x_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
return v___x_853_;
}
else
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v_a_856_; uint8_t v___x_857_; 
v___x_854_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear___closed__2));
v___x_855_ = l_Lean_hasConst___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__1___redArg(v___x_854_, v___x_851_, v_a_847_);
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_856_);
v___x_857_ = lean_unbox(v_a_856_);
lean_dec(v_a_856_);
if (v___x_857_ == 0)
{
lean_dec(v_indName_843_);
return v___x_855_;
}
else
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v_a_860_; uint8_t v___x_861_; 
lean_dec_ref(v___x_855_);
v___x_858_ = l_Lean_mkCtorElimName(v_indName_843_);
v___x_859_ = l_Lean_hasConst___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__1___redArg(v___x_858_, v___x_851_, v_a_847_);
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_860_);
v___x_861_ = lean_unbox(v_a_860_);
lean_dec(v_a_860_);
if (v___x_861_ == 0)
{
return v___x_859_;
}
else
{
lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_869_; 
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_869_ == 0)
{
lean_object* v_unused_870_; 
v_unused_870_ = lean_ctor_get(v___x_859_, 0);
lean_dec(v_unused_870_);
v___x_863_ = v___x_859_;
v_isShared_864_ = v_isSharedCheck_869_;
goto v_resetjp_862_;
}
else
{
lean_dec(v___x_859_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_869_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; lean_object* v___x_867_; 
v___x_865_ = lean_box(v___x_851_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_865_);
v___x_867_ = v___x_863_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_865_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear___boxed(lean_object* v_indName_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear(v_indName_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
lean_dec(v_a_873_);
lean_dec_ref(v_a_872_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___lam__0(lean_object* v_then_878_, lean_object* v_h_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v___x_885_; 
lean_inc(v___y_883_);
lean_inc_ref(v___y_882_);
lean_inc(v___y_881_);
lean_inc_ref(v___y_880_);
lean_inc_ref(v_h_879_);
v___x_885_ = lean_apply_6(v_then_878_, v_h_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, lean_box(0));
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; uint8_t v___x_890_; uint8_t v___x_891_; uint8_t v___x_892_; lean_object* v___x_893_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
lean_dec_ref_known(v___x_885_, 1);
v___x_887_ = lean_unsigned_to_nat(1u);
v___x_888_ = lean_mk_empty_array_with_capacity(v___x_887_);
v___x_889_ = lean_array_push(v___x_888_, v_h_879_);
v___x_890_ = 0;
v___x_891_ = 1;
v___x_892_ = 1;
v___x_893_ = l_Lean_Meta_mkLambdaFVars(v___x_889_, v_a_886_, v___x_890_, v___x_891_, v___x_890_, v___x_891_, v___x_892_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
lean_dec_ref(v___x_889_);
return v___x_893_;
}
else
{
lean_dec_ref(v_h_879_);
return v___x_885_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___lam__0___boxed(lean_object* v_then_894_, lean_object* v_h_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___lam__0(v_then_894_, v_h_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___lam__1(lean_object* v_else_902_, lean_object* v_h_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v___x_909_; 
lean_inc(v___y_907_);
lean_inc_ref(v___y_906_);
lean_inc(v___y_905_);
lean_inc_ref(v___y_904_);
lean_inc_ref(v_h_903_);
v___x_909_ = lean_apply_6(v_else_902_, v_h_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, lean_box(0));
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; uint8_t v___x_914_; uint8_t v___x_915_; uint8_t v___x_916_; lean_object* v___x_917_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_910_);
lean_dec_ref_known(v___x_909_, 1);
v___x_911_ = lean_unsigned_to_nat(1u);
v___x_912_ = lean_mk_empty_array_with_capacity(v___x_911_);
v___x_913_ = lean_array_push(v___x_912_, v_h_903_);
v___x_914_ = 0;
v___x_915_ = 1;
v___x_916_ = 1;
v___x_917_ = l_Lean_Meta_mkLambdaFVars(v___x_913_, v_a_910_, v___x_914_, v___x_915_, v___x_914_, v___x_915_, v___x_916_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
lean_dec_ref(v___x_913_);
return v___x_917_;
}
else
{
lean_dec_ref(v_h_903_);
return v___x_909_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___lam__1___boxed(lean_object* v_else_918_, lean_object* v_h_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___lam__1(v_else_918_, v_h_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___redArg___lam__0(lean_object* v_k_926_, lean_object* v_b_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v___x_933_; 
lean_inc(v___y_931_);
lean_inc_ref(v___y_930_);
lean_inc(v___y_929_);
lean_inc_ref(v___y_928_);
v___x_933_ = lean_apply_6(v_k_926_, v_b_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, lean_box(0));
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_934_, lean_object* v_b_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___redArg___lam__0(v_k_934_, v_b_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___redArg(lean_object* v_name_942_, uint8_t v_bi_943_, lean_object* v_type_944_, lean_object* v_k_945_, uint8_t v_kind_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v___f_952_; lean_object* v___x_953_; 
v___f_952_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_952_, 0, v_k_945_);
v___x_953_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_942_, v_bi_943_, v_type_944_, v___f_952_, v_kind_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
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
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
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
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_962_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___redArg___boxed(lean_object* v_name_970_, lean_object* v_bi_971_, lean_object* v_type_972_, lean_object* v_k_973_, lean_object* v_kind_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
uint8_t v_bi_boxed_980_; uint8_t v_kind_boxed_981_; lean_object* v_res_982_; 
v_bi_boxed_980_ = lean_unbox(v_bi_971_);
v_kind_boxed_981_ = lean_unbox(v_kind_974_);
v_res_982_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___redArg(v_name_970_, v_bi_boxed_980_, v_type_972_, v_k_973_, v_kind_boxed_981_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(lean_object* v_name_983_, lean_object* v_type_984_, lean_object* v_k_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
uint8_t v___x_991_; uint8_t v___x_992_; lean_object* v___x_993_; 
v___x_991_ = 0;
v___x_992_ = 0;
v___x_993_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___redArg(v_name_983_, v___x_991_, v_type_984_, v_k_985_, v___x_992_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg___boxed(lean_object* v_name_994_, lean_object* v_type_995_, lean_object* v_k_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v_name_994_, v_type_995_, v_k_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
return v_res_1002_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__0(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = lean_unsigned_to_nat(1u);
v___x_1004_ = l_Lean_Level_ofNat(v___x_1003_);
return v___x_1004_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__1(void){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1005_ = lean_box(0);
v___x_1006_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__0, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__0_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__0);
v___x_1007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
lean_ctor_set(v___x_1007_, 1, v___x_1005_);
return v___x_1007_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__3(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1010_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__1, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__1_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__1);
v___x_1011_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__2));
v___x_1012_ = l_Lean_mkConst(v___x_1011_, v___x_1010_);
return v___x_1012_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__6(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1016_ = lean_box(0);
v___x_1017_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__5));
v___x_1018_ = l_Lean_mkConst(v___x_1017_, v___x_1016_);
return v___x_1018_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__11(void){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1026_ = lean_box(0);
v___x_1027_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__10));
v___x_1028_ = l_Lean_mkConst(v___x_1027_, v___x_1026_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq(lean_object* v_P_1032_, lean_object* v_e1_1033_, lean_object* v_e2_1034_, lean_object* v_then_1035_, lean_object* v_else_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v___x_1042_; 
lean_inc_ref(v_P_1032_);
v___x_1042_ = l_Lean_Meta_getLevel(v_P_1032_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1043_; lean_object* v___f_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v_heq_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_a_1043_);
lean_dec_ref_known(v___x_1042_, 1);
v___f_1044_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1044_, 0, v_then_1035_);
v___x_1045_ = lean_box(0);
v___x_1046_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__3, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__3_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__3);
v___x_1047_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__6, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__6_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__6);
lean_inc_ref(v_e2_1034_);
lean_inc_ref(v_e1_1033_);
v_heq_1048_ = l_Lean_mkApp3(v___x_1046_, v___x_1047_, v_e1_1033_, v_e2_1034_);
v___x_1049_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__8));
v___x_1050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1050_, 0, v_a_1043_);
lean_ctor_set(v___x_1050_, 1, v___x_1045_);
v___x_1051_ = l_Lean_mkConst(v___x_1049_, v___x_1050_);
v___x_1052_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__11, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__11_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__11);
v___x_1053_ = l_Lean_mkAppB(v___x_1052_, v_e1_1033_, v_e2_1034_);
lean_inc_ref_n(v_heq_1048_, 2);
v___x_1054_ = l_Lean_mkApp3(v___x_1051_, v_P_1032_, v_heq_1048_, v___x_1053_);
v___x_1055_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__13));
v___x_1056_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_1055_, v_heq_1048_, v___f_1044_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; lean_object* v___f_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_a_1057_);
lean_dec_ref_known(v___x_1056_, 1);
v___f_1058_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___lam__1___boxed), 7, 1);
lean_closure_set(v___f_1058_, 0, v_else_1036_);
v___x_1059_ = l_Lean_mkNot(v_heq_1048_);
v___x_1060_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_1055_, v___x_1059_, v___f_1058_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1070_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1063_ = v___x_1060_;
v_isShared_1064_ = v_isSharedCheck_1070_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1060_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1070_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1068_; 
v___x_1065_ = l_Lean_Expr_app___override(v___x_1054_, v_a_1057_);
v___x_1066_ = l_Lean_Expr_app___override(v___x_1065_, v_a_1061_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 0, v___x_1066_);
v___x_1068_ = v___x_1063_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1066_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
else
{
lean_dec(v_a_1057_);
lean_dec_ref(v___x_1054_);
return v___x_1060_;
}
}
else
{
lean_dec_ref(v___x_1054_);
lean_dec_ref(v_heq_1048_);
lean_dec_ref(v_else_1036_);
return v___x_1056_;
}
}
else
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
lean_dec_ref(v_else_1036_);
lean_dec_ref(v_then_1035_);
lean_dec_ref(v_e2_1034_);
lean_dec_ref(v_e1_1033_);
lean_dec_ref(v_P_1032_);
v_a_1071_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_1042_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1042_);
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
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___boxed(lean_object* v_P_1079_, lean_object* v_e1_1080_, lean_object* v_e2_1081_, lean_object* v_then_1082_, lean_object* v_else_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq(v_P_1079_, v_e1_1080_, v_e2_1081_, v_then_1082_, v_else_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
lean_dec(v_a_1087_);
lean_dec_ref(v_a_1086_);
lean_dec(v_a_1085_);
lean_dec_ref(v_a_1084_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0(lean_object* v_00_u03b1_1090_, lean_object* v_name_1091_, uint8_t v_bi_1092_, lean_object* v_type_1093_, lean_object* v_k_1094_, uint8_t v_kind_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___redArg(v_name_1091_, v_bi_1092_, v_type_1093_, v_k_1094_, v_kind_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1102_, lean_object* v_name_1103_, lean_object* v_bi_1104_, lean_object* v_type_1105_, lean_object* v_k_1106_, lean_object* v_kind_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
uint8_t v_bi_boxed_1113_; uint8_t v_kind_boxed_1114_; lean_object* v_res_1115_; 
v_bi_boxed_1113_ = lean_unbox(v_bi_1104_);
v_kind_boxed_1114_ = lean_unbox(v_kind_1107_);
v_res_1115_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0(v_00_u03b1_1102_, v_name_1103_, v_bi_boxed_1113_, v_type_1105_, v_k_1106_, v_kind_boxed_1114_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0(lean_object* v_00_u03b1_1116_, lean_object* v_name_1117_, lean_object* v_type_1118_, lean_object* v_k_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v_name_1117_, v_type_1118_, v_k_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___boxed(lean_object* v_00_u03b1_1126_, lean_object* v_name_1127_, lean_object* v_type_1128_, lean_object* v_k_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0(v_00_u03b1_1126_, v_name_1127_, v_type_1128_, v_k_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__3___redArg(lean_object* v_type_1136_, lean_object* v_k_1137_, uint8_t v_cleanupAnnotations_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v___f_1144_; uint8_t v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___f_1144_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1144_, 0, v_k_1137_);
v___x_1145_ = 0;
v___x_1146_ = lean_box(0);
v___x_1147_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1145_, v___x_1146_, v_type_1136_, v___f_1144_, v_cleanupAnnotations_1138_, v___x_1145_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1147_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1147_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
v_a_1156_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1147_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1147_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__3___redArg___boxed(lean_object* v_type_1164_, lean_object* v_k_1165_, lean_object* v_cleanupAnnotations_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1172_; lean_object* v_res_1173_; 
v_cleanupAnnotations_boxed_1172_ = lean_unbox(v_cleanupAnnotations_1166_);
v_res_1173_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__3___redArg(v_type_1164_, v_k_1165_, v_cleanupAnnotations_boxed_1172_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__3(lean_object* v_00_u03b1_1174_, lean_object* v_type_1175_, lean_object* v_k_1176_, uint8_t v_cleanupAnnotations_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__3___redArg(v_type_1175_, v_k_1176_, v_cleanupAnnotations_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__3___boxed(lean_object* v_00_u03b1_1184_, lean_object* v_type_1185_, lean_object* v_k_1186_, lean_object* v_cleanupAnnotations_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1193_; lean_object* v_res_1194_; 
v_cleanupAnnotations_boxed_1193_ = lean_unbox(v_cleanupAnnotations_1187_);
v_res_1194_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__3(v_00_u03b1_1184_, v_type_1185_, v_k_1186_, v_cleanupAnnotations_boxed_1193_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__6___redArg(lean_object* v_name_1195_, lean_object* v_levelParams_1196_, lean_object* v_type_1197_, lean_object* v_value_1198_, lean_object* v_hints_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v___x_1202_; uint8_t v___y_1204_; uint8_t v___y_1211_; lean_object* v_env_1214_; uint8_t v___x_1215_; 
v___x_1202_ = lean_st_ref_get(v___y_1200_);
v_env_1214_ = lean_ctor_get(v___x_1202_, 0);
lean_inc_ref_n(v_env_1214_, 2);
lean_dec(v___x_1202_);
v___x_1215_ = l_Lean_Environment_hasUnsafe(v_env_1214_, v_type_1197_);
if (v___x_1215_ == 0)
{
uint8_t v___x_1216_; 
v___x_1216_ = l_Lean_Environment_hasUnsafe(v_env_1214_, v_value_1198_);
v___y_1211_ = v___x_1216_;
goto v___jp_1210_;
}
else
{
lean_dec_ref(v_env_1214_);
v___y_1211_ = v___x_1215_;
goto v___jp_1210_;
}
v___jp_1203_:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
lean_inc(v_name_1195_);
v___x_1205_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1205_, 0, v_name_1195_);
lean_ctor_set(v___x_1205_, 1, v_levelParams_1196_);
lean_ctor_set(v___x_1205_, 2, v_type_1197_);
v___x_1206_ = lean_box(0);
v___x_1207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1207_, 0, v_name_1195_);
lean_ctor_set(v___x_1207_, 1, v___x_1206_);
v___x_1208_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1208_, 0, v___x_1205_);
lean_ctor_set(v___x_1208_, 1, v_value_1198_);
lean_ctor_set(v___x_1208_, 2, v_hints_1199_);
lean_ctor_set(v___x_1208_, 3, v___x_1207_);
lean_ctor_set_uint8(v___x_1208_, sizeof(void*)*4, v___y_1204_);
v___x_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
return v___x_1209_;
}
v___jp_1210_:
{
if (v___y_1211_ == 0)
{
uint8_t v___x_1212_; 
v___x_1212_ = 1;
v___y_1204_ = v___x_1212_;
goto v___jp_1203_;
}
else
{
uint8_t v___x_1213_; 
v___x_1213_ = 0;
v___y_1204_ = v___x_1213_;
goto v___jp_1203_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__6___redArg___boxed(lean_object* v_name_1217_, lean_object* v_levelParams_1218_, lean_object* v_type_1219_, lean_object* v_value_1220_, lean_object* v_hints_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__6___redArg(v_name_1217_, v_levelParams_1218_, v_type_1219_, v_value_1220_, v_hints_1221_, v___y_1222_);
lean_dec(v___y_1222_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__6(lean_object* v_name_1225_, lean_object* v_levelParams_1226_, lean_object* v_type_1227_, lean_object* v_value_1228_, lean_object* v_hints_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v___x_1235_; 
v___x_1235_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__6___redArg(v_name_1225_, v_levelParams_1226_, v_type_1227_, v_value_1228_, v_hints_1229_, v___y_1233_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__6___boxed(lean_object* v_name_1236_, lean_object* v_levelParams_1237_, lean_object* v_type_1238_, lean_object* v_value_1239_, lean_object* v_hints_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__6(v_name_1236_, v_levelParams_1237_, v_type_1238_, v_value_1239_, v_hints_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8(lean_object* v_msg_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v___f_1254_; lean_object* v___x_13646__overap_1255_; lean_object* v___x_1256_; 
v___f_1254_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8___closed__0));
v___x_13646__overap_1255_ = lean_panic_fn_borrowed(v___f_1254_, v_msg_1248_);
lean_inc(v___y_1252_);
lean_inc_ref(v___y_1251_);
lean_inc(v___y_1250_);
lean_inc_ref(v___y_1249_);
v___x_1256_ = lean_apply_5(v___x_13646__overap_1255_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, lean_box(0));
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8___boxed(lean_object* v_msg_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8(v_msg_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__0(lean_object* v___x_1264_, uint8_t v___x_1265_, lean_object* v_ys_1266_, lean_object* v_x_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
uint8_t v___x_1273_; uint8_t v___x_1274_; lean_object* v___x_1275_; 
v___x_1273_ = 0;
v___x_1274_ = 1;
v___x_1275_ = l_Lean_Meta_mkLambdaFVars(v_ys_1266_, v___x_1264_, v___x_1273_, v___x_1265_, v___x_1273_, v___x_1265_, v___x_1274_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__0___boxed(lean_object* v___x_1276_, lean_object* v___x_1277_, lean_object* v_ys_1278_, lean_object* v_x_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
uint8_t v___x_16350__boxed_1285_; lean_object* v_res_1286_; 
v___x_16350__boxed_1285_ = lean_unbox(v___x_1277_);
v_res_1286_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__0(v___x_1276_, v___x_16350__boxed_1285_, v_ys_1278_, v_x_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec_ref(v_x_1279_);
lean_dec_ref(v_ys_1278_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__0(lean_object* v_P_1287_, lean_object* v_x_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1294_, 0, v_P_1287_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__0___boxed(lean_object* v_P_1295_, lean_object* v_x_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__0(v_P_1295_, v_x_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec_ref(v_x_1296_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__1(lean_object* v___x_1303_, lean_object* v_P_1304_, lean_object* v_xs1_1305_, lean_object* v_zs1_1306_, lean_object* v_xs2_1307_, uint8_t v___x_1308_, uint8_t v___x_1309_, lean_object* v_zs2_1310_, lean_object* v_x_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v___x_1317_; 
lean_inc_ref(v_P_1304_);
v___x_1317_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg(v___x_1303_, v_P_1304_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
lean_inc(v_a_1318_);
lean_dec_ref_known(v___x_1317_, 1);
v___x_1319_ = l_Array_append___redArg(v_xs1_1305_, v_zs1_1306_);
v___x_1320_ = l_Array_append___redArg(v___x_1319_, v_xs2_1307_);
v___x_1321_ = l_Array_append___redArg(v___x_1320_, v_zs2_1310_);
v___x_1322_ = l_Lean_Expr_beta(v_a_1318_, v___x_1321_);
v___x_1323_ = l_Lean_mkArrow(v___x_1322_, v_P_1304_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v_a_1324_; uint8_t v___x_1325_; lean_object* v___x_1326_; 
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_a_1324_);
lean_dec_ref_known(v___x_1323_, 1);
v___x_1325_ = 1;
v___x_1326_ = l_Lean_Meta_mkLambdaFVars(v_zs2_1310_, v_a_1324_, v___x_1308_, v___x_1309_, v___x_1308_, v___x_1309_, v___x_1325_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
return v___x_1326_;
}
else
{
return v___x_1323_;
}
}
else
{
lean_dec_ref(v_xs1_1305_);
lean_dec_ref(v_P_1304_);
return v___x_1317_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__1___boxed(lean_object* v___x_1327_, lean_object* v_P_1328_, lean_object* v_xs1_1329_, lean_object* v_zs1_1330_, lean_object* v_xs2_1331_, lean_object* v___x_1332_, lean_object* v___x_1333_, lean_object* v_zs2_1334_, lean_object* v_x_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
uint8_t v___x_16400__boxed_1341_; uint8_t v___x_16401__boxed_1342_; lean_object* v_res_1343_; 
v___x_16400__boxed_1341_ = lean_unbox(v___x_1332_);
v___x_16401__boxed_1342_ = lean_unbox(v___x_1333_);
v_res_1343_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__1(v___x_1327_, v_P_1328_, v_xs1_1329_, v_zs1_1330_, v_xs2_1331_, v___x_16400__boxed_1341_, v___x_16401__boxed_1342_, v_zs2_1334_, v_x_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec_ref(v_x_1335_);
lean_dec_ref(v_zs2_1334_);
lean_dec_ref(v_xs2_1331_);
lean_dec_ref(v_zs1_1330_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__2(lean_object* v_val_1344_, lean_object* v___x_1345_, lean_object* v___x_1346_, lean_object* v_indName_1347_, lean_object* v___x_1348_, lean_object* v_xs2_1349_, lean_object* v___x_1350_, lean_object* v_ysx2_1351_, lean_object* v_P_1352_, lean_object* v_xs1_1353_, lean_object* v_zs1_1354_, uint8_t v___x_1355_, uint8_t v___x_1356_, lean_object* v_h_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v_ctors_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v_ctors_1363_ = lean_ctor_get(v_val_1344_, 4);
v___x_1364_ = l_List_get_x21Internal___redArg(v___x_1345_, v_ctors_1363_, v___x_1346_);
lean_inc(v___x_1364_);
v___x_1365_ = l_Lean_mkConstructorElimName(v_indName_1347_, v___x_1364_);
v___x_1366_ = l_Lean_mkConst(v___x_1365_, v___x_1348_);
lean_inc_ref(v_xs2_1349_);
v___x_1367_ = l_Array_append___redArg(v_xs2_1349_, v___x_1350_);
v___x_1368_ = l_Array_append___redArg(v___x_1367_, v_ysx2_1351_);
v___x_1369_ = lean_unsigned_to_nat(1u);
v___x_1370_ = lean_mk_empty_array_with_capacity(v___x_1369_);
v___x_1371_ = lean_array_push(v___x_1370_, v_h_1357_);
v___x_1372_ = l_Array_append___redArg(v___x_1368_, v___x_1371_);
lean_dec_ref(v___x_1371_);
v___x_1373_ = l_Lean_mkAppN(v___x_1366_, v___x_1372_);
lean_dec_ref(v___x_1372_);
lean_inc(v___y_1361_);
lean_inc_ref(v___y_1360_);
lean_inc(v___y_1359_);
lean_inc_ref(v___y_1358_);
lean_inc_ref(v___x_1373_);
v___x_1374_ = lean_infer_type(v___x_1373_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; lean_object* v___x_1376_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_a_1375_);
lean_dec_ref_known(v___x_1374_, 1);
lean_inc(v___y_1361_);
lean_inc_ref(v___y_1360_);
lean_inc(v___y_1359_);
lean_inc_ref(v___y_1358_);
v___x_1376_ = lean_whnf(v_a_1375_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___f_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1377_);
lean_dec_ref_known(v___x_1376_, 1);
v___x_1378_ = lean_box(v___x_1355_);
v___x_1379_ = lean_box(v___x_1356_);
v___f_1380_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__1___boxed), 14, 7);
lean_closure_set(v___f_1380_, 0, v___x_1364_);
lean_closure_set(v___f_1380_, 1, v_P_1352_);
lean_closure_set(v___f_1380_, 2, v_xs1_1353_);
lean_closure_set(v___f_1380_, 3, v_zs1_1354_);
lean_closure_set(v___f_1380_, 4, v_xs2_1349_);
lean_closure_set(v___f_1380_, 5, v___x_1378_);
lean_closure_set(v___f_1380_, 6, v___x_1379_);
v___x_1381_ = l_Lean_Expr_bindingDomain_x21(v_a_1377_);
lean_dec(v_a_1377_);
v___x_1382_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__3___redArg(v___x_1381_, v___f_1380_, v___x_1355_, v___x_1355_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1391_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1385_ = v___x_1382_;
v_isShared_1386_ = v_isSharedCheck_1391_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1382_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1391_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1387_ = l_Lean_Expr_app___override(v___x_1373_, v_a_1383_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1387_);
v___x_1389_ = v___x_1385_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
else
{
lean_dec_ref(v___x_1373_);
return v___x_1382_;
}
}
else
{
lean_dec_ref(v___x_1373_);
lean_dec(v___x_1364_);
lean_dec_ref(v_zs1_1354_);
lean_dec_ref(v_xs1_1353_);
lean_dec_ref(v_P_1352_);
lean_dec_ref(v_xs2_1349_);
return v___x_1376_;
}
}
else
{
lean_dec_ref(v___x_1373_);
lean_dec(v___x_1364_);
lean_dec_ref(v_zs1_1354_);
lean_dec_ref(v_xs1_1353_);
lean_dec_ref(v_P_1352_);
lean_dec_ref(v_xs2_1349_);
return v___x_1374_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__2___boxed(lean_object** _args){
lean_object* v_val_1392_ = _args[0];
lean_object* v___x_1393_ = _args[1];
lean_object* v___x_1394_ = _args[2];
lean_object* v_indName_1395_ = _args[3];
lean_object* v___x_1396_ = _args[4];
lean_object* v_xs2_1397_ = _args[5];
lean_object* v___x_1398_ = _args[6];
lean_object* v_ysx2_1399_ = _args[7];
lean_object* v_P_1400_ = _args[8];
lean_object* v_xs1_1401_ = _args[9];
lean_object* v_zs1_1402_ = _args[10];
lean_object* v___x_1403_ = _args[11];
lean_object* v___x_1404_ = _args[12];
lean_object* v_h_1405_ = _args[13];
lean_object* v___y_1406_ = _args[14];
lean_object* v___y_1407_ = _args[15];
lean_object* v___y_1408_ = _args[16];
lean_object* v___y_1409_ = _args[17];
lean_object* v___y_1410_ = _args[18];
_start:
{
uint8_t v___x_16453__boxed_1411_; uint8_t v___x_16454__boxed_1412_; lean_object* v_res_1413_; 
v___x_16453__boxed_1411_ = lean_unbox(v___x_1403_);
v___x_16454__boxed_1412_ = lean_unbox(v___x_1404_);
v_res_1413_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__2(v_val_1392_, v___x_1393_, v___x_1394_, v_indName_1395_, v___x_1396_, v_xs2_1397_, v___x_1398_, v_ysx2_1399_, v_P_1400_, v_xs1_1401_, v_zs1_1402_, v___x_16453__boxed_1411_, v___x_16454__boxed_1412_, v_h_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec_ref(v_ysx2_1399_);
lean_dec_ref(v___x_1398_);
lean_dec(v_indName_1395_);
lean_dec(v___x_1393_);
lean_dec_ref(v_val_1392_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg___lam__0(uint8_t v___x_1414_, lean_object* v_P_1415_, uint8_t v___x_1416_, uint8_t v___x_1417_, lean_object* v___x_1418_, lean_object* v_xs1_1419_, lean_object* v_zs1_1420_, lean_object* v_xs2_1421_, lean_object* v_zs2_1422_, lean_object* v_x_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
if (v___x_1414_ == 0)
{
uint8_t v___x_1429_; lean_object* v___x_1430_; 
lean_dec_ref(v_xs1_1419_);
lean_dec(v___x_1418_);
v___x_1429_ = 1;
v___x_1430_ = l_Lean_Meta_mkLambdaFVars(v_zs2_1422_, v_P_1415_, v___x_1416_, v___x_1417_, v___x_1416_, v___x_1417_, v___x_1429_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
return v___x_1430_;
}
else
{
lean_object* v___x_1431_; 
lean_inc_ref(v_P_1415_);
v___x_1431_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg(v___x_1418_, v_P_1415_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_a_1432_);
lean_dec_ref_known(v___x_1431_, 1);
v___x_1433_ = l_Array_append___redArg(v_xs1_1419_, v_zs1_1420_);
v___x_1434_ = l_Array_append___redArg(v___x_1433_, v_xs2_1421_);
v___x_1435_ = l_Array_append___redArg(v___x_1434_, v_zs2_1422_);
v___x_1436_ = l_Lean_Expr_beta(v_a_1432_, v___x_1435_);
v___x_1437_ = l_Lean_mkArrow(v___x_1436_, v_P_1415_, v___y_1426_, v___y_1427_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; uint8_t v___x_1439_; lean_object* v___x_1440_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_a_1438_);
lean_dec_ref_known(v___x_1437_, 1);
v___x_1439_ = 1;
v___x_1440_ = l_Lean_Meta_mkLambdaFVars(v_zs2_1422_, v_a_1438_, v___x_1416_, v___x_1417_, v___x_1416_, v___x_1417_, v___x_1439_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
return v___x_1440_;
}
else
{
return v___x_1437_;
}
}
else
{
lean_dec_ref(v_xs1_1419_);
lean_dec_ref(v_P_1415_);
return v___x_1431_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg___lam__0___boxed(lean_object* v___x_1441_, lean_object* v_P_1442_, lean_object* v___x_1443_, lean_object* v___x_1444_, lean_object* v___x_1445_, lean_object* v_xs1_1446_, lean_object* v_zs1_1447_, lean_object* v_xs2_1448_, lean_object* v_zs2_1449_, lean_object* v_x_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
uint8_t v___x_16543__boxed_1456_; uint8_t v___x_16544__boxed_1457_; uint8_t v___x_16545__boxed_1458_; lean_object* v_res_1459_; 
v___x_16543__boxed_1456_ = lean_unbox(v___x_1441_);
v___x_16544__boxed_1457_ = lean_unbox(v___x_1443_);
v___x_16545__boxed_1458_ = lean_unbox(v___x_1444_);
v_res_1459_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg___lam__0(v___x_16543__boxed_1456_, v_P_1442_, v___x_16544__boxed_1457_, v___x_16545__boxed_1458_, v___x_1445_, v_xs1_1446_, v_zs1_1447_, v_xs2_1448_, v_zs2_1449_, v_x_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
lean_dec_ref(v_x_1450_);
lean_dec_ref(v_zs2_1449_);
lean_dec_ref(v_xs2_1448_);
lean_dec_ref(v_zs1_1447_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg(lean_object* v_i_1460_, lean_object* v_P_1461_, lean_object* v___x_1462_, lean_object* v_xs1_1463_, lean_object* v_zs1_1464_, lean_object* v_xs2_1465_, size_t v_sz_1466_, size_t v_i_1467_, lean_object* v_bs_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
uint8_t v___x_1474_; 
v___x_1474_ = lean_usize_dec_lt(v_i_1467_, v_sz_1466_);
if (v___x_1474_ == 0)
{
lean_object* v___x_1475_; 
lean_dec_ref(v_xs2_1465_);
lean_dec_ref(v_zs1_1464_);
lean_dec_ref(v_xs1_1463_);
lean_dec(v___x_1462_);
lean_dec_ref(v_P_1461_);
v___x_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1475_, 0, v_bs_1468_);
return v___x_1475_;
}
else
{
uint8_t v___x_1476_; lean_object* v_v_1477_; lean_object* v___x_1478_; lean_object* v_bs_x27_1479_; lean_object* v___x_1480_; uint8_t v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___f_1485_; lean_object* v___x_1486_; 
v___x_1476_ = 0;
v_v_1477_ = lean_array_uget(v_bs_1468_, v_i_1467_);
v___x_1478_ = lean_unsigned_to_nat(0u);
v_bs_x27_1479_ = lean_array_uset(v_bs_1468_, v_i_1467_, v___x_1478_);
v___x_1480_ = lean_usize_to_nat(v_i_1467_);
v___x_1481_ = lean_nat_dec_eq(v_i_1460_, v___x_1480_);
lean_dec(v___x_1480_);
v___x_1482_ = lean_box(v___x_1481_);
v___x_1483_ = lean_box(v___x_1476_);
v___x_1484_ = lean_box(v___x_1474_);
lean_inc_ref(v_xs2_1465_);
lean_inc_ref(v_zs1_1464_);
lean_inc_ref(v_xs1_1463_);
lean_inc(v___x_1462_);
lean_inc_ref(v_P_1461_);
v___f_1485_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg___lam__0___boxed), 15, 8);
lean_closure_set(v___f_1485_, 0, v___x_1482_);
lean_closure_set(v___f_1485_, 1, v_P_1461_);
lean_closure_set(v___f_1485_, 2, v___x_1483_);
lean_closure_set(v___f_1485_, 3, v___x_1484_);
lean_closure_set(v___f_1485_, 4, v___x_1462_);
lean_closure_set(v___f_1485_, 5, v_xs1_1463_);
lean_closure_set(v___f_1485_, 6, v_zs1_1464_);
lean_closure_set(v___f_1485_, 7, v_xs2_1465_);
v___x_1486_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__3___redArg(v_v_1477_, v___f_1485_, v___x_1476_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1487_; size_t v___x_1488_; size_t v___x_1489_; lean_object* v___x_1490_; 
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
lean_inc(v_a_1487_);
lean_dec_ref_known(v___x_1486_, 1);
v___x_1488_ = ((size_t)1ULL);
v___x_1489_ = lean_usize_add(v_i_1467_, v___x_1488_);
v___x_1490_ = lean_array_uset(v_bs_x27_1479_, v_i_1467_, v_a_1487_);
v_i_1467_ = v___x_1489_;
v_bs_1468_ = v___x_1490_;
goto _start;
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
lean_dec_ref(v_bs_x27_1479_);
lean_dec_ref(v_xs2_1465_);
lean_dec_ref(v_zs1_1464_);
lean_dec_ref(v_xs1_1463_);
lean_dec(v___x_1462_);
lean_dec_ref(v_P_1461_);
v_a_1492_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1486_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1486_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg___boxed(lean_object* v_i_1500_, lean_object* v_P_1501_, lean_object* v___x_1502_, lean_object* v_xs1_1503_, lean_object* v_zs1_1504_, lean_object* v_xs2_1505_, lean_object* v_sz_1506_, lean_object* v_i_1507_, lean_object* v_bs_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
size_t v_sz_boxed_1514_; size_t v_i_boxed_1515_; lean_object* v_res_1516_; 
v_sz_boxed_1514_ = lean_unbox_usize(v_sz_1506_);
lean_dec(v_sz_1506_);
v_i_boxed_1515_ = lean_unbox_usize(v_i_1507_);
lean_dec(v_i_1507_);
v_res_1516_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg(v_i_1500_, v_P_1501_, v___x_1502_, v_xs1_1503_, v_zs1_1504_, v_xs2_1505_, v_sz_boxed_1514_, v_i_boxed_1515_, v_bs_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v_i_1500_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__3(uint8_t v___y_1517_, lean_object* v_xs2_1518_, lean_object* v___x_1519_, lean_object* v_ysx2_1520_, lean_object* v___x_1521_, lean_object* v___x_1522_, lean_object* v_val_1523_, lean_object* v___x_1524_, lean_object* v___x_1525_, lean_object* v_P_1526_, lean_object* v_xs1_1527_, uint8_t v___x_1528_, uint8_t v___x_1529_, lean_object* v_indName_1530_, lean_object* v___x_1531_, lean_object* v_tail_1532_, lean_object* v___x_1533_, lean_object* v___f_1534_, lean_object* v_zs1_1535_, lean_object* v_x_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
if (v___y_1517_ == 0)
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
lean_dec_ref(v___f_1534_);
lean_dec_ref(v___x_1533_);
lean_dec(v_tail_1532_);
lean_dec(v___x_1531_);
lean_dec(v_indName_1530_);
lean_inc_ref(v_xs2_1518_);
v___x_1542_ = l_Array_append___redArg(v_xs2_1518_, v___x_1519_);
lean_dec_ref(v___x_1519_);
v___x_1543_ = l_Array_append___redArg(v___x_1542_, v_ysx2_1520_);
lean_dec_ref(v_ysx2_1520_);
v___x_1544_ = l_Lean_mkAppN(v___x_1521_, v___x_1543_);
lean_dec_ref(v___x_1543_);
lean_inc(v___y_1540_);
lean_inc_ref(v___y_1539_);
lean_inc(v___y_1538_);
lean_inc_ref(v___y_1537_);
lean_inc_ref(v___x_1544_);
v___x_1545_ = lean_infer_type(v___x_1544_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1547_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref_known(v___x_1545_, 1);
v___x_1547_ = l_Lean_Meta_arrowDomainsN(v___x_1522_, v_a_1546_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v_ctors_1549_; lean_object* v___x_1550_; size_t v_sz_1551_; size_t v___x_1552_; lean_object* v___x_1553_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1548_);
lean_dec_ref_known(v___x_1547_, 1);
v_ctors_1549_ = lean_ctor_get(v_val_1523_, 4);
lean_inc(v_ctors_1549_);
lean_dec_ref(v_val_1523_);
lean_inc(v___x_1525_);
v___x_1550_ = l_List_get_x21Internal___redArg(v___x_1524_, v_ctors_1549_, v___x_1525_);
lean_dec(v_ctors_1549_);
lean_dec(v___x_1524_);
v_sz_1551_ = lean_array_size(v_a_1548_);
v___x_1552_ = ((size_t)0ULL);
lean_inc_ref(v_zs1_1535_);
v___x_1553_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg(v___x_1525_, v_P_1526_, v___x_1550_, v_xs1_1527_, v_zs1_1535_, v_xs2_1518_, v_sz_1551_, v___x_1552_, v_a_1548_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
lean_dec(v___x_1525_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; lean_object* v___x_1557_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1554_);
lean_dec_ref_known(v___x_1553_, 1);
v___x_1555_ = l_Lean_mkAppN(v___x_1544_, v_a_1554_);
lean_dec(v_a_1554_);
v___x_1556_ = 1;
v___x_1557_ = l_Lean_Meta_mkLambdaFVars(v_zs1_1535_, v___x_1555_, v___x_1528_, v___x_1529_, v___x_1528_, v___x_1529_, v___x_1556_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
lean_dec_ref(v_zs1_1535_);
return v___x_1557_;
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_dec_ref(v___x_1544_);
lean_dec_ref(v_zs1_1535_);
v_a_1558_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1553_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1553_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
lean_dec_ref(v___x_1544_);
lean_dec_ref(v_zs1_1535_);
lean_dec_ref(v_xs1_1527_);
lean_dec_ref(v_P_1526_);
lean_dec(v___x_1525_);
lean_dec(v___x_1524_);
lean_dec_ref(v_val_1523_);
lean_dec_ref(v_xs2_1518_);
v_a_1566_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1547_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1547_);
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
else
{
lean_dec_ref(v___x_1544_);
lean_dec_ref(v_zs1_1535_);
lean_dec_ref(v_xs1_1527_);
lean_dec_ref(v_P_1526_);
lean_dec(v___x_1525_);
lean_dec(v___x_1524_);
lean_dec_ref(v_val_1523_);
lean_dec(v___x_1522_);
lean_dec_ref(v_xs2_1518_);
return v___x_1545_;
}
}
else
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___f_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
lean_dec(v___x_1522_);
lean_dec_ref(v___x_1521_);
v___x_1574_ = lean_box(v___x_1528_);
v___x_1575_ = lean_box(v___x_1529_);
lean_inc_ref(v_zs1_1535_);
lean_inc_ref(v_ysx2_1520_);
lean_inc_ref(v_xs2_1518_);
lean_inc(v_indName_1530_);
lean_inc(v___x_1525_);
v___f_1576_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__2___boxed), 19, 13);
lean_closure_set(v___f_1576_, 0, v_val_1523_);
lean_closure_set(v___f_1576_, 1, v___x_1524_);
lean_closure_set(v___f_1576_, 2, v___x_1525_);
lean_closure_set(v___f_1576_, 3, v_indName_1530_);
lean_closure_set(v___f_1576_, 4, v___x_1531_);
lean_closure_set(v___f_1576_, 5, v_xs2_1518_);
lean_closure_set(v___f_1576_, 6, v___x_1519_);
lean_closure_set(v___f_1576_, 7, v_ysx2_1520_);
lean_closure_set(v___f_1576_, 8, v_P_1526_);
lean_closure_set(v___f_1576_, 9, v_xs1_1527_);
lean_closure_set(v___f_1576_, 10, v_zs1_1535_);
lean_closure_set(v___f_1576_, 11, v___x_1574_);
lean_closure_set(v___f_1576_, 12, v___x_1575_);
v___x_1577_ = l_Lean_mkCtorIdxName(v_indName_1530_);
v___x_1578_ = l_Lean_mkConst(v___x_1577_, v_tail_1532_);
v___x_1579_ = l_Array_append___redArg(v_xs2_1518_, v_ysx2_1520_);
lean_dec_ref(v_ysx2_1520_);
v___x_1580_ = l_Lean_mkAppN(v___x_1578_, v___x_1579_);
lean_dec_ref(v___x_1579_);
v___x_1581_ = l_Lean_mkRawNatLit(v___x_1525_);
v___x_1582_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq(v___x_1533_, v___x_1580_, v___x_1581_, v___f_1576_, v___f_1534_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; uint8_t v___x_1584_; lean_object* v___x_1585_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref_known(v___x_1582_, 1);
v___x_1584_ = 1;
v___x_1585_ = l_Lean_Meta_mkLambdaFVars(v_zs1_1535_, v_a_1583_, v___x_1528_, v___x_1529_, v___x_1528_, v___x_1529_, v___x_1584_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
lean_dec_ref(v_zs1_1535_);
return v___x_1585_;
}
else
{
lean_dec_ref(v_zs1_1535_);
return v___x_1582_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___y_1586_ = _args[0];
lean_object* v_xs2_1587_ = _args[1];
lean_object* v___x_1588_ = _args[2];
lean_object* v_ysx2_1589_ = _args[3];
lean_object* v___x_1590_ = _args[4];
lean_object* v___x_1591_ = _args[5];
lean_object* v_val_1592_ = _args[6];
lean_object* v___x_1593_ = _args[7];
lean_object* v___x_1594_ = _args[8];
lean_object* v_P_1595_ = _args[9];
lean_object* v_xs1_1596_ = _args[10];
lean_object* v___x_1597_ = _args[11];
lean_object* v___x_1598_ = _args[12];
lean_object* v_indName_1599_ = _args[13];
lean_object* v___x_1600_ = _args[14];
lean_object* v_tail_1601_ = _args[15];
lean_object* v___x_1602_ = _args[16];
lean_object* v___f_1603_ = _args[17];
lean_object* v_zs1_1604_ = _args[18];
lean_object* v_x_1605_ = _args[19];
lean_object* v___y_1606_ = _args[20];
lean_object* v___y_1607_ = _args[21];
lean_object* v___y_1608_ = _args[22];
lean_object* v___y_1609_ = _args[23];
lean_object* v___y_1610_ = _args[24];
_start:
{
uint8_t v___y_16665__boxed_1611_; uint8_t v___x_16672__boxed_1612_; uint8_t v___x_16673__boxed_1613_; lean_object* v_res_1614_; 
v___y_16665__boxed_1611_ = lean_unbox(v___y_1586_);
v___x_16672__boxed_1612_ = lean_unbox(v___x_1597_);
v___x_16673__boxed_1613_ = lean_unbox(v___x_1598_);
v_res_1614_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__3(v___y_16665__boxed_1611_, v_xs2_1587_, v___x_1588_, v_ysx2_1589_, v___x_1590_, v___x_1591_, v_val_1592_, v___x_1593_, v___x_1594_, v_P_1595_, v_xs1_1596_, v___x_16672__boxed_1612_, v___x_16673__boxed_1613_, v_indName_1599_, v___x_1600_, v_tail_1601_, v___x_1602_, v___f_1603_, v_zs1_1604_, v_x_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec_ref(v_x_1605_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg(lean_object* v_val_1615_, lean_object* v_P_1616_, lean_object* v_xs1_1617_, lean_object* v_xs2_1618_, lean_object* v_indName_1619_, lean_object* v___x_1620_, lean_object* v___x_1621_, lean_object* v_ysx2_1622_, uint8_t v___y_1623_, lean_object* v___x_1624_, lean_object* v___x_1625_, lean_object* v_tail_1626_, lean_object* v___x_1627_, size_t v_sz_1628_, size_t v_i_1629_, lean_object* v_bs_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
uint8_t v___x_1636_; 
v___x_1636_ = lean_usize_dec_lt(v_i_1629_, v_sz_1628_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; 
lean_dec_ref(v___x_1627_);
lean_dec(v_tail_1626_);
lean_dec(v___x_1625_);
lean_dec_ref(v___x_1624_);
lean_dec_ref(v_ysx2_1622_);
lean_dec_ref(v___x_1621_);
lean_dec(v___x_1620_);
lean_dec(v_indName_1619_);
lean_dec_ref(v_xs2_1618_);
lean_dec_ref(v_xs1_1617_);
lean_dec_ref(v_P_1616_);
lean_dec_ref(v_val_1615_);
v___x_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1637_, 0, v_bs_1630_);
return v___x_1637_;
}
else
{
lean_object* v___f_1638_; lean_object* v___x_1639_; uint8_t v___x_1640_; lean_object* v_v_1641_; lean_object* v___x_1642_; lean_object* v_bs_x27_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___f_1648_; lean_object* v___x_1649_; 
lean_inc_ref_n(v_P_1616_, 2);
v___f_1638_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1638_, 0, v_P_1616_);
v___x_1639_ = lean_box(0);
v___x_1640_ = 0;
v_v_1641_ = lean_array_uget(v_bs_1630_, v_i_1629_);
v___x_1642_ = lean_unsigned_to_nat(0u);
v_bs_x27_1643_ = lean_array_uset(v_bs_1630_, v_i_1629_, v___x_1642_);
v___x_1644_ = lean_usize_to_nat(v_i_1629_);
v___x_1645_ = lean_box(v___y_1623_);
v___x_1646_ = lean_box(v___x_1640_);
v___x_1647_ = lean_box(v___x_1636_);
lean_inc_ref(v___x_1627_);
lean_inc(v_tail_1626_);
lean_inc(v___x_1620_);
lean_inc(v_indName_1619_);
lean_inc_ref(v_xs1_1617_);
lean_inc_ref(v_val_1615_);
lean_inc(v___x_1625_);
lean_inc_ref(v___x_1624_);
lean_inc_ref(v_ysx2_1622_);
lean_inc_ref(v___x_1621_);
lean_inc_ref(v_xs2_1618_);
v___f_1648_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__3___boxed), 25, 18);
lean_closure_set(v___f_1648_, 0, v___x_1645_);
lean_closure_set(v___f_1648_, 1, v_xs2_1618_);
lean_closure_set(v___f_1648_, 2, v___x_1621_);
lean_closure_set(v___f_1648_, 3, v_ysx2_1622_);
lean_closure_set(v___f_1648_, 4, v___x_1624_);
lean_closure_set(v___f_1648_, 5, v___x_1625_);
lean_closure_set(v___f_1648_, 6, v_val_1615_);
lean_closure_set(v___f_1648_, 7, v___x_1639_);
lean_closure_set(v___f_1648_, 8, v___x_1644_);
lean_closure_set(v___f_1648_, 9, v_P_1616_);
lean_closure_set(v___f_1648_, 10, v_xs1_1617_);
lean_closure_set(v___f_1648_, 11, v___x_1646_);
lean_closure_set(v___f_1648_, 12, v___x_1647_);
lean_closure_set(v___f_1648_, 13, v_indName_1619_);
lean_closure_set(v___f_1648_, 14, v___x_1620_);
lean_closure_set(v___f_1648_, 15, v_tail_1626_);
lean_closure_set(v___f_1648_, 16, v___x_1627_);
lean_closure_set(v___f_1648_, 17, v___f_1638_);
v___x_1649_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__3___redArg(v_v_1641_, v___f_1648_, v___x_1640_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_a_1650_; size_t v___x_1651_; size_t v___x_1652_; lean_object* v___x_1653_; 
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_a_1650_);
lean_dec_ref_known(v___x_1649_, 1);
v___x_1651_ = ((size_t)1ULL);
v___x_1652_ = lean_usize_add(v_i_1629_, v___x_1651_);
v___x_1653_ = lean_array_uset(v_bs_x27_1643_, v_i_1629_, v_a_1650_);
v_i_1629_ = v___x_1652_;
v_bs_1630_ = v___x_1653_;
goto _start;
}
else
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1662_; 
lean_dec_ref(v_bs_x27_1643_);
lean_dec_ref(v___x_1627_);
lean_dec(v_tail_1626_);
lean_dec(v___x_1625_);
lean_dec_ref(v___x_1624_);
lean_dec_ref(v_ysx2_1622_);
lean_dec_ref(v___x_1621_);
lean_dec(v___x_1620_);
lean_dec(v_indName_1619_);
lean_dec_ref(v_xs2_1618_);
lean_dec_ref(v_xs1_1617_);
lean_dec_ref(v_P_1616_);
lean_dec_ref(v_val_1615_);
v_a_1655_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1657_ = v___x_1649_;
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1649_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___boxed(lean_object** _args){
lean_object* v_val_1663_ = _args[0];
lean_object* v_P_1664_ = _args[1];
lean_object* v_xs1_1665_ = _args[2];
lean_object* v_xs2_1666_ = _args[3];
lean_object* v_indName_1667_ = _args[4];
lean_object* v___x_1668_ = _args[5];
lean_object* v___x_1669_ = _args[6];
lean_object* v_ysx2_1670_ = _args[7];
lean_object* v___y_1671_ = _args[8];
lean_object* v___x_1672_ = _args[9];
lean_object* v___x_1673_ = _args[10];
lean_object* v_tail_1674_ = _args[11];
lean_object* v___x_1675_ = _args[12];
lean_object* v_sz_1676_ = _args[13];
lean_object* v_i_1677_ = _args[14];
lean_object* v_bs_1678_ = _args[15];
lean_object* v___y_1679_ = _args[16];
lean_object* v___y_1680_ = _args[17];
lean_object* v___y_1681_ = _args[18];
lean_object* v___y_1682_ = _args[19];
lean_object* v___y_1683_ = _args[20];
_start:
{
uint8_t v___y_16811__boxed_1684_; size_t v_sz_boxed_1685_; size_t v_i_boxed_1686_; lean_object* v_res_1687_; 
v___y_16811__boxed_1684_ = lean_unbox(v___y_1671_);
v_sz_boxed_1685_ = lean_unbox_usize(v_sz_1676_);
lean_dec(v_sz_1676_);
v_i_boxed_1686_ = lean_unbox_usize(v_i_1677_);
lean_dec(v_i_1677_);
v_res_1687_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg(v_val_1663_, v_P_1664_, v_xs1_1665_, v_xs2_1666_, v_indName_1667_, v___x_1668_, v___x_1669_, v_ysx2_1670_, v___y_16811__boxed_1684_, v___x_1672_, v___x_1673_, v_tail_1674_, v___x_1675_, v_sz_boxed_1685_, v_i_boxed_1686_, v_bs_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__1(lean_object* v___x_1688_, lean_object* v_t1_1689_, lean_object* v_val_1690_, lean_object* v_P_1691_, lean_object* v_xs1_1692_, lean_object* v_xs2_1693_, lean_object* v_indName_1694_, lean_object* v___x_1695_, lean_object* v___x_1696_, lean_object* v_ysx2_1697_, uint8_t v___y_1698_, lean_object* v___x_1699_, lean_object* v_tail_1700_, lean_object* v___x_1701_, lean_object* v___x_1702_, lean_object* v___x_1703_, lean_object* v_ysx1_1704_, uint8_t v___x_1705_, uint8_t v___x_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
lean_object* v___x_1712_; 
lean_inc(v___x_1688_);
v___x_1712_ = l_Lean_Meta_arrowDomainsN(v___x_1688_, v_t1_1689_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; size_t v_sz_1714_; size_t v___x_1715_; lean_object* v___x_1716_; 
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_a_1713_);
lean_dec_ref_known(v___x_1712_, 1);
v_sz_1714_ = lean_array_size(v_a_1713_);
v___x_1715_ = ((size_t)0ULL);
lean_inc_ref(v_ysx2_1697_);
lean_inc_ref(v_xs2_1693_);
lean_inc_ref(v_xs1_1692_);
lean_inc_ref(v_P_1691_);
v___x_1716_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg(v_val_1690_, v_P_1691_, v_xs1_1692_, v_xs2_1693_, v_indName_1694_, v___x_1695_, v___x_1696_, v_ysx2_1697_, v___y_1698_, v___x_1699_, v___x_1688_, v_tail_1700_, v___x_1701_, v_sz_1714_, v___x_1715_, v_a_1713_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; uint8_t v___x_1724_; lean_object* v___x_1725_; 
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_a_1717_);
lean_dec_ref_known(v___x_1716_, 1);
v___x_1718_ = l_Lean_mkAppN(v___x_1702_, v_a_1717_);
lean_dec(v_a_1717_);
v___x_1719_ = lean_array_push(v___x_1703_, v_P_1691_);
v___x_1720_ = l_Array_append___redArg(v___x_1719_, v_xs1_1692_);
lean_dec_ref(v_xs1_1692_);
v___x_1721_ = l_Array_append___redArg(v___x_1720_, v_ysx1_1704_);
v___x_1722_ = l_Array_append___redArg(v___x_1721_, v_xs2_1693_);
lean_dec_ref(v_xs2_1693_);
v___x_1723_ = l_Array_append___redArg(v___x_1722_, v_ysx2_1697_);
lean_dec_ref(v_ysx2_1697_);
v___x_1724_ = 1;
v___x_1725_ = l_Lean_Meta_mkLambdaFVars(v___x_1723_, v___x_1718_, v___x_1705_, v___x_1706_, v___x_1705_, v___x_1706_, v___x_1724_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
lean_dec_ref(v___x_1723_);
return v___x_1725_;
}
else
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
lean_dec_ref(v___x_1703_);
lean_dec_ref(v___x_1702_);
lean_dec_ref(v_ysx2_1697_);
lean_dec_ref(v_xs2_1693_);
lean_dec_ref(v_xs1_1692_);
lean_dec_ref(v_P_1691_);
v_a_1726_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1728_ = v___x_1716_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1716_);
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
}
else
{
lean_object* v_a_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1741_; 
lean_dec_ref(v___x_1703_);
lean_dec_ref(v___x_1702_);
lean_dec_ref(v___x_1701_);
lean_dec(v_tail_1700_);
lean_dec_ref(v___x_1699_);
lean_dec_ref(v_ysx2_1697_);
lean_dec_ref(v___x_1696_);
lean_dec(v___x_1695_);
lean_dec(v_indName_1694_);
lean_dec_ref(v_xs2_1693_);
lean_dec_ref(v_xs1_1692_);
lean_dec_ref(v_P_1691_);
lean_dec_ref(v_val_1690_);
lean_dec(v___x_1688_);
v_a_1734_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1736_ = v___x_1712_;
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_a_1734_);
lean_dec(v___x_1712_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1739_; 
if (v_isShared_1737_ == 0)
{
v___x_1739_ = v___x_1736_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_a_1734_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__1___boxed(lean_object** _args){
lean_object* v___x_1742_ = _args[0];
lean_object* v_t1_1743_ = _args[1];
lean_object* v_val_1744_ = _args[2];
lean_object* v_P_1745_ = _args[3];
lean_object* v_xs1_1746_ = _args[4];
lean_object* v_xs2_1747_ = _args[5];
lean_object* v_indName_1748_ = _args[6];
lean_object* v___x_1749_ = _args[7];
lean_object* v___x_1750_ = _args[8];
lean_object* v_ysx2_1751_ = _args[9];
lean_object* v___y_1752_ = _args[10];
lean_object* v___x_1753_ = _args[11];
lean_object* v_tail_1754_ = _args[12];
lean_object* v___x_1755_ = _args[13];
lean_object* v___x_1756_ = _args[14];
lean_object* v___x_1757_ = _args[15];
lean_object* v_ysx1_1758_ = _args[16];
lean_object* v___x_1759_ = _args[17];
lean_object* v___x_1760_ = _args[18];
lean_object* v___y_1761_ = _args[19];
lean_object* v___y_1762_ = _args[20];
lean_object* v___y_1763_ = _args[21];
lean_object* v___y_1764_ = _args[22];
lean_object* v___y_1765_ = _args[23];
_start:
{
uint8_t v___y_16901__boxed_1766_; uint8_t v___x_16907__boxed_1767_; uint8_t v___x_16908__boxed_1768_; lean_object* v_res_1769_; 
v___y_16901__boxed_1766_ = lean_unbox(v___y_1752_);
v___x_16907__boxed_1767_ = lean_unbox(v___x_1759_);
v___x_16908__boxed_1768_ = lean_unbox(v___x_1760_);
v_res_1769_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__1(v___x_1742_, v_t1_1743_, v_val_1744_, v_P_1745_, v_xs1_1746_, v_xs2_1747_, v_indName_1748_, v___x_1749_, v___x_1750_, v_ysx2_1751_, v___y_16901__boxed_1766_, v___x_1753_, v_tail_1754_, v___x_1755_, v___x_1756_, v___x_1757_, v_ysx1_1758_, v___x_16907__boxed_1767_, v___x_16908__boxed_1768_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec_ref(v_ysx1_1758_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__2(lean_object* v___x_1770_, lean_object* v_ysx1_1771_, lean_object* v___x_1772_, lean_object* v_t1_1773_, lean_object* v_val_1774_, lean_object* v_P_1775_, lean_object* v_xs1_1776_, lean_object* v_xs2_1777_, lean_object* v_indName_1778_, lean_object* v___x_1779_, lean_object* v___x_1780_, uint8_t v___y_1781_, lean_object* v___x_1782_, lean_object* v_tail_1783_, lean_object* v___x_1784_, lean_object* v___x_1785_, uint8_t v___x_1786_, uint8_t v___x_1787_, lean_object* v_ysx2_1788_, lean_object* v___t2_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___f_1799_; lean_object* v___x_1800_; 
v___x_1795_ = l_Lean_mkAppN(v___x_1770_, v_ysx1_1771_);
v___x_1796_ = lean_box(v___y_1781_);
v___x_1797_ = lean_box(v___x_1786_);
v___x_1798_ = lean_box(v___x_1787_);
lean_inc_ref(v_ysx2_1788_);
v___f_1799_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__1___boxed), 24, 19);
lean_closure_set(v___f_1799_, 0, v___x_1772_);
lean_closure_set(v___f_1799_, 1, v_t1_1773_);
lean_closure_set(v___f_1799_, 2, v_val_1774_);
lean_closure_set(v___f_1799_, 3, v_P_1775_);
lean_closure_set(v___f_1799_, 4, v_xs1_1776_);
lean_closure_set(v___f_1799_, 5, v_xs2_1777_);
lean_closure_set(v___f_1799_, 6, v_indName_1778_);
lean_closure_set(v___f_1799_, 7, v___x_1779_);
lean_closure_set(v___f_1799_, 8, v___x_1780_);
lean_closure_set(v___f_1799_, 9, v_ysx2_1788_);
lean_closure_set(v___f_1799_, 10, v___x_1796_);
lean_closure_set(v___f_1799_, 11, v___x_1782_);
lean_closure_set(v___f_1799_, 12, v_tail_1783_);
lean_closure_set(v___f_1799_, 13, v___x_1784_);
lean_closure_set(v___f_1799_, 14, v___x_1795_);
lean_closure_set(v___f_1799_, 15, v___x_1785_);
lean_closure_set(v___f_1799_, 16, v_ysx1_1771_);
lean_closure_set(v___f_1799_, 17, v___x_1797_);
lean_closure_set(v___f_1799_, 18, v___x_1798_);
v___x_1800_ = l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__2___redArg(v_ysx2_1788_, v___f_1799_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__2___boxed(lean_object** _args){
lean_object* v___x_1801_ = _args[0];
lean_object* v_ysx1_1802_ = _args[1];
lean_object* v___x_1803_ = _args[2];
lean_object* v_t1_1804_ = _args[3];
lean_object* v_val_1805_ = _args[4];
lean_object* v_P_1806_ = _args[5];
lean_object* v_xs1_1807_ = _args[6];
lean_object* v_xs2_1808_ = _args[7];
lean_object* v_indName_1809_ = _args[8];
lean_object* v___x_1810_ = _args[9];
lean_object* v___x_1811_ = _args[10];
lean_object* v___y_1812_ = _args[11];
lean_object* v___x_1813_ = _args[12];
lean_object* v_tail_1814_ = _args[13];
lean_object* v___x_1815_ = _args[14];
lean_object* v___x_1816_ = _args[15];
lean_object* v___x_1817_ = _args[16];
lean_object* v___x_1818_ = _args[17];
lean_object* v_ysx2_1819_ = _args[18];
lean_object* v___t2_1820_ = _args[19];
lean_object* v___y_1821_ = _args[20];
lean_object* v___y_1822_ = _args[21];
lean_object* v___y_1823_ = _args[22];
lean_object* v___y_1824_ = _args[23];
lean_object* v___y_1825_ = _args[24];
_start:
{
uint8_t v___y_17011__boxed_1826_; uint8_t v___x_17016__boxed_1827_; uint8_t v___x_17017__boxed_1828_; lean_object* v_res_1829_; 
v___y_17011__boxed_1826_ = lean_unbox(v___y_1812_);
v___x_17016__boxed_1827_ = lean_unbox(v___x_1817_);
v___x_17017__boxed_1828_ = lean_unbox(v___x_1818_);
v_res_1829_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__2(v___x_1801_, v_ysx1_1802_, v___x_1803_, v_t1_1804_, v_val_1805_, v_P_1806_, v_xs1_1807_, v_xs2_1808_, v_indName_1809_, v___x_1810_, v___x_1811_, v___y_17011__boxed_1826_, v___x_1813_, v_tail_1814_, v___x_1815_, v___x_1816_, v___x_17016__boxed_1827_, v___x_17017__boxed_1828_, v_ysx2_1819_, v___t2_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec_ref(v___t2_1820_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__3(lean_object* v___x_1830_, lean_object* v___x_1831_, lean_object* v_val_1832_, lean_object* v_P_1833_, lean_object* v_xs1_1834_, lean_object* v_xs2_1835_, lean_object* v_indName_1836_, lean_object* v___x_1837_, lean_object* v___x_1838_, uint8_t v___y_1839_, lean_object* v___x_1840_, lean_object* v_tail_1841_, lean_object* v___x_1842_, lean_object* v___x_1843_, uint8_t v___x_1844_, uint8_t v___x_1845_, lean_object* v_a_1846_, lean_object* v___x_1847_, lean_object* v_ysx1_1848_, lean_object* v_t1_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___f_1858_; lean_object* v___x_1859_; 
v___x_1855_ = lean_box(v___y_1839_);
v___x_1856_ = lean_box(v___x_1844_);
v___x_1857_ = lean_box(v___x_1845_);
v___f_1858_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__2___boxed), 25, 18);
lean_closure_set(v___f_1858_, 0, v___x_1830_);
lean_closure_set(v___f_1858_, 1, v_ysx1_1848_);
lean_closure_set(v___f_1858_, 2, v___x_1831_);
lean_closure_set(v___f_1858_, 3, v_t1_1849_);
lean_closure_set(v___f_1858_, 4, v_val_1832_);
lean_closure_set(v___f_1858_, 5, v_P_1833_);
lean_closure_set(v___f_1858_, 6, v_xs1_1834_);
lean_closure_set(v___f_1858_, 7, v_xs2_1835_);
lean_closure_set(v___f_1858_, 8, v_indName_1836_);
lean_closure_set(v___f_1858_, 9, v___x_1837_);
lean_closure_set(v___f_1858_, 10, v___x_1838_);
lean_closure_set(v___f_1858_, 11, v___x_1855_);
lean_closure_set(v___f_1858_, 12, v___x_1840_);
lean_closure_set(v___f_1858_, 13, v_tail_1841_);
lean_closure_set(v___f_1858_, 14, v___x_1842_);
lean_closure_set(v___f_1858_, 15, v___x_1843_);
lean_closure_set(v___f_1858_, 16, v___x_1856_);
lean_closure_set(v___f_1858_, 17, v___x_1857_);
v___x_1859_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(v_a_1846_, v___x_1847_, v___f_1858_, v___x_1844_, v___x_1844_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__3___boxed(lean_object** _args){
lean_object* v___x_1860_ = _args[0];
lean_object* v___x_1861_ = _args[1];
lean_object* v_val_1862_ = _args[2];
lean_object* v_P_1863_ = _args[3];
lean_object* v_xs1_1864_ = _args[4];
lean_object* v_xs2_1865_ = _args[5];
lean_object* v_indName_1866_ = _args[6];
lean_object* v___x_1867_ = _args[7];
lean_object* v___x_1868_ = _args[8];
lean_object* v___y_1869_ = _args[9];
lean_object* v___x_1870_ = _args[10];
lean_object* v_tail_1871_ = _args[11];
lean_object* v___x_1872_ = _args[12];
lean_object* v___x_1873_ = _args[13];
lean_object* v___x_1874_ = _args[14];
lean_object* v___x_1875_ = _args[15];
lean_object* v_a_1876_ = _args[16];
lean_object* v___x_1877_ = _args[17];
lean_object* v_ysx1_1878_ = _args[18];
lean_object* v_t1_1879_ = _args[19];
lean_object* v___y_1880_ = _args[20];
lean_object* v___y_1881_ = _args[21];
lean_object* v___y_1882_ = _args[22];
lean_object* v___y_1883_ = _args[23];
lean_object* v___y_1884_ = _args[24];
_start:
{
uint8_t v___y_17074__boxed_1885_; uint8_t v___x_17079__boxed_1886_; uint8_t v___x_17080__boxed_1887_; lean_object* v_res_1888_; 
v___y_17074__boxed_1885_ = lean_unbox(v___y_1869_);
v___x_17079__boxed_1886_ = lean_unbox(v___x_1874_);
v___x_17080__boxed_1887_ = lean_unbox(v___x_1875_);
v_res_1888_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__3(v___x_1860_, v___x_1861_, v_val_1862_, v_P_1863_, v_xs1_1864_, v_xs2_1865_, v_indName_1866_, v___x_1867_, v___x_1868_, v___y_17074__boxed_1885_, v___x_1870_, v_tail_1871_, v___x_1872_, v___x_1873_, v___x_17079__boxed_1886_, v___x_17080__boxed_1887_, v_a_1876_, v___x_1877_, v_ysx1_1878_, v_t1_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__4(lean_object* v_t1_1889_, lean_object* v___f_1890_, lean_object* v_t2_1891_, lean_object* v___x_1892_, lean_object* v_numIndices_1893_, lean_object* v___x_1894_, lean_object* v_val_1895_, lean_object* v_P_1896_, lean_object* v_xs1_1897_, lean_object* v_xs2_1898_, lean_object* v_indName_1899_, lean_object* v___x_1900_, uint8_t v___y_1901_, lean_object* v___x_1902_, lean_object* v_tail_1903_, lean_object* v___x_1904_, uint8_t v___x_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v___x_1911_; 
lean_inc_ref(v_t1_1889_);
v___x_1911_ = l_Lean_Meta_whnfD(v_t1_1889_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1913_; uint8_t v___x_1914_; lean_object* v___x_1915_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref_known(v___x_1911_, 1);
v___x_1913_ = l_Lean_Expr_bindingDomain_x21(v_a_1912_);
lean_dec(v_a_1912_);
v___x_1914_ = 0;
lean_inc_ref(v___f_1890_);
v___x_1915_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__3___redArg(v___x_1913_, v___f_1890_, v___x_1914_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc_n(v_a_1916_, 2);
lean_dec_ref_known(v___x_1915_, 1);
v___x_1917_ = lean_unsigned_to_nat(1u);
v___x_1918_ = lean_mk_empty_array_with_capacity(v___x_1917_);
lean_inc_ref(v___x_1918_);
v___x_1919_ = lean_array_push(v___x_1918_, v_a_1916_);
v___x_1920_ = l_Lean_Meta_instantiateForall(v_t1_1889_, v___x_1919_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
lean_dec_ref(v___x_1919_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v___x_1922_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1921_);
lean_dec_ref_known(v___x_1920_, 1);
lean_inc_ref(v_t2_1891_);
v___x_1922_ = l_Lean_Meta_whnfD(v_t2_1891_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_a_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
lean_inc(v_a_1923_);
lean_dec_ref_known(v___x_1922_, 1);
v___x_1924_ = l_Lean_Expr_bindingDomain_x21(v_a_1923_);
lean_dec(v_a_1923_);
v___x_1925_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__3___redArg(v___x_1924_, v___f_1890_, v___x_1914_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1926_);
lean_dec_ref_known(v___x_1925_, 1);
lean_inc_ref(v___x_1918_);
v___x_1927_ = lean_array_push(v___x_1918_, v_a_1926_);
v___x_1928_ = l_Lean_Meta_instantiateForall(v_t2_1891_, v___x_1927_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1943_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1931_ = v___x_1928_;
v_isShared_1932_ = v_isSharedCheck_1943_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1928_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1943_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1936_; 
v___x_1933_ = l_Lean_Expr_app___override(v___x_1892_, v_a_1916_);
v___x_1934_ = lean_nat_add(v_numIndices_1893_, v___x_1917_);
if (v_isShared_1932_ == 0)
{
lean_ctor_set_tag(v___x_1931_, 1);
lean_ctor_set(v___x_1931_, 0, v___x_1934_);
v___x_1936_ = v___x_1931_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1934_);
v___x_1936_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___f_1940_; lean_object* v___x_1941_; 
v___x_1937_ = lean_box(v___y_1901_);
v___x_1938_ = lean_box(v___x_1914_);
v___x_1939_ = lean_box(v___x_1905_);
lean_inc_ref(v___x_1936_);
v___f_1940_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__3___boxed), 25, 18);
lean_closure_set(v___f_1940_, 0, v___x_1933_);
lean_closure_set(v___f_1940_, 1, v___x_1894_);
lean_closure_set(v___f_1940_, 2, v_val_1895_);
lean_closure_set(v___f_1940_, 3, v_P_1896_);
lean_closure_set(v___f_1940_, 4, v_xs1_1897_);
lean_closure_set(v___f_1940_, 5, v_xs2_1898_);
lean_closure_set(v___f_1940_, 6, v_indName_1899_);
lean_closure_set(v___f_1940_, 7, v___x_1900_);
lean_closure_set(v___f_1940_, 8, v___x_1927_);
lean_closure_set(v___f_1940_, 9, v___x_1937_);
lean_closure_set(v___f_1940_, 10, v___x_1902_);
lean_closure_set(v___f_1940_, 11, v_tail_1903_);
lean_closure_set(v___f_1940_, 12, v___x_1904_);
lean_closure_set(v___f_1940_, 13, v___x_1918_);
lean_closure_set(v___f_1940_, 14, v___x_1938_);
lean_closure_set(v___f_1940_, 15, v___x_1939_);
lean_closure_set(v___f_1940_, 16, v_a_1929_);
lean_closure_set(v___f_1940_, 17, v___x_1936_);
v___x_1941_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(v_a_1921_, v___x_1936_, v___f_1940_, v___x_1914_, v___x_1914_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
return v___x_1941_;
}
}
}
else
{
lean_dec_ref(v___x_1927_);
lean_dec(v_a_1921_);
lean_dec_ref(v___x_1918_);
lean_dec(v_a_1916_);
lean_dec_ref(v___x_1904_);
lean_dec(v_tail_1903_);
lean_dec_ref(v___x_1902_);
lean_dec(v___x_1900_);
lean_dec(v_indName_1899_);
lean_dec_ref(v_xs2_1898_);
lean_dec_ref(v_xs1_1897_);
lean_dec_ref(v_P_1896_);
lean_dec_ref(v_val_1895_);
lean_dec(v___x_1894_);
lean_dec_ref(v___x_1892_);
return v___x_1928_;
}
}
else
{
lean_dec(v_a_1921_);
lean_dec_ref(v___x_1918_);
lean_dec(v_a_1916_);
lean_dec_ref(v___x_1904_);
lean_dec(v_tail_1903_);
lean_dec_ref(v___x_1902_);
lean_dec(v___x_1900_);
lean_dec(v_indName_1899_);
lean_dec_ref(v_xs2_1898_);
lean_dec_ref(v_xs1_1897_);
lean_dec_ref(v_P_1896_);
lean_dec_ref(v_val_1895_);
lean_dec(v___x_1894_);
lean_dec_ref(v___x_1892_);
lean_dec_ref(v_t2_1891_);
return v___x_1925_;
}
}
else
{
lean_dec(v_a_1921_);
lean_dec_ref(v___x_1918_);
lean_dec(v_a_1916_);
lean_dec_ref(v___x_1904_);
lean_dec(v_tail_1903_);
lean_dec_ref(v___x_1902_);
lean_dec(v___x_1900_);
lean_dec(v_indName_1899_);
lean_dec_ref(v_xs2_1898_);
lean_dec_ref(v_xs1_1897_);
lean_dec_ref(v_P_1896_);
lean_dec_ref(v_val_1895_);
lean_dec(v___x_1894_);
lean_dec_ref(v___x_1892_);
lean_dec_ref(v_t2_1891_);
lean_dec_ref(v___f_1890_);
return v___x_1922_;
}
}
else
{
lean_dec_ref(v___x_1918_);
lean_dec(v_a_1916_);
lean_dec_ref(v___x_1904_);
lean_dec(v_tail_1903_);
lean_dec_ref(v___x_1902_);
lean_dec(v___x_1900_);
lean_dec(v_indName_1899_);
lean_dec_ref(v_xs2_1898_);
lean_dec_ref(v_xs1_1897_);
lean_dec_ref(v_P_1896_);
lean_dec_ref(v_val_1895_);
lean_dec(v___x_1894_);
lean_dec_ref(v___x_1892_);
lean_dec_ref(v_t2_1891_);
lean_dec_ref(v___f_1890_);
return v___x_1920_;
}
}
else
{
lean_dec_ref(v___x_1904_);
lean_dec(v_tail_1903_);
lean_dec_ref(v___x_1902_);
lean_dec(v___x_1900_);
lean_dec(v_indName_1899_);
lean_dec_ref(v_xs2_1898_);
lean_dec_ref(v_xs1_1897_);
lean_dec_ref(v_P_1896_);
lean_dec_ref(v_val_1895_);
lean_dec(v___x_1894_);
lean_dec_ref(v___x_1892_);
lean_dec_ref(v_t2_1891_);
lean_dec_ref(v___f_1890_);
lean_dec_ref(v_t1_1889_);
return v___x_1915_;
}
}
else
{
lean_dec_ref(v___x_1904_);
lean_dec(v_tail_1903_);
lean_dec_ref(v___x_1902_);
lean_dec(v___x_1900_);
lean_dec(v_indName_1899_);
lean_dec_ref(v_xs2_1898_);
lean_dec_ref(v_xs1_1897_);
lean_dec_ref(v_P_1896_);
lean_dec_ref(v_val_1895_);
lean_dec(v___x_1894_);
lean_dec_ref(v___x_1892_);
lean_dec_ref(v_t2_1891_);
lean_dec_ref(v___f_1890_);
lean_dec_ref(v_t1_1889_);
return v___x_1911_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__4___boxed(lean_object** _args){
lean_object* v_t1_1944_ = _args[0];
lean_object* v___f_1945_ = _args[1];
lean_object* v_t2_1946_ = _args[2];
lean_object* v___x_1947_ = _args[3];
lean_object* v_numIndices_1948_ = _args[4];
lean_object* v___x_1949_ = _args[5];
lean_object* v_val_1950_ = _args[6];
lean_object* v_P_1951_ = _args[7];
lean_object* v_xs1_1952_ = _args[8];
lean_object* v_xs2_1953_ = _args[9];
lean_object* v_indName_1954_ = _args[10];
lean_object* v___x_1955_ = _args[11];
lean_object* v___y_1956_ = _args[12];
lean_object* v___x_1957_ = _args[13];
lean_object* v_tail_1958_ = _args[14];
lean_object* v___x_1959_ = _args[15];
lean_object* v___x_1960_ = _args[16];
lean_object* v___y_1961_ = _args[17];
lean_object* v___y_1962_ = _args[18];
lean_object* v___y_1963_ = _args[19];
lean_object* v___y_1964_ = _args[20];
lean_object* v___y_1965_ = _args[21];
_start:
{
uint8_t v___y_17141__boxed_1966_; uint8_t v___x_17145__boxed_1967_; lean_object* v_res_1968_; 
v___y_17141__boxed_1966_ = lean_unbox(v___y_1956_);
v___x_17145__boxed_1967_ = lean_unbox(v___x_1960_);
v_res_1968_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__4(v_t1_1944_, v___f_1945_, v_t2_1946_, v___x_1947_, v_numIndices_1948_, v___x_1949_, v_val_1950_, v_P_1951_, v_xs1_1952_, v_xs2_1953_, v_indName_1954_, v___x_1955_, v___y_17141__boxed_1966_, v___x_1957_, v_tail_1958_, v___x_1959_, v___x_17145__boxed_1967_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v_numIndices_1948_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__5(lean_object* v___x_1969_, lean_object* v_xs1_1970_, lean_object* v_t1_1971_, lean_object* v___f_1972_, lean_object* v_numIndices_1973_, lean_object* v___x_1974_, lean_object* v_val_1975_, lean_object* v_P_1976_, lean_object* v_indName_1977_, lean_object* v___x_1978_, uint8_t v___y_1979_, lean_object* v_tail_1980_, lean_object* v___x_1981_, uint8_t v___x_1982_, lean_object* v_xs2_1983_, lean_object* v_t2_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___f_1993_; lean_object* v___x_1994_; 
lean_inc_ref(v___x_1969_);
v___x_1990_ = l_Lean_mkAppN(v___x_1969_, v_xs1_1970_);
v___x_1991_ = lean_box(v___y_1979_);
v___x_1992_ = lean_box(v___x_1982_);
lean_inc_ref(v_xs2_1983_);
v___f_1993_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__4___boxed), 22, 17);
lean_closure_set(v___f_1993_, 0, v_t1_1971_);
lean_closure_set(v___f_1993_, 1, v___f_1972_);
lean_closure_set(v___f_1993_, 2, v_t2_1984_);
lean_closure_set(v___f_1993_, 3, v___x_1990_);
lean_closure_set(v___f_1993_, 4, v_numIndices_1973_);
lean_closure_set(v___f_1993_, 5, v___x_1974_);
lean_closure_set(v___f_1993_, 6, v_val_1975_);
lean_closure_set(v___f_1993_, 7, v_P_1976_);
lean_closure_set(v___f_1993_, 8, v_xs1_1970_);
lean_closure_set(v___f_1993_, 9, v_xs2_1983_);
lean_closure_set(v___f_1993_, 10, v_indName_1977_);
lean_closure_set(v___f_1993_, 11, v___x_1978_);
lean_closure_set(v___f_1993_, 12, v___x_1991_);
lean_closure_set(v___f_1993_, 13, v___x_1969_);
lean_closure_set(v___f_1993_, 14, v_tail_1980_);
lean_closure_set(v___f_1993_, 15, v___x_1981_);
lean_closure_set(v___f_1993_, 16, v___x_1992_);
v___x_1994_ = l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__2___redArg(v_xs2_1983_, v___f_1993_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__5___boxed(lean_object** _args){
lean_object* v___x_1995_ = _args[0];
lean_object* v_xs1_1996_ = _args[1];
lean_object* v_t1_1997_ = _args[2];
lean_object* v___f_1998_ = _args[3];
lean_object* v_numIndices_1999_ = _args[4];
lean_object* v___x_2000_ = _args[5];
lean_object* v_val_2001_ = _args[6];
lean_object* v_P_2002_ = _args[7];
lean_object* v_indName_2003_ = _args[8];
lean_object* v___x_2004_ = _args[9];
lean_object* v___y_2005_ = _args[10];
lean_object* v_tail_2006_ = _args[11];
lean_object* v___x_2007_ = _args[12];
lean_object* v___x_2008_ = _args[13];
lean_object* v_xs2_2009_ = _args[14];
lean_object* v_t2_2010_ = _args[15];
lean_object* v___y_2011_ = _args[16];
lean_object* v___y_2012_ = _args[17];
lean_object* v___y_2013_ = _args[18];
lean_object* v___y_2014_ = _args[19];
lean_object* v___y_2015_ = _args[20];
_start:
{
uint8_t v___y_17258__boxed_2016_; uint8_t v___x_17261__boxed_2017_; lean_object* v_res_2018_; 
v___y_17258__boxed_2016_ = lean_unbox(v___y_2005_);
v___x_17261__boxed_2017_ = lean_unbox(v___x_2008_);
v_res_2018_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__5(v___x_1995_, v_xs1_1996_, v_t1_1997_, v___f_1998_, v_numIndices_1999_, v___x_2000_, v_val_2001_, v_P_2002_, v_indName_2003_, v___x_2004_, v___y_17258__boxed_2016_, v_tail_2006_, v___x_2007_, v___x_17261__boxed_2017_, v_xs2_2009_, v_t2_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__6(lean_object* v___x_2019_, lean_object* v___f_2020_, lean_object* v_numIndices_2021_, lean_object* v___x_2022_, lean_object* v_val_2023_, lean_object* v_P_2024_, lean_object* v_indName_2025_, lean_object* v___x_2026_, uint8_t v___y_2027_, lean_object* v_tail_2028_, lean_object* v___x_2029_, uint8_t v___x_2030_, lean_object* v_a_2031_, lean_object* v___x_2032_, lean_object* v_xs1_2033_, lean_object* v_t1_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___f_2042_; uint8_t v___x_2043_; lean_object* v___x_2044_; 
v___x_2040_ = lean_box(v___y_2027_);
v___x_2041_ = lean_box(v___x_2030_);
v___f_2042_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__5___boxed), 21, 14);
lean_closure_set(v___f_2042_, 0, v___x_2019_);
lean_closure_set(v___f_2042_, 1, v_xs1_2033_);
lean_closure_set(v___f_2042_, 2, v_t1_2034_);
lean_closure_set(v___f_2042_, 3, v___f_2020_);
lean_closure_set(v___f_2042_, 4, v_numIndices_2021_);
lean_closure_set(v___f_2042_, 5, v___x_2022_);
lean_closure_set(v___f_2042_, 6, v_val_2023_);
lean_closure_set(v___f_2042_, 7, v_P_2024_);
lean_closure_set(v___f_2042_, 8, v_indName_2025_);
lean_closure_set(v___f_2042_, 9, v___x_2026_);
lean_closure_set(v___f_2042_, 10, v___x_2040_);
lean_closure_set(v___f_2042_, 11, v_tail_2028_);
lean_closure_set(v___f_2042_, 12, v___x_2029_);
lean_closure_set(v___f_2042_, 13, v___x_2041_);
v___x_2043_ = 0;
v___x_2044_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(v_a_2031_, v___x_2032_, v___f_2042_, v___x_2043_, v___x_2043_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__6___boxed(lean_object** _args){
lean_object* v___x_2045_ = _args[0];
lean_object* v___f_2046_ = _args[1];
lean_object* v_numIndices_2047_ = _args[2];
lean_object* v___x_2048_ = _args[3];
lean_object* v_val_2049_ = _args[4];
lean_object* v_P_2050_ = _args[5];
lean_object* v_indName_2051_ = _args[6];
lean_object* v___x_2052_ = _args[7];
lean_object* v___y_2053_ = _args[8];
lean_object* v_tail_2054_ = _args[9];
lean_object* v___x_2055_ = _args[10];
lean_object* v___x_2056_ = _args[11];
lean_object* v_a_2057_ = _args[12];
lean_object* v___x_2058_ = _args[13];
lean_object* v_xs1_2059_ = _args[14];
lean_object* v_t1_2060_ = _args[15];
lean_object* v___y_2061_ = _args[16];
lean_object* v___y_2062_ = _args[17];
lean_object* v___y_2063_ = _args[18];
lean_object* v___y_2064_ = _args[19];
lean_object* v___y_2065_ = _args[20];
_start:
{
uint8_t v___y_17310__boxed_2066_; uint8_t v___x_17313__boxed_2067_; lean_object* v_res_2068_; 
v___y_17310__boxed_2066_ = lean_unbox(v___y_2053_);
v___x_17313__boxed_2067_ = lean_unbox(v___x_2056_);
v_res_2068_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__6(v___x_2045_, v___f_2046_, v_numIndices_2047_, v___x_2048_, v_val_2049_, v_P_2050_, v_indName_2051_, v___x_2052_, v___y_17310__boxed_2066_, v_tail_2054_, v___x_2055_, v___x_17313__boxed_2067_, v_a_2057_, v___x_2058_, v_xs1_2059_, v_t1_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__7(lean_object* v_val_2069_, lean_object* v___x_2070_, lean_object* v___f_2071_, lean_object* v___x_2072_, lean_object* v_indName_2073_, lean_object* v___x_2074_, uint8_t v___y_2075_, lean_object* v_tail_2076_, lean_object* v___x_2077_, uint8_t v___x_2078_, lean_object* v_a_2079_, lean_object* v_P_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
lean_object* v_numParams_2086_; lean_object* v_numIndices_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___f_2091_; uint8_t v___x_2092_; lean_object* v___x_2093_; 
v_numParams_2086_ = lean_ctor_get(v_val_2069_, 1);
v_numIndices_2087_ = lean_ctor_get(v_val_2069_, 2);
lean_inc(v_numIndices_2087_);
lean_inc(v_numParams_2086_);
v___x_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2088_, 0, v_numParams_2086_);
v___x_2089_ = lean_box(v___y_2075_);
v___x_2090_ = lean_box(v___x_2078_);
lean_inc_ref(v___x_2088_);
lean_inc_ref(v_a_2079_);
v___f_2091_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__6___boxed), 21, 14);
lean_closure_set(v___f_2091_, 0, v___x_2070_);
lean_closure_set(v___f_2091_, 1, v___f_2071_);
lean_closure_set(v___f_2091_, 2, v_numIndices_2087_);
lean_closure_set(v___f_2091_, 3, v___x_2072_);
lean_closure_set(v___f_2091_, 4, v_val_2069_);
lean_closure_set(v___f_2091_, 5, v_P_2080_);
lean_closure_set(v___f_2091_, 6, v_indName_2073_);
lean_closure_set(v___f_2091_, 7, v___x_2074_);
lean_closure_set(v___f_2091_, 8, v___x_2089_);
lean_closure_set(v___f_2091_, 9, v_tail_2076_);
lean_closure_set(v___f_2091_, 10, v___x_2077_);
lean_closure_set(v___f_2091_, 11, v___x_2090_);
lean_closure_set(v___f_2091_, 12, v_a_2079_);
lean_closure_set(v___f_2091_, 13, v___x_2088_);
v___x_2092_ = 0;
v___x_2093_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(v_a_2079_, v___x_2088_, v___f_2091_, v___x_2092_, v___x_2092_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__7___boxed(lean_object** _args){
lean_object* v_val_2094_ = _args[0];
lean_object* v___x_2095_ = _args[1];
lean_object* v___f_2096_ = _args[2];
lean_object* v___x_2097_ = _args[3];
lean_object* v_indName_2098_ = _args[4];
lean_object* v___x_2099_ = _args[5];
lean_object* v___y_2100_ = _args[6];
lean_object* v_tail_2101_ = _args[7];
lean_object* v___x_2102_ = _args[8];
lean_object* v___x_2103_ = _args[9];
lean_object* v_a_2104_ = _args[10];
lean_object* v_P_2105_ = _args[11];
lean_object* v___y_2106_ = _args[12];
lean_object* v___y_2107_ = _args[13];
lean_object* v___y_2108_ = _args[14];
lean_object* v___y_2109_ = _args[15];
lean_object* v___y_2110_ = _args[16];
_start:
{
uint8_t v___y_17368__boxed_2111_; uint8_t v___x_17371__boxed_2112_; lean_object* v_res_2113_; 
v___y_17368__boxed_2111_ = lean_unbox(v___y_2100_);
v___x_17371__boxed_2112_ = lean_unbox(v___x_2103_);
v_res_2113_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__7(v_val_2094_, v___x_2095_, v___f_2096_, v___x_2097_, v_indName_2098_, v___x_2099_, v___y_17368__boxed_2111_, v_tail_2101_, v___x_2102_, v___x_17371__boxed_2112_, v_a_2104_, v_P_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
return v_res_2113_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_2114_; 
v___x_2114_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2114_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__0);
v___x_2116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
return v___x_2116_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2117_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__1);
v___x_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
lean_ctor_set(v___x_2118_, 1, v___x_2117_);
return v___x_2118_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__1);
v___x_2120_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
lean_ctor_set(v___x_2120_, 1, v___x_2119_);
lean_ctor_set(v___x_2120_, 2, v___x_2119_);
lean_ctor_set(v___x_2120_, 3, v___x_2119_);
lean_ctor_set(v___x_2120_, 4, v___x_2119_);
lean_ctor_set(v___x_2120_, 5, v___x_2119_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg(lean_object* v_declName_2121_, uint8_t v_s_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v___x_2126_; lean_object* v_env_2127_; lean_object* v_nextMacroScope_2128_; lean_object* v_ngen_2129_; lean_object* v_auxDeclNGen_2130_; lean_object* v_traceState_2131_; lean_object* v_messages_2132_; lean_object* v_infoState_2133_; lean_object* v_snapshotTasks_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2163_; 
v___x_2126_ = lean_st_ref_take(v___y_2124_);
v_env_2127_ = lean_ctor_get(v___x_2126_, 0);
v_nextMacroScope_2128_ = lean_ctor_get(v___x_2126_, 1);
v_ngen_2129_ = lean_ctor_get(v___x_2126_, 2);
v_auxDeclNGen_2130_ = lean_ctor_get(v___x_2126_, 3);
v_traceState_2131_ = lean_ctor_get(v___x_2126_, 4);
v_messages_2132_ = lean_ctor_get(v___x_2126_, 6);
v_infoState_2133_ = lean_ctor_get(v___x_2126_, 7);
v_snapshotTasks_2134_ = lean_ctor_get(v___x_2126_, 8);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2163_ == 0)
{
lean_object* v_unused_2164_; 
v_unused_2164_ = lean_ctor_get(v___x_2126_, 5);
lean_dec(v_unused_2164_);
v___x_2136_ = v___x_2126_;
v_isShared_2137_ = v_isSharedCheck_2163_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_snapshotTasks_2134_);
lean_inc(v_infoState_2133_);
lean_inc(v_messages_2132_);
lean_inc(v_traceState_2131_);
lean_inc(v_auxDeclNGen_2130_);
lean_inc(v_ngen_2129_);
lean_inc(v_nextMacroScope_2128_);
lean_inc(v_env_2127_);
lean_dec(v___x_2126_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2163_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
uint8_t v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2143_; 
v___x_2138_ = 0;
v___x_2139_ = lean_box(0);
v___x_2140_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_2127_, v_declName_2121_, v_s_2122_, v___x_2138_, v___x_2139_);
v___x_2141_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 5, v___x_2141_);
lean_ctor_set(v___x_2136_, 0, v___x_2140_);
v___x_2143_ = v___x_2136_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2140_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v_nextMacroScope_2128_);
lean_ctor_set(v_reuseFailAlloc_2162_, 2, v_ngen_2129_);
lean_ctor_set(v_reuseFailAlloc_2162_, 3, v_auxDeclNGen_2130_);
lean_ctor_set(v_reuseFailAlloc_2162_, 4, v_traceState_2131_);
lean_ctor_set(v_reuseFailAlloc_2162_, 5, v___x_2141_);
lean_ctor_set(v_reuseFailAlloc_2162_, 6, v_messages_2132_);
lean_ctor_set(v_reuseFailAlloc_2162_, 7, v_infoState_2133_);
lean_ctor_set(v_reuseFailAlloc_2162_, 8, v_snapshotTasks_2134_);
v___x_2143_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v_mctx_2146_; lean_object* v_zetaDeltaFVarIds_2147_; lean_object* v_postponed_2148_; lean_object* v_diag_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2160_; 
v___x_2144_ = lean_st_ref_put(v___y_2124_, v___x_2143_);
v___x_2145_ = lean_st_ref_take(v___y_2123_);
v_mctx_2146_ = lean_ctor_get(v___x_2145_, 0);
v_zetaDeltaFVarIds_2147_ = lean_ctor_get(v___x_2145_, 2);
v_postponed_2148_ = lean_ctor_get(v___x_2145_, 3);
v_diag_2149_ = lean_ctor_get(v___x_2145_, 4);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2160_ == 0)
{
lean_object* v_unused_2161_; 
v_unused_2161_ = lean_ctor_get(v___x_2145_, 1);
lean_dec(v_unused_2161_);
v___x_2151_ = v___x_2145_;
v_isShared_2152_ = v_isSharedCheck_2160_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_diag_2149_);
lean_inc(v_postponed_2148_);
lean_inc(v_zetaDeltaFVarIds_2147_);
lean_inc(v_mctx_2146_);
lean_dec(v___x_2145_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2160_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2153_; lean_object* v___x_2155_; 
v___x_2153_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3);
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 1, v___x_2153_);
v___x_2155_ = v___x_2151_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_mctx_2146_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v___x_2153_);
lean_ctor_set(v_reuseFailAlloc_2159_, 2, v_zetaDeltaFVarIds_2147_);
lean_ctor_set(v_reuseFailAlloc_2159_, 3, v_postponed_2148_);
lean_ctor_set(v_reuseFailAlloc_2159_, 4, v_diag_2149_);
v___x_2155_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2156_ = lean_st_ref_put(v___y_2123_, v___x_2155_);
v___x_2157_ = lean_box(0);
v___x_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
return v___x_2158_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___boxed(lean_object* v_declName_2165_, lean_object* v_s_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
uint8_t v_s_boxed_2170_; lean_object* v_res_2171_; 
v_s_boxed_2170_ = lean_unbox(v_s_2166_);
v_res_2171_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg(v_declName_2165_, v_s_boxed_2170_, v___y_2167_, v___y_2168_);
lean_dec(v___y_2168_);
lean_dec(v___y_2167_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7(lean_object* v_declName_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
uint8_t v___x_2178_; lean_object* v___x_2179_; 
v___x_2178_ = 0;
v___x_2179_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg(v_declName_2172_, v___x_2178_, v___y_2174_, v___y_2176_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7___boxed(lean_object* v_declName_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7(v_declName_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__2(lean_object* v_a_2187_, lean_object* v_a_2188_){
_start:
{
if (lean_obj_tag(v_a_2187_) == 0)
{
lean_object* v___x_2189_; 
v___x_2189_ = l_List_reverse___redArg(v_a_2188_);
return v___x_2189_;
}
else
{
lean_object* v_head_2190_; lean_object* v_tail_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2200_; 
v_head_2190_ = lean_ctor_get(v_a_2187_, 0);
v_tail_2191_ = lean_ctor_get(v_a_2187_, 1);
v_isSharedCheck_2200_ = !lean_is_exclusive(v_a_2187_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2193_ = v_a_2187_;
v_isShared_2194_ = v_isSharedCheck_2200_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_tail_2191_);
lean_inc(v_head_2190_);
lean_dec(v_a_2187_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2200_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2195_; lean_object* v___x_2197_; 
v___x_2195_ = l_Lean_mkLevelParam(v_head_2190_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 1, v_a_2188_);
lean_ctor_set(v___x_2193_, 0, v___x_2195_);
v___x_2197_ = v___x_2193_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2195_);
lean_ctor_set(v_reuseFailAlloc_2199_, 1, v_a_2188_);
v___x_2197_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
v_a_2187_ = v_tail_2191_;
v_a_2188_ = v___x_2197_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_2201_; 
v___x_2201_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2201_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2202_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
return v___x_2203_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2204_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_2205_ = lean_unsigned_to_nat(0u);
v___x_2206_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
lean_ctor_set(v___x_2206_, 1, v___x_2205_);
lean_ctor_set(v___x_2206_, 2, v___x_2205_);
lean_ctor_set(v___x_2206_, 3, v___x_2205_);
lean_ctor_set(v___x_2206_, 4, v___x_2204_);
lean_ctor_set(v___x_2206_, 5, v___x_2204_);
lean_ctor_set(v___x_2206_, 6, v___x_2204_);
lean_ctor_set(v___x_2206_, 7, v___x_2204_);
lean_ctor_set(v___x_2206_, 8, v___x_2204_);
lean_ctor_set(v___x_2206_, 9, v___x_2204_);
lean_ctor_set(v___x_2206_, 10, v___x_2204_);
return v___x_2206_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2207_ = lean_unsigned_to_nat(32u);
v___x_2208_ = lean_mk_empty_array_with_capacity(v___x_2207_);
v___x_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
return v___x_2209_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4(void){
_start:
{
size_t v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2210_ = ((size_t)5ULL);
v___x_2211_ = lean_unsigned_to_nat(0u);
v___x_2212_ = lean_unsigned_to_nat(32u);
v___x_2213_ = lean_mk_empty_array_with_capacity(v___x_2212_);
v___x_2214_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_2215_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
lean_ctor_set(v___x_2215_, 1, v___x_2213_);
lean_ctor_set(v___x_2215_, 2, v___x_2211_);
lean_ctor_set(v___x_2215_, 3, v___x_2211_);
lean_ctor_set_usize(v___x_2215_, 4, v___x_2210_);
return v___x_2215_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2216_ = lean_box(1);
v___x_2217_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_2218_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_2219_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2218_);
lean_ctor_set(v___x_2219_, 1, v___x_2217_);
lean_ctor_set(v___x_2219_, 2, v___x_2216_);
return v___x_2219_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2221_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6));
v___x_2222_ = l_Lean_stringToMessageData(v___x_2221_);
return v___x_2222_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2224_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8));
v___x_2225_ = l_Lean_stringToMessageData(v___x_2224_);
return v___x_2225_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10));
v___x_2228_ = l_Lean_stringToMessageData(v___x_2227_);
return v___x_2228_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12));
v___x_2231_ = l_Lean_stringToMessageData(v___x_2230_);
return v___x_2231_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14));
v___x_2234_ = l_Lean_stringToMessageData(v___x_2233_);
return v___x_2234_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2236_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16));
v___x_2237_ = l_Lean_stringToMessageData(v___x_2236_);
return v___x_2237_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19(void){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2239_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__18));
v___x_2240_ = l_Lean_stringToMessageData(v___x_2239_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_2241_, lean_object* v_declHint_2242_, lean_object* v___y_2243_){
_start:
{
lean_object* v___x_2245_; lean_object* v_env_2246_; uint8_t v___x_2247_; 
v___x_2245_ = lean_st_ref_get(v___y_2243_);
v_env_2246_ = lean_ctor_get(v___x_2245_, 0);
lean_inc_ref(v_env_2246_);
lean_dec(v___x_2245_);
v___x_2247_ = l_Lean_Name_isAnonymous(v_declHint_2242_);
if (v___x_2247_ == 0)
{
uint8_t v_isExporting_2248_; 
v_isExporting_2248_ = lean_ctor_get_uint8(v_env_2246_, sizeof(void*)*8);
if (v_isExporting_2248_ == 0)
{
lean_object* v___x_2249_; 
lean_dec_ref(v_env_2246_);
lean_dec(v_declHint_2242_);
v___x_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2249_, 0, v_msg_2241_);
return v___x_2249_;
}
else
{
lean_object* v___x_2250_; uint8_t v___x_2251_; 
lean_inc_ref(v_env_2246_);
v___x_2250_ = l_Lean_Environment_setExporting(v_env_2246_, v___x_2247_);
lean_inc(v_declHint_2242_);
lean_inc_ref(v___x_2250_);
v___x_2251_ = l_Lean_Environment_contains(v___x_2250_, v_declHint_2242_, v_isExporting_2248_);
if (v___x_2251_ == 0)
{
lean_object* v___x_2252_; 
lean_dec_ref(v___x_2250_);
lean_dec_ref(v_env_2246_);
lean_dec(v_declHint_2242_);
v___x_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2252_, 0, v_msg_2241_);
return v___x_2252_;
}
else
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v_c_2258_; lean_object* v___x_2259_; 
v___x_2253_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_2254_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_2255_ = l_Lean_Options_empty;
v___x_2256_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2250_);
lean_ctor_set(v___x_2256_, 1, v___x_2253_);
lean_ctor_set(v___x_2256_, 2, v___x_2254_);
lean_ctor_set(v___x_2256_, 3, v___x_2255_);
lean_inc(v_declHint_2242_);
v___x_2257_ = l_Lean_MessageData_ofConstName(v_declHint_2242_, v___x_2247_);
v_c_2258_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2258_, 0, v___x_2256_);
lean_ctor_set(v_c_2258_, 1, v___x_2257_);
v___x_2259_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2246_, v_declHint_2242_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
lean_dec_ref(v_env_2246_);
lean_dec(v_declHint_2242_);
v___x_2260_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_2261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2260_);
lean_ctor_set(v___x_2261_, 1, v_c_2258_);
v___x_2262_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9);
v___x_2263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2261_);
lean_ctor_set(v___x_2263_, 1, v___x_2262_);
v___x_2264_ = l_Lean_MessageData_note(v___x_2263_);
v___x_2265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2265_, 0, v_msg_2241_);
lean_ctor_set(v___x_2265_, 1, v___x_2264_);
v___x_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2265_);
return v___x_2266_;
}
else
{
lean_object* v_val_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2302_; 
v_val_2267_ = lean_ctor_get(v___x_2259_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2269_ = v___x_2259_;
v_isShared_2270_ = v_isSharedCheck_2302_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_val_2267_);
lean_dec(v___x_2259_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2302_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v_mod_2274_; uint8_t v___x_2275_; 
v___x_2271_ = lean_box(0);
v___x_2272_ = l_Lean_Environment_header(v_env_2246_);
lean_dec_ref(v_env_2246_);
v___x_2273_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2272_);
v_mod_2274_ = lean_array_get(v___x_2271_, v___x_2273_, v_val_2267_);
lean_dec(v_val_2267_);
lean_dec_ref(v___x_2273_);
v___x_2275_ = l_Lean_isPrivateName(v_declHint_2242_);
lean_dec(v_declHint_2242_);
if (v___x_2275_ == 0)
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2287_; 
v___x_2276_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11);
v___x_2277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2276_);
lean_ctor_set(v___x_2277_, 1, v_c_2258_);
v___x_2278_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13);
v___x_2279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2277_);
lean_ctor_set(v___x_2279_, 1, v___x_2278_);
v___x_2280_ = l_Lean_MessageData_ofName(v_mod_2274_);
v___x_2281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2279_);
lean_ctor_set(v___x_2281_, 1, v___x_2280_);
v___x_2282_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15);
v___x_2283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2281_);
lean_ctor_set(v___x_2283_, 1, v___x_2282_);
v___x_2284_ = l_Lean_MessageData_note(v___x_2283_);
v___x_2285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2285_, 0, v_msg_2241_);
lean_ctor_set(v___x_2285_, 1, v___x_2284_);
if (v_isShared_2270_ == 0)
{
lean_ctor_set_tag(v___x_2269_, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2285_);
v___x_2287_ = v___x_2269_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2285_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
else
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2300_; 
v___x_2289_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_2290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2289_);
lean_ctor_set(v___x_2290_, 1, v_c_2258_);
v___x_2291_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17);
v___x_2292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2290_);
lean_ctor_set(v___x_2292_, 1, v___x_2291_);
v___x_2293_ = l_Lean_MessageData_ofName(v_mod_2274_);
v___x_2294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2292_);
lean_ctor_set(v___x_2294_, 1, v___x_2293_);
v___x_2295_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19);
v___x_2296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2294_);
lean_ctor_set(v___x_2296_, 1, v___x_2295_);
v___x_2297_ = l_Lean_MessageData_note(v___x_2296_);
v___x_2298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2298_, 0, v_msg_2241_);
lean_ctor_set(v___x_2298_, 1, v___x_2297_);
if (v_isShared_2270_ == 0)
{
lean_ctor_set_tag(v___x_2269_, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2298_);
v___x_2300_ = v___x_2269_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2298_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2303_; 
lean_dec_ref(v_env_2246_);
lean_dec(v_declHint_2242_);
v___x_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2303_, 0, v_msg_2241_);
return v___x_2303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_2304_, lean_object* v_declHint_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_2304_, v_declHint_2305_, v___y_2306_);
lean_dec(v___y_2306_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12(lean_object* v_msg_2309_, lean_object* v_declHint_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v___x_2316_; lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2326_; 
v___x_2316_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_2309_, v_declHint_2310_, v___y_2314_);
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2319_ = v___x_2316_;
v_isShared_2320_ = v_isSharedCheck_2326_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2316_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2326_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2324_; 
v___x_2321_ = l_Lean_unknownIdentifierMessageTag;
v___x_2322_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2321_);
lean_ctor_set(v___x_2322_, 1, v_a_2317_);
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 0, v___x_2322_);
v___x_2324_ = v___x_2319_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v___x_2322_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12___boxed(lean_object* v_msg_2327_, lean_object* v_declHint_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_2327_, v_declHint_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(lean_object* v_ref_2335_, lean_object* v_msg_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v_fileName_2342_; lean_object* v_fileMap_2343_; lean_object* v_options_2344_; lean_object* v_currRecDepth_2345_; lean_object* v_maxRecDepth_2346_; lean_object* v_ref_2347_; lean_object* v_currNamespace_2348_; lean_object* v_openDecls_2349_; lean_object* v_initHeartbeats_2350_; lean_object* v_maxHeartbeats_2351_; lean_object* v_quotContext_2352_; lean_object* v_currMacroScope_2353_; uint8_t v_diag_2354_; lean_object* v_cancelTk_x3f_2355_; uint8_t v_suppressElabErrors_2356_; lean_object* v_inheritedTraceOptions_2357_; lean_object* v_ref_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v_fileName_2342_ = lean_ctor_get(v___y_2339_, 0);
v_fileMap_2343_ = lean_ctor_get(v___y_2339_, 1);
v_options_2344_ = lean_ctor_get(v___y_2339_, 2);
v_currRecDepth_2345_ = lean_ctor_get(v___y_2339_, 3);
v_maxRecDepth_2346_ = lean_ctor_get(v___y_2339_, 4);
v_ref_2347_ = lean_ctor_get(v___y_2339_, 5);
v_currNamespace_2348_ = lean_ctor_get(v___y_2339_, 6);
v_openDecls_2349_ = lean_ctor_get(v___y_2339_, 7);
v_initHeartbeats_2350_ = lean_ctor_get(v___y_2339_, 8);
v_maxHeartbeats_2351_ = lean_ctor_get(v___y_2339_, 9);
v_quotContext_2352_ = lean_ctor_get(v___y_2339_, 10);
v_currMacroScope_2353_ = lean_ctor_get(v___y_2339_, 11);
v_diag_2354_ = lean_ctor_get_uint8(v___y_2339_, sizeof(void*)*14);
v_cancelTk_x3f_2355_ = lean_ctor_get(v___y_2339_, 12);
v_suppressElabErrors_2356_ = lean_ctor_get_uint8(v___y_2339_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2357_ = lean_ctor_get(v___y_2339_, 13);
v_ref_2358_ = l_Lean_replaceRef(v_ref_2335_, v_ref_2347_);
lean_inc_ref(v_inheritedTraceOptions_2357_);
lean_inc(v_cancelTk_x3f_2355_);
lean_inc(v_currMacroScope_2353_);
lean_inc(v_quotContext_2352_);
lean_inc(v_maxHeartbeats_2351_);
lean_inc(v_initHeartbeats_2350_);
lean_inc(v_openDecls_2349_);
lean_inc(v_currNamespace_2348_);
lean_inc(v_maxRecDepth_2346_);
lean_inc(v_currRecDepth_2345_);
lean_inc_ref(v_options_2344_);
lean_inc_ref(v_fileMap_2343_);
lean_inc_ref(v_fileName_2342_);
v___x_2359_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2359_, 0, v_fileName_2342_);
lean_ctor_set(v___x_2359_, 1, v_fileMap_2343_);
lean_ctor_set(v___x_2359_, 2, v_options_2344_);
lean_ctor_set(v___x_2359_, 3, v_currRecDepth_2345_);
lean_ctor_set(v___x_2359_, 4, v_maxRecDepth_2346_);
lean_ctor_set(v___x_2359_, 5, v_ref_2358_);
lean_ctor_set(v___x_2359_, 6, v_currNamespace_2348_);
lean_ctor_set(v___x_2359_, 7, v_openDecls_2349_);
lean_ctor_set(v___x_2359_, 8, v_initHeartbeats_2350_);
lean_ctor_set(v___x_2359_, 9, v_maxHeartbeats_2351_);
lean_ctor_set(v___x_2359_, 10, v_quotContext_2352_);
lean_ctor_set(v___x_2359_, 11, v_currMacroScope_2353_);
lean_ctor_set(v___x_2359_, 12, v_cancelTk_x3f_2355_);
lean_ctor_set(v___x_2359_, 13, v_inheritedTraceOptions_2357_);
lean_ctor_set_uint8(v___x_2359_, sizeof(void*)*14, v_diag_2354_);
lean_ctor_set_uint8(v___x_2359_, sizeof(void*)*14 + 1, v_suppressElabErrors_2356_);
v___x_2360_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0___redArg(v_msg_2336_, v___y_2337_, v___y_2338_, v___x_2359_, v___y_2340_);
lean_dec_ref_known(v___x_2359_, 14);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg___boxed(lean_object* v_ref_2361_, lean_object* v_msg_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_2361_, v_msg_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v_ref_2361_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11___redArg(lean_object* v_ref_2369_, lean_object* v_msg_2370_, lean_object* v_declHint_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v___x_2377_; lean_object* v_a_2378_; lean_object* v___x_2379_; 
v___x_2377_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_2370_, v_declHint_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
v_a_2378_ = lean_ctor_get(v___x_2377_, 0);
lean_inc(v_a_2378_);
lean_dec_ref(v___x_2377_);
v___x_2379_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_2369_, v_a_2378_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11___redArg___boxed(lean_object* v_ref_2380_, lean_object* v_msg_2381_, lean_object* v_declHint_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_2380_, v_msg_2381_, v_declHint_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v_ref_2380_);
return v_res_2388_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_2391_ = l_Lean_stringToMessageData(v___x_2390_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_2392_, lean_object* v_constName_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
lean_object* v___x_2399_; uint8_t v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2399_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_2400_ = 0;
lean_inc(v_constName_2393_);
v___x_2401_ = l_Lean_MessageData_ofConstName(v_constName_2393_, v___x_2400_);
v___x_2402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2399_);
lean_ctor_set(v___x_2402_, 1, v___x_2401_);
v___x_2403_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__1);
v___x_2404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2402_);
lean_ctor_set(v___x_2404_, 1, v___x_2403_);
v___x_2405_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_2392_, v___x_2404_, v_constName_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_2406_, lean_object* v_constName_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg(v_ref_2406_, v_constName_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec(v_ref_2406_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0___redArg(lean_object* v_constName_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v_ref_2420_; lean_object* v___x_2421_; 
v_ref_2420_ = lean_ctor_get(v___y_2417_, 5);
v___x_2421_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg(v_ref_2420_, v_constName_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0___redArg(v_constName_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__1(lean_object* v_constName_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v___x_2435_; lean_object* v_env_2436_; uint8_t v___x_2437_; lean_object* v___x_2438_; 
v___x_2435_ = lean_st_ref_get(v___y_2433_);
v_env_2436_ = lean_ctor_get(v___x_2435_, 0);
lean_inc_ref(v_env_2436_);
lean_dec(v___x_2435_);
v___x_2437_ = 0;
lean_inc(v_constName_2429_);
v___x_2438_ = l_Lean_Environment_findConstVal_x3f(v_env_2436_, v_constName_2429_, v___x_2437_);
if (lean_obj_tag(v___x_2438_) == 0)
{
lean_object* v___x_2439_; 
v___x_2439_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0___redArg(v_constName_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_);
return v___x_2439_;
}
else
{
lean_object* v_val_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
lean_dec(v_constName_2429_);
v_val_2440_ = lean_ctor_get(v___x_2438_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v___x_2438_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_val_2440_);
lean_dec(v___x_2438_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
lean_ctor_set_tag(v___x_2442_, 0);
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_val_2440_);
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
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__1___boxed(lean_object* v_constName_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__1(v_constName_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(lean_object* v_constName_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_){
_start:
{
lean_object* v___x_2461_; lean_object* v_env_2462_; uint8_t v___x_2463_; lean_object* v___x_2464_; 
v___x_2461_ = lean_st_ref_get(v___y_2459_);
v_env_2462_ = lean_ctor_get(v___x_2461_, 0);
lean_inc_ref(v_env_2462_);
lean_dec(v___x_2461_);
v___x_2463_ = 0;
lean_inc(v_constName_2455_);
v___x_2464_ = l_Lean_Environment_find_x3f(v_env_2462_, v_constName_2455_, v___x_2463_);
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_object* v___x_2465_; 
v___x_2465_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0___redArg(v_constName_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
return v___x_2465_;
}
else
{
lean_object* v_val_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
lean_dec(v_constName_2455_);
v_val_2466_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2468_ = v___x_2464_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_val_2466_);
lean_dec(v___x_2464_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
lean_ctor_set_tag(v___x_2468_, 0);
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_val_2466_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0___boxed(lean_object* v_constName_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(v_constName_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
return v_res_2480_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__5(void){
_start:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2487_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__4));
v___x_2488_ = lean_unsigned_to_nat(58u);
v___x_2489_ = lean_unsigned_to_nat(81u);
v___x_2490_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__3));
v___x_2491_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__2));
v___x_2492_ = l_mkPanicMessageWithDecl(v___x_2491_, v___x_2490_, v___x_2489_, v___x_2488_, v___x_2487_);
return v___x_2492_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__6(void){
_start:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2493_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__6));
v___x_2494_ = lean_unsigned_to_nat(60u);
v___x_2495_ = lean_unsigned_to_nat(74u);
v___x_2496_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__3));
v___x_2497_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__2));
v___x_2498_ = l_mkPanicMessageWithDecl(v___x_2497_, v___x_2496_, v___x_2495_, v___x_2494_, v___x_2493_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType(lean_object* v_indName_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_){
_start:
{
lean_object* v_declName_2505_; lean_object* v___x_2506_; 
lean_inc_n(v_indName_2499_, 2);
v_declName_2505_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionTypeName(v_indName_2499_);
v___x_2506_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(v_indName_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_);
if (lean_obj_tag(v___x_2506_) == 0)
{
lean_object* v_a_2507_; 
v_a_2507_ = lean_ctor_get(v___x_2506_, 0);
lean_inc(v_a_2507_);
lean_dec_ref_known(v___x_2506_, 1);
if (lean_obj_tag(v_a_2507_) == 5)
{
lean_object* v_val_2508_; lean_object* v_options_2509_; lean_object* v___x_2510_; uint8_t v___x_2511_; lean_object* v___x_2512_; lean_object* v_a_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; uint8_t v___y_2517_; uint8_t v___x_2663_; 
v_val_2508_ = lean_ctor_get(v_a_2507_, 0);
lean_inc_ref(v_val_2508_);
lean_dec_ref_known(v_a_2507_, 1);
v_options_2509_ = lean_ctor_get(v_a_2502_, 2);
lean_inc(v_indName_2499_);
v___x_2510_ = l_Lean_mkCtorElimName(v_indName_2499_);
v___x_2511_ = 1;
v___x_2512_ = l_Lean_hasConst___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__1___redArg(v___x_2510_, v___x_2511_, v_a_2503_);
v_a_2513_ = lean_ctor_get(v___x_2512_, 0);
lean_inc(v_a_2513_);
lean_dec_ref(v___x_2512_);
v___x_2514_ = lean_unsigned_to_nat(2u);
v___x_2515_ = l_Lean_InductiveVal_numCtors(v_val_2508_);
v___x_2663_ = lean_nat_dec_lt(v___x_2514_, v___x_2515_);
if (v___x_2663_ == 0)
{
lean_dec(v_a_2513_);
v___y_2517_ = v___x_2663_;
goto v___jp_2516_;
}
else
{
lean_object* v___x_2664_; uint8_t v___x_2665_; 
v___x_2664_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_backward_linearNoConfusionType;
v___x_2665_ = l_Lean_Option_get___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__0(v_options_2509_, v___x_2664_);
if (v___x_2665_ == 0)
{
lean_dec(v_a_2513_);
v___y_2517_ = v___x_2665_;
goto v___jp_2516_;
}
else
{
uint8_t v___x_2666_; 
v___x_2666_ = lean_unbox(v_a_2513_);
lean_dec(v_a_2513_);
v___y_2517_ = v___x_2666_;
goto v___jp_2516_;
}
}
v___jp_2516_:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; 
lean_inc(v_indName_2499_);
v___x_2518_ = l_Lean_mkCasesOnName(v_indName_2499_);
lean_inc(v___x_2518_);
v___x_2519_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__1(v___x_2518_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v_a_2520_; lean_object* v_levelParams_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
v_a_2520_ = lean_ctor_get(v___x_2519_, 0);
lean_inc(v_a_2520_);
lean_dec_ref_known(v___x_2519_, 1);
v_levelParams_2521_ = lean_ctor_get(v_a_2520_, 1);
lean_inc_n(v_levelParams_2521_, 2);
lean_dec(v_a_2520_);
v___x_2522_ = lean_box(0);
v___x_2523_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__2(v_levelParams_2521_, v___x_2522_);
if (lean_obj_tag(v___x_2523_) == 1)
{
lean_object* v_head_2524_; lean_object* v_tail_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2652_; 
v_head_2524_ = lean_ctor_get(v___x_2523_, 0);
v_tail_2525_ = lean_ctor_get(v___x_2523_, 1);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2527_ = v___x_2523_;
v_isShared_2528_ = v_isSharedCheck_2652_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_tail_2525_);
lean_inc(v_head_2524_);
lean_dec(v___x_2523_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2652_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2529_; lean_object* v___x_2531_; 
lean_inc(v_head_2524_);
v___x_2529_ = l_Lean_Level_succ___override(v_head_2524_);
lean_inc(v_tail_2525_);
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 0, v___x_2529_);
v___x_2531_ = v___x_2527_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2529_);
lean_ctor_set(v_reuseFailAlloc_2651_, 1, v_tail_2525_);
v___x_2531_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; 
lean_inc_ref(v___x_2531_);
v___x_2532_ = l_Lean_mkConst(v___x_2518_, v___x_2531_);
lean_inc(v_a_2503_);
lean_inc_ref(v_a_2502_);
lean_inc(v_a_2501_);
lean_inc_ref(v_a_2500_);
lean_inc_ref(v___x_2532_);
v___x_2533_ = lean_infer_type(v___x_2532_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v_a_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___f_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___f_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
v_a_2534_ = lean_ctor_get(v___x_2533_, 0);
lean_inc(v_a_2534_);
lean_dec_ref_known(v___x_2533_, 1);
v___x_2535_ = l_Lean_mkSort(v_head_2524_);
v___x_2536_ = lean_box(v___x_2511_);
lean_inc_ref_n(v___x_2535_, 2);
v___f_2537_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2537_, 0, v___x_2535_);
lean_closure_set(v___f_2537_, 1, v___x_2536_);
v___x_2538_ = lean_box(v___y_2517_);
v___x_2539_ = lean_box(v___x_2511_);
v___f_2540_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__7___boxed), 17, 11);
lean_closure_set(v___f_2540_, 0, v_val_2508_);
lean_closure_set(v___f_2540_, 1, v___x_2532_);
lean_closure_set(v___f_2540_, 2, v___f_2537_);
lean_closure_set(v___f_2540_, 3, v___x_2515_);
lean_closure_set(v___f_2540_, 4, v_indName_2499_);
lean_closure_set(v___f_2540_, 5, v___x_2531_);
lean_closure_set(v___f_2540_, 6, v___x_2538_);
lean_closure_set(v___f_2540_, 7, v_tail_2525_);
lean_closure_set(v___f_2540_, 8, v___x_2535_);
lean_closure_set(v___f_2540_, 9, v___x_2539_);
lean_closure_set(v___f_2540_, 10, v_a_2534_);
v___x_2541_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__1));
v___x_2542_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_2541_, v___x_2535_, v___f_2540_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v_a_2543_; lean_object* v___x_2544_; 
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
lean_inc_n(v_a_2543_, 2);
lean_dec_ref_known(v___x_2542_, 1);
lean_inc(v_a_2503_);
lean_inc_ref(v_a_2502_);
lean_inc(v_a_2501_);
lean_inc_ref(v_a_2500_);
v___x_2544_ = lean_infer_type(v_a_2543_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v_a_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2626_; 
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc(v_a_2545_);
lean_dec_ref_known(v___x_2544_, 1);
v___x_2546_ = lean_box(1);
lean_inc(v_declName_2505_);
v___x_2547_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__6___redArg(v_declName_2505_, v_levelParams_2521_, v_a_2545_, v_a_2543_, v___x_2546_, v_a_2503_);
v_a_2548_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2550_ = v___x_2547_;
v_isShared_2551_ = v_isSharedCheck_2626_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v___x_2547_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2626_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2553_; 
if (v_isShared_2551_ == 0)
{
lean_ctor_set_tag(v___x_2550_, 1);
v___x_2553_ = v___x_2550_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2548_);
v___x_2553_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
uint8_t v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = 0;
v___x_2555_ = l_Lean_addDecl(v___x_2553_, v___x_2554_, v_a_2502_, v_a_2503_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v___x_2556_; lean_object* v_env_2557_; lean_object* v_nextMacroScope_2558_; lean_object* v_ngen_2559_; lean_object* v_auxDeclNGen_2560_; lean_object* v_traceState_2561_; lean_object* v_messages_2562_; lean_object* v_infoState_2563_; lean_object* v_snapshotTasks_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2623_; 
lean_dec_ref_known(v___x_2555_, 1);
v___x_2556_ = lean_st_ref_take(v_a_2503_);
v_env_2557_ = lean_ctor_get(v___x_2556_, 0);
v_nextMacroScope_2558_ = lean_ctor_get(v___x_2556_, 1);
v_ngen_2559_ = lean_ctor_get(v___x_2556_, 2);
v_auxDeclNGen_2560_ = lean_ctor_get(v___x_2556_, 3);
v_traceState_2561_ = lean_ctor_get(v___x_2556_, 4);
v_messages_2562_ = lean_ctor_get(v___x_2556_, 6);
v_infoState_2563_ = lean_ctor_get(v___x_2556_, 7);
v_snapshotTasks_2564_ = lean_ctor_get(v___x_2556_, 8);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2623_ == 0)
{
lean_object* v_unused_2624_; 
v_unused_2624_ = lean_ctor_get(v___x_2556_, 5);
lean_dec(v_unused_2624_);
v___x_2566_ = v___x_2556_;
v_isShared_2567_ = v_isSharedCheck_2623_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_snapshotTasks_2564_);
lean_inc(v_infoState_2563_);
lean_inc(v_messages_2562_);
lean_inc(v_traceState_2561_);
lean_inc(v_auxDeclNGen_2560_);
lean_inc(v_ngen_2559_);
lean_inc(v_nextMacroScope_2558_);
lean_inc(v_env_2557_);
lean_dec(v___x_2556_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2623_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2571_; 
lean_inc(v_declName_2505_);
v___x_2568_ = l_Lean_Meta_addToCompletionBlackList(v_env_2557_, v_declName_2505_);
v___x_2569_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2);
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 5, v___x_2569_);
lean_ctor_set(v___x_2566_, 0, v___x_2568_);
v___x_2571_ = v___x_2566_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v___x_2568_);
lean_ctor_set(v_reuseFailAlloc_2622_, 1, v_nextMacroScope_2558_);
lean_ctor_set(v_reuseFailAlloc_2622_, 2, v_ngen_2559_);
lean_ctor_set(v_reuseFailAlloc_2622_, 3, v_auxDeclNGen_2560_);
lean_ctor_set(v_reuseFailAlloc_2622_, 4, v_traceState_2561_);
lean_ctor_set(v_reuseFailAlloc_2622_, 5, v___x_2569_);
lean_ctor_set(v_reuseFailAlloc_2622_, 6, v_messages_2562_);
lean_ctor_set(v_reuseFailAlloc_2622_, 7, v_infoState_2563_);
lean_ctor_set(v_reuseFailAlloc_2622_, 8, v_snapshotTasks_2564_);
v___x_2571_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v_mctx_2574_; lean_object* v_zetaDeltaFVarIds_2575_; lean_object* v_postponed_2576_; lean_object* v_diag_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2620_; 
v___x_2572_ = lean_st_ref_put(v_a_2503_, v___x_2571_);
v___x_2573_ = lean_st_ref_take(v_a_2501_);
v_mctx_2574_ = lean_ctor_get(v___x_2573_, 0);
v_zetaDeltaFVarIds_2575_ = lean_ctor_get(v___x_2573_, 2);
v_postponed_2576_ = lean_ctor_get(v___x_2573_, 3);
v_diag_2577_ = lean_ctor_get(v___x_2573_, 4);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2620_ == 0)
{
lean_object* v_unused_2621_; 
v_unused_2621_ = lean_ctor_get(v___x_2573_, 1);
lean_dec(v_unused_2621_);
v___x_2579_ = v___x_2573_;
v_isShared_2580_ = v_isSharedCheck_2620_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_diag_2577_);
lean_inc(v_postponed_2576_);
lean_inc(v_zetaDeltaFVarIds_2575_);
lean_inc(v_mctx_2574_);
lean_dec(v___x_2573_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2620_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2581_; lean_object* v___x_2583_; 
v___x_2581_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 1, v___x_2581_);
v___x_2583_ = v___x_2579_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_mctx_2574_);
lean_ctor_set(v_reuseFailAlloc_2619_, 1, v___x_2581_);
lean_ctor_set(v_reuseFailAlloc_2619_, 2, v_zetaDeltaFVarIds_2575_);
lean_ctor_set(v_reuseFailAlloc_2619_, 3, v_postponed_2576_);
lean_ctor_set(v_reuseFailAlloc_2619_, 4, v_diag_2577_);
v___x_2583_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v_env_2586_; lean_object* v_nextMacroScope_2587_; lean_object* v_ngen_2588_; lean_object* v_auxDeclNGen_2589_; lean_object* v_traceState_2590_; lean_object* v_messages_2591_; lean_object* v_infoState_2592_; lean_object* v_snapshotTasks_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2617_; 
v___x_2584_ = lean_st_ref_put(v_a_2501_, v___x_2583_);
v___x_2585_ = lean_st_ref_take(v_a_2503_);
v_env_2586_ = lean_ctor_get(v___x_2585_, 0);
v_nextMacroScope_2587_ = lean_ctor_get(v___x_2585_, 1);
v_ngen_2588_ = lean_ctor_get(v___x_2585_, 2);
v_auxDeclNGen_2589_ = lean_ctor_get(v___x_2585_, 3);
v_traceState_2590_ = lean_ctor_get(v___x_2585_, 4);
v_messages_2591_ = lean_ctor_get(v___x_2585_, 6);
v_infoState_2592_ = lean_ctor_get(v___x_2585_, 7);
v_snapshotTasks_2593_ = lean_ctor_get(v___x_2585_, 8);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2617_ == 0)
{
lean_object* v_unused_2618_; 
v_unused_2618_ = lean_ctor_get(v___x_2585_, 5);
lean_dec(v_unused_2618_);
v___x_2595_ = v___x_2585_;
v_isShared_2596_ = v_isSharedCheck_2617_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_snapshotTasks_2593_);
lean_inc(v_infoState_2592_);
lean_inc(v_messages_2591_);
lean_inc(v_traceState_2590_);
lean_inc(v_auxDeclNGen_2589_);
lean_inc(v_ngen_2588_);
lean_inc(v_nextMacroScope_2587_);
lean_inc(v_env_2586_);
lean_dec(v___x_2585_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2617_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2597_; lean_object* v___x_2599_; 
lean_inc(v_declName_2505_);
v___x_2597_ = l_Lean_addProtected(v_env_2586_, v_declName_2505_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 5, v___x_2569_);
lean_ctor_set(v___x_2595_, 0, v___x_2597_);
v___x_2599_ = v___x_2595_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v___x_2597_);
lean_ctor_set(v_reuseFailAlloc_2616_, 1, v_nextMacroScope_2587_);
lean_ctor_set(v_reuseFailAlloc_2616_, 2, v_ngen_2588_);
lean_ctor_set(v_reuseFailAlloc_2616_, 3, v_auxDeclNGen_2589_);
lean_ctor_set(v_reuseFailAlloc_2616_, 4, v_traceState_2590_);
lean_ctor_set(v_reuseFailAlloc_2616_, 5, v___x_2569_);
lean_ctor_set(v_reuseFailAlloc_2616_, 6, v_messages_2591_);
lean_ctor_set(v_reuseFailAlloc_2616_, 7, v_infoState_2592_);
lean_ctor_set(v_reuseFailAlloc_2616_, 8, v_snapshotTasks_2593_);
v___x_2599_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v_mctx_2602_; lean_object* v_zetaDeltaFVarIds_2603_; lean_object* v_postponed_2604_; lean_object* v_diag_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2614_; 
v___x_2600_ = lean_st_ref_put(v_a_2503_, v___x_2599_);
v___x_2601_ = lean_st_ref_take(v_a_2501_);
v_mctx_2602_ = lean_ctor_get(v___x_2601_, 0);
v_zetaDeltaFVarIds_2603_ = lean_ctor_get(v___x_2601_, 2);
v_postponed_2604_ = lean_ctor_get(v___x_2601_, 3);
v_diag_2605_ = lean_ctor_get(v___x_2601_, 4);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2614_ == 0)
{
lean_object* v_unused_2615_; 
v_unused_2615_ = lean_ctor_get(v___x_2601_, 1);
lean_dec(v_unused_2615_);
v___x_2607_ = v___x_2601_;
v_isShared_2608_ = v_isSharedCheck_2614_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_diag_2605_);
lean_inc(v_postponed_2604_);
lean_inc(v_zetaDeltaFVarIds_2603_);
lean_inc(v_mctx_2602_);
lean_dec(v___x_2601_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2614_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2610_; 
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 1, v___x_2581_);
v___x_2610_ = v___x_2607_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_mctx_2602_);
lean_ctor_set(v_reuseFailAlloc_2613_, 1, v___x_2581_);
lean_ctor_set(v_reuseFailAlloc_2613_, 2, v_zetaDeltaFVarIds_2603_);
lean_ctor_set(v_reuseFailAlloc_2613_, 3, v_postponed_2604_);
lean_ctor_set(v_reuseFailAlloc_2613_, 4, v_diag_2605_);
v___x_2610_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2611_ = lean_st_ref_put(v_a_2501_, v___x_2610_);
v___x_2612_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7(v_declName_2505_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_);
return v___x_2612_;
}
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
lean_dec(v_declName_2505_);
return v___x_2555_;
}
}
}
}
else
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2634_; 
lean_dec(v_a_2543_);
lean_dec(v_levelParams_2521_);
lean_dec(v_declName_2505_);
v_a_2627_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2629_ = v___x_2544_;
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2544_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2632_; 
if (v_isShared_2630_ == 0)
{
v___x_2632_ = v___x_2629_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
}
else
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2642_; 
lean_dec(v_levelParams_2521_);
lean_dec(v_declName_2505_);
v_a_2635_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2637_ = v___x_2542_;
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2542_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2640_; 
if (v_isShared_2638_ == 0)
{
v___x_2640_ = v___x_2637_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_a_2635_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
}
else
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2650_; 
lean_dec_ref(v___x_2532_);
lean_dec_ref(v___x_2531_);
lean_dec(v_tail_2525_);
lean_dec(v_head_2524_);
lean_dec(v_levelParams_2521_);
lean_dec(v___x_2515_);
lean_dec_ref(v_val_2508_);
lean_dec(v_declName_2505_);
lean_dec(v_indName_2499_);
v_a_2643_ = lean_ctor_get(v___x_2533_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2645_ = v___x_2533_;
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2533_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2646_ == 0)
{
v___x_2648_ = v___x_2645_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
}
}
else
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
lean_dec(v___x_2523_);
lean_dec(v_levelParams_2521_);
lean_dec(v___x_2518_);
lean_dec(v___x_2515_);
lean_dec_ref(v_val_2508_);
lean_dec(v_declName_2505_);
lean_dec(v_indName_2499_);
v___x_2653_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__5, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__5_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__5);
v___x_2654_ = l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8(v___x_2653_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_);
return v___x_2654_;
}
}
else
{
lean_object* v_a_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2662_; 
lean_dec(v___x_2518_);
lean_dec(v___x_2515_);
lean_dec_ref(v_val_2508_);
lean_dec(v_declName_2505_);
lean_dec(v_indName_2499_);
v_a_2655_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2657_ = v___x_2519_;
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_a_2655_);
lean_dec(v___x_2519_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2660_; 
if (v_isShared_2658_ == 0)
{
v___x_2660_ = v___x_2657_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_a_2655_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
}
}
else
{
lean_object* v___x_2667_; lean_object* v___x_2668_; 
lean_dec(v_a_2507_);
lean_dec(v_declName_2505_);
lean_dec(v_indName_2499_);
v___x_2667_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__6, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__6_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__6);
v___x_2668_ = l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8(v___x_2667_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_);
return v___x_2668_;
}
}
else
{
lean_object* v_a_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2676_; 
lean_dec(v_declName_2505_);
lean_dec(v_indName_2499_);
v_a_2669_ = lean_ctor_get(v___x_2506_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2671_ = v___x_2506_;
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_a_2669_);
lean_dec(v___x_2506_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2674_; 
if (v_isShared_2672_ == 0)
{
v___x_2674_ = v___x_2671_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_a_2669_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___boxed(lean_object* v_indName_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType(v_indName_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_);
lean_dec(v_a_2681_);
lean_dec_ref(v_a_2680_);
lean_dec(v_a_2679_);
lean_dec_ref(v_a_2678_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4(lean_object* v_i_2684_, lean_object* v_P_2685_, lean_object* v___x_2686_, lean_object* v_xs1_2687_, lean_object* v_zs1_2688_, lean_object* v_xs2_2689_, lean_object* v_as_2690_, size_t v_sz_2691_, size_t v_i_2692_, lean_object* v_bs_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
lean_object* v___x_2699_; 
v___x_2699_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg(v_i_2684_, v_P_2685_, v___x_2686_, v_xs1_2687_, v_zs1_2688_, v_xs2_2689_, v_sz_2691_, v_i_2692_, v_bs_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
return v___x_2699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___boxed(lean_object* v_i_2700_, lean_object* v_P_2701_, lean_object* v___x_2702_, lean_object* v_xs1_2703_, lean_object* v_zs1_2704_, lean_object* v_xs2_2705_, lean_object* v_as_2706_, lean_object* v_sz_2707_, lean_object* v_i_2708_, lean_object* v_bs_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
size_t v_sz_boxed_2715_; size_t v_i_boxed_2716_; lean_object* v_res_2717_; 
v_sz_boxed_2715_ = lean_unbox_usize(v_sz_2707_);
lean_dec(v_sz_2707_);
v_i_boxed_2716_ = lean_unbox_usize(v_i_2708_);
lean_dec(v_i_2708_);
v_res_2717_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4(v_i_2700_, v_P_2701_, v___x_2702_, v_xs1_2703_, v_zs1_2704_, v_xs2_2705_, v_as_2706_, v_sz_boxed_2715_, v_i_boxed_2716_, v_bs_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec_ref(v_as_2706_);
lean_dec(v_i_2700_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5(lean_object* v_val_2718_, lean_object* v_P_2719_, lean_object* v_xs1_2720_, lean_object* v_xs2_2721_, lean_object* v_indName_2722_, lean_object* v___x_2723_, lean_object* v___x_2724_, lean_object* v_ysx2_2725_, uint8_t v___y_2726_, lean_object* v___x_2727_, lean_object* v___x_2728_, lean_object* v_tail_2729_, lean_object* v___x_2730_, lean_object* v_as_2731_, size_t v_sz_2732_, size_t v_i_2733_, lean_object* v_bs_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v___x_2740_; 
v___x_2740_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg(v_val_2718_, v_P_2719_, v_xs1_2720_, v_xs2_2721_, v_indName_2722_, v___x_2723_, v___x_2724_, v_ysx2_2725_, v___y_2726_, v___x_2727_, v___x_2728_, v_tail_2729_, v___x_2730_, v_sz_2732_, v_i_2733_, v_bs_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___boxed(lean_object** _args){
lean_object* v_val_2741_ = _args[0];
lean_object* v_P_2742_ = _args[1];
lean_object* v_xs1_2743_ = _args[2];
lean_object* v_xs2_2744_ = _args[3];
lean_object* v_indName_2745_ = _args[4];
lean_object* v___x_2746_ = _args[5];
lean_object* v___x_2747_ = _args[6];
lean_object* v_ysx2_2748_ = _args[7];
lean_object* v___y_2749_ = _args[8];
lean_object* v___x_2750_ = _args[9];
lean_object* v___x_2751_ = _args[10];
lean_object* v_tail_2752_ = _args[11];
lean_object* v___x_2753_ = _args[12];
lean_object* v_as_2754_ = _args[13];
lean_object* v_sz_2755_ = _args[14];
lean_object* v_i_2756_ = _args[15];
lean_object* v_bs_2757_ = _args[16];
lean_object* v___y_2758_ = _args[17];
lean_object* v___y_2759_ = _args[18];
lean_object* v___y_2760_ = _args[19];
lean_object* v___y_2761_ = _args[20];
lean_object* v___y_2762_ = _args[21];
_start:
{
uint8_t v___y_18427__boxed_2763_; size_t v_sz_boxed_2764_; size_t v_i_boxed_2765_; lean_object* v_res_2766_; 
v___y_18427__boxed_2763_ = lean_unbox(v___y_2749_);
v_sz_boxed_2764_ = lean_unbox_usize(v_sz_2755_);
lean_dec(v_sz_2755_);
v_i_boxed_2765_ = lean_unbox_usize(v_i_2756_);
lean_dec(v_i_2756_);
v_res_2766_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5(v_val_2741_, v_P_2742_, v_xs1_2743_, v_xs2_2744_, v_indName_2745_, v___x_2746_, v___x_2747_, v_ysx2_2748_, v___y_18427__boxed_2763_, v___x_2750_, v___x_2751_, v_tail_2752_, v___x_2753_, v_as_2754_, v_sz_boxed_2764_, v_i_boxed_2765_, v_bs_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec_ref(v_as_2754_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8(lean_object* v_declName_2767_, uint8_t v_s_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_){
_start:
{
lean_object* v___x_2774_; 
v___x_2774_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg(v_declName_2767_, v_s_2768_, v___y_2770_, v___y_2772_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___boxed(lean_object* v_declName_2775_, lean_object* v_s_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_){
_start:
{
uint8_t v_s_boxed_2782_; lean_object* v_res_2783_; 
v_s_boxed_2782_ = lean_unbox(v_s_2776_);
v_res_2783_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8(v_declName_2775_, v_s_boxed_2782_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
return v_res_2783_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0(lean_object* v_00_u03b1_2784_, lean_object* v_constName_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_){
_start:
{
lean_object* v___x_2791_; 
v___x_2791_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0___redArg(v_constName_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2792_, lean_object* v_constName_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0(v_00_u03b1_2792_, v_constName_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_2800_, lean_object* v_ref_2801_, lean_object* v_constName_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v___x_2808_; 
v___x_2808_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg(v_ref_2801_, v_constName_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_2809_, lean_object* v_ref_2810_, lean_object* v_constName_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
lean_object* v_res_2817_; 
v_res_2817_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4(v_00_u03b1_2809_, v_ref_2810_, v_constName_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v_ref_2810_);
return v_res_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11(lean_object* v_00_u03b1_2818_, lean_object* v_ref_2819_, lean_object* v_msg_2820_, lean_object* v_declHint_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_){
_start:
{
lean_object* v___x_2827_; 
v___x_2827_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_2819_, v_msg_2820_, v_declHint_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11___boxed(lean_object* v_00_u03b1_2828_, lean_object* v_ref_2829_, lean_object* v_msg_2830_, lean_object* v_declHint_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_){
_start:
{
lean_object* v_res_2837_; 
v_res_2837_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11(v_00_u03b1_2828_, v_ref_2829_, v_msg_2830_, v_declHint_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v_ref_2829_);
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(lean_object* v_msg_2838_, lean_object* v_declHint_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_){
_start:
{
lean_object* v___x_2845_; 
v___x_2845_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_2838_, v_declHint_2839_, v___y_2843_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_2846_, lean_object* v_declHint_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(v_msg_2846_, v_declHint_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__13(lean_object* v_00_u03b1_2854_, lean_object* v_ref_2855_, lean_object* v_msg_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_){
_start:
{
lean_object* v___x_2862_; 
v___x_2862_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_2855_, v_msg_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__13___boxed(lean_object* v_00_u03b1_2863_, lean_object* v_ref_2864_, lean_object* v_msg_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_){
_start:
{
lean_object* v_res_2871_; 
v_res_2871_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__13(v_00_u03b1_2863_, v_ref_2864_, v_msg_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v_ref_2864_);
return v_res_2871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___lam__0___boxed(lean_object* v_x_2872_, lean_object* v_xs_2873_, lean_object* v_k_2874_, lean_object* v_tail_2875_, lean_object* v_tail_2876_, lean_object* v_v_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
lean_object* v_res_2883_; 
v_res_2883_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___lam__0(v_x_2872_, v_xs_2873_, v_k_2874_, v_tail_2875_, v_tail_2876_, v_v_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg(lean_object* v_xs_2887_, lean_object* v_k_2888_, lean_object* v_x_2889_, lean_object* v_x_2890_, lean_object* v_x_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_){
_start:
{
if (lean_obj_tag(v_x_2889_) == 1)
{
if (lean_obj_tag(v_x_2890_) == 1)
{
lean_object* v_head_2897_; lean_object* v_tail_2898_; lean_object* v_head_2899_; lean_object* v_tail_2900_; lean_object* v___x_2901_; 
v_head_2897_ = lean_ctor_get(v_x_2889_, 0);
lean_inc(v_head_2897_);
v_tail_2898_ = lean_ctor_get(v_x_2889_, 1);
lean_inc(v_tail_2898_);
lean_dec_ref_known(v_x_2889_, 2);
v_head_2899_ = lean_ctor_get(v_x_2890_, 0);
lean_inc(v_head_2899_);
v_tail_2900_ = lean_ctor_get(v_x_2890_, 1);
lean_inc(v_tail_2900_);
lean_dec_ref_known(v_x_2890_, 2);
v___x_2901_ = l_Lean_Meta_mkEqHEq(v_head_2897_, v_head_2899_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v_a_2902_; lean_object* v___f_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; uint8_t v___x_2906_; 
v_a_2902_ = lean_ctor_get(v___x_2901_, 0);
lean_inc(v_a_2902_);
lean_dec_ref_known(v___x_2901_, 1);
lean_inc_ref(v_xs_2887_);
lean_inc_ref(v_x_2891_);
v___f_2903_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2903_, 0, v_x_2891_);
lean_closure_set(v___f_2903_, 1, v_xs_2887_);
lean_closure_set(v___f_2903_, 2, v_k_2888_);
lean_closure_set(v___f_2903_, 3, v_tail_2898_);
lean_closure_set(v___f_2903_, 4, v_tail_2900_);
v___x_2904_ = lean_unsigned_to_nat(1u);
v___x_2905_ = lean_array_get_size(v_xs_2887_);
lean_dec_ref(v_xs_2887_);
v___x_2906_ = lean_nat_dec_lt(v___x_2904_, v___x_2905_);
if (v___x_2906_ == 0)
{
lean_object* v___x_2907_; lean_object* v___x_2908_; 
lean_dec_ref(v_x_2891_);
v___x_2907_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___closed__1));
v___x_2908_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_2907_, v_a_2902_, v___f_2903_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_);
return v___x_2908_;
}
else
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2909_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___closed__1));
v___x_2910_ = lean_array_get_size(v_x_2891_);
lean_dec_ref(v_x_2891_);
v___x_2911_ = lean_nat_add(v___x_2910_, v___x_2904_);
v___x_2912_ = lean_name_append_index_after(v___x_2909_, v___x_2911_);
v___x_2913_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_2912_, v_a_2902_, v___f_2903_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_);
return v___x_2913_;
}
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
lean_dec(v_tail_2900_);
lean_dec(v_tail_2898_);
lean_dec_ref(v_x_2891_);
lean_dec_ref(v_k_2888_);
lean_dec_ref(v_xs_2887_);
v_a_2914_ = lean_ctor_get(v___x_2901_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2901_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2901_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2914_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
}
else
{
lean_object* v___x_2922_; 
lean_dec_ref_known(v_x_2889_, 2);
lean_dec(v_x_2890_);
lean_dec_ref(v_xs_2887_);
lean_inc(v_a_2895_);
lean_inc_ref(v_a_2894_);
lean_inc(v_a_2893_);
lean_inc_ref(v_a_2892_);
v___x_2922_ = lean_apply_6(v_k_2888_, v_x_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, lean_box(0));
return v___x_2922_;
}
}
else
{
lean_object* v___x_2923_; 
lean_dec(v_x_2890_);
lean_dec(v_x_2889_);
lean_dec_ref(v_xs_2887_);
lean_inc(v_a_2895_);
lean_inc_ref(v_a_2894_);
lean_inc(v_a_2893_);
lean_inc_ref(v_a_2892_);
v___x_2923_ = lean_apply_6(v_k_2888_, v_x_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, lean_box(0));
return v___x_2923_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___lam__0(lean_object* v_x_2924_, lean_object* v_xs_2925_, lean_object* v_k_2926_, lean_object* v_tail_2927_, lean_object* v_tail_2928_, lean_object* v_v_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_){
_start:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2935_ = lean_array_push(v_x_2924_, v_v_2929_);
v___x_2936_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg(v_xs_2925_, v_k_2926_, v_tail_2927_, v_tail_2928_, v___x_2935_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___boxed(lean_object* v_xs_2937_, lean_object* v_k_2938_, lean_object* v_x_2939_, lean_object* v_x_2940_, lean_object* v_x_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_){
_start:
{
lean_object* v_res_2947_; 
v_res_2947_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg(v_xs_2937_, v_k_2938_, v_x_2939_, v_x_2940_, v_x_2941_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_);
lean_dec(v_a_2945_);
lean_dec_ref(v_a_2944_);
lean_dec(v_a_2943_);
lean_dec_ref(v_a_2942_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go(lean_object* v_00_u03b1_2948_, lean_object* v_xs_2949_, lean_object* v_k_2950_, lean_object* v_x_2951_, lean_object* v_x_2952_, lean_object* v_x_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_){
_start:
{
lean_object* v___x_2959_; 
v___x_2959_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg(v_xs_2949_, v_k_2950_, v_x_2951_, v_x_2952_, v_x_2953_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___boxed(lean_object* v_00_u03b1_2960_, lean_object* v_xs_2961_, lean_object* v_k_2962_, lean_object* v_x_2963_, lean_object* v_x_2964_, lean_object* v_x_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_){
_start:
{
lean_object* v_res_2971_; 
v_res_2971_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go(v_00_u03b1_2960_, v_xs_2961_, v_k_2962_, v_x_2963_, v_x_2964_, v_x_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_);
lean_dec(v_a_2969_);
lean_dec_ref(v_a_2968_);
lean_dec(v_a_2967_);
lean_dec_ref(v_a_2966_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope___redArg(lean_object* v_xs_2974_, lean_object* v_ys_2975_, lean_object* v_k_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_){
_start:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
lean_inc_ref(v_xs_2974_);
v___x_2982_ = lean_array_to_list(v_xs_2974_);
v___x_2983_ = lean_array_to_list(v_ys_2975_);
v___x_2984_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope___redArg___closed__0));
v___x_2985_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg(v_xs_2974_, v_k_2976_, v___x_2982_, v___x_2983_, v___x_2984_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope___redArg___boxed(lean_object* v_xs_2986_, lean_object* v_ys_2987_, lean_object* v_k_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope___redArg(v_xs_2986_, v_ys_2987_, v_k_2988_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_);
lean_dec(v_a_2992_);
lean_dec_ref(v_a_2991_);
lean_dec(v_a_2990_);
lean_dec_ref(v_a_2989_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope(lean_object* v_00_u03b1_2995_, lean_object* v_inst_2996_, lean_object* v_xs_2997_, lean_object* v_ys_2998_, lean_object* v_k_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_){
_start:
{
lean_object* v___x_3005_; 
v___x_3005_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope___redArg(v_xs_2997_, v_ys_2998_, v_k_2999_, v_a_3000_, v_a_3001_, v_a_3002_, v_a_3003_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope___boxed(lean_object* v_00_u03b1_3006_, lean_object* v_inst_3007_, lean_object* v_xs_3008_, lean_object* v_ys_3009_, lean_object* v_k_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_){
_start:
{
lean_object* v_res_3016_; 
v_res_3016_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope(v_00_u03b1_3006_, v_inst_3007_, v_xs_3008_, v_ys_3009_, v_k_3010_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
lean_dec(v_a_3014_);
lean_dec_ref(v_a_3013_);
lean_dec(v_a_3012_);
lean_dec_ref(v_a_3011_);
lean_dec(v_inst_3007_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg___lam__0___boxed(lean_object* v_x_3017_, lean_object* v_x_3018_, lean_object* v_xs_3019_, lean_object* v_k_3020_, lean_object* v_tail_3021_, lean_object* v_tail_3022_, lean_object* v_v_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
lean_object* v_res_3029_; 
v_res_3029_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg___lam__0(v_x_3017_, v_x_3018_, v_xs_3019_, v_k_3020_, v_tail_3021_, v_tail_3022_, v_v_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg(lean_object* v_xs_3030_, lean_object* v_k_3031_, lean_object* v_x_3032_, lean_object* v_x_3033_, lean_object* v_x_3034_, lean_object* v_x_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_){
_start:
{
if (lean_obj_tag(v_x_3032_) == 1)
{
if (lean_obj_tag(v_x_3033_) == 1)
{
lean_object* v_head_3041_; lean_object* v_tail_3042_; lean_object* v_head_3043_; lean_object* v_tail_3044_; lean_object* v___x_3045_; 
v_head_3041_ = lean_ctor_get(v_x_3032_, 0);
lean_inc_n(v_head_3041_, 2);
v_tail_3042_ = lean_ctor_get(v_x_3032_, 1);
lean_inc(v_tail_3042_);
lean_dec_ref_known(v_x_3032_, 2);
v_head_3043_ = lean_ctor_get(v_x_3033_, 0);
lean_inc_n(v_head_3043_, 2);
v_tail_3044_ = lean_ctor_get(v_x_3033_, 1);
lean_inc(v_tail_3044_);
lean_dec_ref_known(v_x_3033_, 2);
v___x_3045_ = l_Lean_Meta_isExprDefEq(v_head_3041_, v_head_3043_, v_a_3036_, v_a_3037_, v_a_3038_, v_a_3039_);
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_object* v_a_3046_; lean_object* v___f_3047_; uint8_t v___x_3069_; 
v_a_3046_ = lean_ctor_get(v___x_3045_, 0);
lean_inc(v_a_3046_);
lean_dec_ref_known(v___x_3045_, 1);
lean_inc(v_tail_3044_);
lean_inc(v_tail_3042_);
lean_inc_ref(v_k_3031_);
lean_inc_ref(v_xs_3030_);
lean_inc_ref(v_x_3035_);
lean_inc_ref(v_x_3034_);
v___f_3047_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_3047_, 0, v_x_3034_);
lean_closure_set(v___f_3047_, 1, v_x_3035_);
lean_closure_set(v___f_3047_, 2, v_xs_3030_);
lean_closure_set(v___f_3047_, 3, v_k_3031_);
lean_closure_set(v___f_3047_, 4, v_tail_3042_);
lean_closure_set(v___f_3047_, 5, v_tail_3044_);
v___x_3069_ = l_List_isEmpty___redArg(v_tail_3042_);
if (v___x_3069_ == 0)
{
uint8_t v___x_3070_; 
v___x_3070_ = lean_unbox(v_a_3046_);
lean_dec(v_a_3046_);
if (v___x_3070_ == 0)
{
lean_dec(v_tail_3044_);
lean_dec(v_tail_3042_);
lean_dec_ref(v_x_3034_);
lean_dec_ref(v_k_3031_);
goto v___jp_3048_;
}
else
{
lean_object* v___x_3071_; 
lean_dec_ref(v___f_3047_);
lean_dec(v_head_3043_);
v___x_3071_ = l_Lean_Meta_mkEqRefl(v_head_3041_, v_a_3036_, v_a_3037_, v_a_3038_, v_a_3039_);
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_object* v_a_3072_; lean_object* v___x_3073_; 
v_a_3072_ = lean_ctor_get(v___x_3071_, 0);
lean_inc(v_a_3072_);
lean_dec_ref_known(v___x_3071_, 1);
v___x_3073_ = lean_array_push(v_x_3035_, v_a_3072_);
v_x_3032_ = v_tail_3042_;
v_x_3033_ = v_tail_3044_;
v_x_3035_ = v___x_3073_;
goto _start;
}
else
{
lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3082_; 
lean_dec(v_tail_3044_);
lean_dec(v_tail_3042_);
lean_dec_ref(v_x_3035_);
lean_dec_ref(v_x_3034_);
lean_dec_ref(v_k_3031_);
lean_dec_ref(v_xs_3030_);
v_a_3075_ = lean_ctor_get(v___x_3071_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3077_ = v___x_3071_;
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_a_3075_);
lean_dec(v___x_3071_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3080_; 
if (v_isShared_3078_ == 0)
{
v___x_3080_ = v___x_3077_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_a_3075_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
}
}
else
{
lean_dec(v_a_3046_);
lean_dec(v_tail_3044_);
lean_dec(v_tail_3042_);
lean_dec_ref(v_x_3034_);
lean_dec_ref(v_k_3031_);
goto v___jp_3048_;
}
v___jp_3048_:
{
lean_object* v___x_3049_; 
v___x_3049_ = l_Lean_Meta_mkEqHEq(v_head_3041_, v_head_3043_, v_a_3036_, v_a_3037_, v_a_3038_, v_a_3039_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_object* v_a_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; uint8_t v___x_3053_; 
v_a_3050_ = lean_ctor_get(v___x_3049_, 0);
lean_inc(v_a_3050_);
lean_dec_ref_known(v___x_3049_, 1);
v___x_3051_ = lean_unsigned_to_nat(1u);
v___x_3052_ = lean_array_get_size(v_xs_3030_);
lean_dec_ref(v_xs_3030_);
v___x_3053_ = lean_nat_dec_lt(v___x_3051_, v___x_3052_);
if (v___x_3053_ == 0)
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
lean_dec_ref(v_x_3035_);
v___x_3054_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___closed__1));
v___x_3055_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_3054_, v_a_3050_, v___f_3047_, v_a_3036_, v_a_3037_, v_a_3038_, v_a_3039_);
return v___x_3055_;
}
else
{
lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3056_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___closed__1));
v___x_3057_ = lean_array_get_size(v_x_3035_);
lean_dec_ref(v_x_3035_);
v___x_3058_ = lean_nat_add(v___x_3057_, v___x_3051_);
v___x_3059_ = lean_name_append_index_after(v___x_3056_, v___x_3058_);
v___x_3060_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_3059_, v_a_3050_, v___f_3047_, v_a_3036_, v_a_3037_, v_a_3038_, v_a_3039_);
return v___x_3060_;
}
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
lean_dec_ref(v___f_3047_);
lean_dec_ref(v_x_3035_);
lean_dec_ref(v_xs_3030_);
v_a_3061_ = lean_ctor_get(v___x_3049_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_3049_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3049_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
}
else
{
lean_object* v_a_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3090_; 
lean_dec(v_tail_3044_);
lean_dec(v_head_3043_);
lean_dec(v_tail_3042_);
lean_dec(v_head_3041_);
lean_dec_ref(v_x_3035_);
lean_dec_ref(v_x_3034_);
lean_dec_ref(v_k_3031_);
lean_dec_ref(v_xs_3030_);
v_a_3083_ = lean_ctor_get(v___x_3045_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3085_ = v___x_3045_;
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_a_3083_);
lean_dec(v___x_3045_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3088_; 
if (v_isShared_3086_ == 0)
{
v___x_3088_ = v___x_3085_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_a_3083_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
}
else
{
lean_object* v___x_3091_; 
lean_dec_ref_known(v_x_3032_, 2);
lean_dec(v_x_3033_);
lean_dec_ref(v_xs_3030_);
lean_inc(v_a_3039_);
lean_inc_ref(v_a_3038_);
lean_inc(v_a_3037_);
lean_inc_ref(v_a_3036_);
v___x_3091_ = lean_apply_7(v_k_3031_, v_x_3034_, v_x_3035_, v_a_3036_, v_a_3037_, v_a_3038_, v_a_3039_, lean_box(0));
return v___x_3091_;
}
}
else
{
lean_object* v___x_3092_; 
lean_dec(v_x_3033_);
lean_dec(v_x_3032_);
lean_dec_ref(v_xs_3030_);
lean_inc(v_a_3039_);
lean_inc_ref(v_a_3038_);
lean_inc(v_a_3037_);
lean_inc_ref(v_a_3036_);
v___x_3092_ = lean_apply_7(v_k_3031_, v_x_3034_, v_x_3035_, v_a_3036_, v_a_3037_, v_a_3038_, v_a_3039_, lean_box(0));
return v___x_3092_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg___lam__0(lean_object* v_x_3093_, lean_object* v_x_3094_, lean_object* v_xs_3095_, lean_object* v_k_3096_, lean_object* v_tail_3097_, lean_object* v_tail_3098_, lean_object* v_v_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_){
_start:
{
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
lean_inc_ref(v_v_3099_);
v___x_3105_ = lean_array_push(v_x_3093_, v_v_3099_);
v___x_3106_ = lean_array_push(v_x_3094_, v_v_3099_);
v___x_3107_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg(v_xs_3095_, v_k_3096_, v_tail_3097_, v_tail_3098_, v___x_3105_, v___x_3106_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_);
return v___x_3107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg___boxed(lean_object* v_xs_3108_, lean_object* v_k_3109_, lean_object* v_x_3110_, lean_object* v_x_3111_, lean_object* v_x_3112_, lean_object* v_x_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_){
_start:
{
lean_object* v_res_3119_; 
v_res_3119_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg(v_xs_3108_, v_k_3109_, v_x_3110_, v_x_3111_, v_x_3112_, v_x_3113_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_);
lean_dec(v_a_3117_);
lean_dec_ref(v_a_3116_);
lean_dec(v_a_3115_);
lean_dec_ref(v_a_3114_);
return v_res_3119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go(lean_object* v_00_u03b1_3120_, lean_object* v_xs_3121_, lean_object* v_k_3122_, lean_object* v_x_3123_, lean_object* v_x_3124_, lean_object* v_x_3125_, lean_object* v_x_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_){
_start:
{
lean_object* v___x_3132_; 
v___x_3132_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg(v_xs_3121_, v_k_3122_, v_x_3123_, v_x_3124_, v_x_3125_, v_x_3126_, v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_);
return v___x_3132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___boxed(lean_object* v_00_u03b1_3133_, lean_object* v_xs_3134_, lean_object* v_k_3135_, lean_object* v_x_3136_, lean_object* v_x_3137_, lean_object* v_x_3138_, lean_object* v_x_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_){
_start:
{
lean_object* v_res_3145_; 
v_res_3145_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go(v_00_u03b1_3133_, v_xs_3134_, v_k_3135_, v_x_3136_, v_x_3137_, v_x_3138_, v_x_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_);
lean_dec(v_a_3143_);
lean_dec_ref(v_a_3142_);
lean_dec(v_a_3141_);
lean_dec_ref(v_a_3140_);
return v_res_3145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope___redArg(lean_object* v_xs_3146_, lean_object* v_ys_3147_, lean_object* v_k_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_){
_start:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
lean_inc_ref(v_xs_3146_);
v___x_3154_ = lean_array_to_list(v_xs_3146_);
v___x_3155_ = lean_array_to_list(v_ys_3147_);
v___x_3156_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope___redArg___closed__0));
v___x_3157_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg(v_xs_3146_, v_k_3148_, v___x_3154_, v___x_3155_, v___x_3156_, v___x_3156_, v_a_3149_, v_a_3150_, v_a_3151_, v_a_3152_);
return v___x_3157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope___redArg___boxed(lean_object* v_xs_3158_, lean_object* v_ys_3159_, lean_object* v_k_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_){
_start:
{
lean_object* v_res_3166_; 
v_res_3166_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope___redArg(v_xs_3158_, v_ys_3159_, v_k_3160_, v_a_3161_, v_a_3162_, v_a_3163_, v_a_3164_);
lean_dec(v_a_3164_);
lean_dec_ref(v_a_3163_);
lean_dec(v_a_3162_);
lean_dec_ref(v_a_3161_);
return v_res_3166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope(lean_object* v_00_u03b1_3167_, lean_object* v_inst_3168_, lean_object* v_xs_3169_, lean_object* v_ys_3170_, lean_object* v_k_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_){
_start:
{
lean_object* v___x_3177_; 
v___x_3177_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope___redArg(v_xs_3169_, v_ys_3170_, v_k_3171_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_);
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope___boxed(lean_object* v_00_u03b1_3178_, lean_object* v_inst_3179_, lean_object* v_xs_3180_, lean_object* v_ys_3181_, lean_object* v_k_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_){
_start:
{
lean_object* v_res_3188_; 
v_res_3188_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope(v_00_u03b1_3178_, v_inst_3179_, v_xs_3180_, v_ys_3181_, v_k_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_);
lean_dec(v_a_3186_);
lean_dec_ref(v_a_3185_);
lean_dec(v_a_3184_);
lean_dec_ref(v_a_3183_);
lean_dec(v_inst_3179_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__1___redArg(lean_object* v_mvarId_3189_, lean_object* v_x_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_){
_start:
{
lean_object* v___x_3196_; 
v___x_3196_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3189_, v_x_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3204_; 
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3199_ = v___x_3196_;
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___x_3196_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3202_; 
if (v_isShared_3200_ == 0)
{
v___x_3202_ = v___x_3199_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_a_3197_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
else
{
lean_object* v_a_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3212_; 
v_a_3205_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3207_ = v___x_3196_;
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_a_3205_);
lean_dec(v___x_3196_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3210_; 
if (v_isShared_3208_ == 0)
{
v___x_3210_ = v___x_3207_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_a_3205_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__1___redArg___boxed(lean_object* v_mvarId_3213_, lean_object* v_x_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
lean_object* v_res_3220_; 
v_res_3220_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__1___redArg(v_mvarId_3213_, v_x_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
lean_dec(v___y_3218_);
lean_dec_ref(v___y_3217_);
lean_dec(v___y_3216_);
lean_dec_ref(v___y_3215_);
return v_res_3220_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__1(lean_object* v_00_u03b1_3221_, lean_object* v_mvarId_3222_, lean_object* v_x_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_){
_start:
{
lean_object* v___x_3229_; 
v___x_3229_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__1___redArg(v_mvarId_3222_, v_x_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_);
return v___x_3229_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__1___boxed(lean_object* v_00_u03b1_3230_, lean_object* v_mvarId_3231_, lean_object* v_x_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_){
_start:
{
lean_object* v_res_3238_; 
v_res_3238_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__1(v_00_u03b1_3230_, v_mvarId_3231_, v_x_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
return v_res_3238_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__2(lean_object* v_msg_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_){
_start:
{
lean_object* v___f_3245_; lean_object* v___x_3627__overap_3246_; lean_object* v___x_3247_; 
v___f_3245_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8___closed__0));
v___x_3627__overap_3246_ = lean_panic_fn_borrowed(v___f_3245_, v_msg_3239_);
lean_inc(v___y_3243_);
lean_inc_ref(v___y_3242_);
lean_inc(v___y_3241_);
lean_inc_ref(v___y_3240_);
v___x_3247_ = lean_apply_5(v___x_3627__overap_3246_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, lean_box(0));
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__2___boxed(lean_object* v_msg_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_){
_start:
{
lean_object* v_res_3254_; 
v_res_3254_ = l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__2(v_msg_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
return v_res_3254_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__5___redArg(lean_object* v_e_3255_, lean_object* v___y_3256_){
_start:
{
uint8_t v___x_3258_; 
v___x_3258_ = l_Lean_Expr_hasMVar(v_e_3255_);
if (v___x_3258_ == 0)
{
lean_object* v___x_3259_; 
v___x_3259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3259_, 0, v_e_3255_);
return v___x_3259_;
}
else
{
lean_object* v___x_3260_; lean_object* v_mctx_3261_; lean_object* v___x_3262_; lean_object* v_fst_3263_; lean_object* v_snd_3264_; lean_object* v___x_3265_; lean_object* v_cache_3266_; lean_object* v_zetaDeltaFVarIds_3267_; lean_object* v_postponed_3268_; lean_object* v_diag_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3278_; 
v___x_3260_ = lean_st_ref_get(v___y_3256_);
v_mctx_3261_ = lean_ctor_get(v___x_3260_, 0);
lean_inc_ref(v_mctx_3261_);
lean_dec(v___x_3260_);
v___x_3262_ = l_Lean_instantiateMVarsCore(v_mctx_3261_, v_e_3255_);
v_fst_3263_ = lean_ctor_get(v___x_3262_, 0);
lean_inc(v_fst_3263_);
v_snd_3264_ = lean_ctor_get(v___x_3262_, 1);
lean_inc(v_snd_3264_);
lean_dec_ref(v___x_3262_);
v___x_3265_ = lean_st_ref_take(v___y_3256_);
v_cache_3266_ = lean_ctor_get(v___x_3265_, 1);
v_zetaDeltaFVarIds_3267_ = lean_ctor_get(v___x_3265_, 2);
v_postponed_3268_ = lean_ctor_get(v___x_3265_, 3);
v_diag_3269_ = lean_ctor_get(v___x_3265_, 4);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3278_ == 0)
{
lean_object* v_unused_3279_; 
v_unused_3279_ = lean_ctor_get(v___x_3265_, 0);
lean_dec(v_unused_3279_);
v___x_3271_ = v___x_3265_;
v_isShared_3272_ = v_isSharedCheck_3278_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_diag_3269_);
lean_inc(v_postponed_3268_);
lean_inc(v_zetaDeltaFVarIds_3267_);
lean_inc(v_cache_3266_);
lean_dec(v___x_3265_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3278_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3274_; 
if (v_isShared_3272_ == 0)
{
lean_ctor_set(v___x_3271_, 0, v_snd_3264_);
v___x_3274_ = v___x_3271_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_snd_3264_);
lean_ctor_set(v_reuseFailAlloc_3277_, 1, v_cache_3266_);
lean_ctor_set(v_reuseFailAlloc_3277_, 2, v_zetaDeltaFVarIds_3267_);
lean_ctor_set(v_reuseFailAlloc_3277_, 3, v_postponed_3268_);
lean_ctor_set(v_reuseFailAlloc_3277_, 4, v_diag_3269_);
v___x_3274_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; 
v___x_3275_ = lean_st_ref_put(v___y_3256_, v___x_3274_);
v___x_3276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3276_, 0, v_fst_3263_);
return v___x_3276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__5___redArg___boxed(lean_object* v_e_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
lean_object* v_res_3283_; 
v_res_3283_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__5___redArg(v_e_3280_, v___y_3281_);
lean_dec(v___y_3281_);
return v_res_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__5(lean_object* v_e_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
lean_object* v___x_3290_; 
v___x_3290_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__5___redArg(v_e_3284_, v___y_3286_);
return v___x_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__5___boxed(lean_object* v_e_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_){
_start:
{
lean_object* v_res_3297_; 
v_res_3297_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__5(v_e_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__0(lean_object* v_cls_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_){
_start:
{
lean_object* v_options_3307_; uint8_t v_hasTrace_3308_; 
v_options_3307_ = lean_ctor_get(v___y_3304_, 2);
v_hasTrace_3308_ = lean_ctor_get_uint8(v_options_3307_, sizeof(void*)*1);
if (v_hasTrace_3308_ == 0)
{
lean_object* v___x_3309_; lean_object* v___x_3310_; 
lean_dec(v_cls_3301_);
v___x_3309_ = lean_box(v_hasTrace_3308_);
v___x_3310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3309_);
return v___x_3310_;
}
else
{
lean_object* v_inheritedTraceOptions_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; uint8_t v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v_inheritedTraceOptions_3311_ = lean_ctor_get(v___y_3304_, 13);
v___x_3312_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__0___closed__1));
v___x_3313_ = l_Lean_Name_append(v___x_3312_, v_cls_3301_);
v___x_3314_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3311_, v_options_3307_, v___x_3313_);
lean_dec(v___x_3313_);
v___x_3315_ = lean_box(v___x_3314_);
v___x_3316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3315_);
return v___x_3316_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__0___boxed(lean_object* v_cls_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__0(v_cls_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
return v_res_3323_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3324_; double v___x_3325_; 
v___x_3324_ = lean_unsigned_to_nat(0u);
v___x_3325_ = lean_float_of_nat(v___x_3324_);
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0(lean_object* v_cls_3329_, lean_object* v_msg_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
lean_object* v_ref_3336_; lean_object* v___x_3337_; lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3382_; 
v_ref_3336_ = lean_ctor_get(v___y_3333_, 5);
v___x_3337_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0_spec__4(v_msg_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3340_ = v___x_3337_;
v_isShared_3341_ = v_isSharedCheck_3382_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3337_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3382_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3342_; lean_object* v_traceState_3343_; lean_object* v_env_3344_; lean_object* v_nextMacroScope_3345_; lean_object* v_ngen_3346_; lean_object* v_auxDeclNGen_3347_; lean_object* v_cache_3348_; lean_object* v_messages_3349_; lean_object* v_infoState_3350_; lean_object* v_snapshotTasks_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3381_; 
v___x_3342_ = lean_st_ref_take(v___y_3334_);
v_traceState_3343_ = lean_ctor_get(v___x_3342_, 4);
v_env_3344_ = lean_ctor_get(v___x_3342_, 0);
v_nextMacroScope_3345_ = lean_ctor_get(v___x_3342_, 1);
v_ngen_3346_ = lean_ctor_get(v___x_3342_, 2);
v_auxDeclNGen_3347_ = lean_ctor_get(v___x_3342_, 3);
v_cache_3348_ = lean_ctor_get(v___x_3342_, 5);
v_messages_3349_ = lean_ctor_get(v___x_3342_, 6);
v_infoState_3350_ = lean_ctor_get(v___x_3342_, 7);
v_snapshotTasks_3351_ = lean_ctor_get(v___x_3342_, 8);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3353_ = v___x_3342_;
v_isShared_3354_ = v_isSharedCheck_3381_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_snapshotTasks_3351_);
lean_inc(v_infoState_3350_);
lean_inc(v_messages_3349_);
lean_inc(v_cache_3348_);
lean_inc(v_traceState_3343_);
lean_inc(v_auxDeclNGen_3347_);
lean_inc(v_ngen_3346_);
lean_inc(v_nextMacroScope_3345_);
lean_inc(v_env_3344_);
lean_dec(v___x_3342_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3381_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
uint64_t v_tid_3355_; lean_object* v_traces_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3380_; 
v_tid_3355_ = lean_ctor_get_uint64(v_traceState_3343_, sizeof(void*)*1);
v_traces_3356_ = lean_ctor_get(v_traceState_3343_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v_traceState_3343_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3358_ = v_traceState_3343_;
v_isShared_3359_ = v_isSharedCheck_3380_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_traces_3356_);
lean_dec(v_traceState_3343_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3380_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v___x_3360_; double v___x_3361_; uint8_t v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3370_; 
v___x_3360_ = lean_box(0);
v___x_3361_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__0);
v___x_3362_ = 0;
v___x_3363_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__1));
v___x_3364_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3364_, 0, v_cls_3329_);
lean_ctor_set(v___x_3364_, 1, v___x_3360_);
lean_ctor_set(v___x_3364_, 2, v___x_3363_);
lean_ctor_set_float(v___x_3364_, sizeof(void*)*3, v___x_3361_);
lean_ctor_set_float(v___x_3364_, sizeof(void*)*3 + 8, v___x_3361_);
lean_ctor_set_uint8(v___x_3364_, sizeof(void*)*3 + 16, v___x_3362_);
v___x_3365_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__2));
v___x_3366_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3364_);
lean_ctor_set(v___x_3366_, 1, v_a_3338_);
lean_ctor_set(v___x_3366_, 2, v___x_3365_);
lean_inc(v_ref_3336_);
v___x_3367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3367_, 0, v_ref_3336_);
lean_ctor_set(v___x_3367_, 1, v___x_3366_);
v___x_3368_ = l_Lean_PersistentArray_push___redArg(v_traces_3356_, v___x_3367_);
if (v_isShared_3359_ == 0)
{
lean_ctor_set(v___x_3358_, 0, v___x_3368_);
v___x_3370_ = v___x_3358_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v___x_3368_);
lean_ctor_set_uint64(v_reuseFailAlloc_3379_, sizeof(void*)*1, v_tid_3355_);
v___x_3370_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
lean_object* v___x_3372_; 
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 4, v___x_3370_);
v___x_3372_ = v___x_3353_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_env_3344_);
lean_ctor_set(v_reuseFailAlloc_3378_, 1, v_nextMacroScope_3345_);
lean_ctor_set(v_reuseFailAlloc_3378_, 2, v_ngen_3346_);
lean_ctor_set(v_reuseFailAlloc_3378_, 3, v_auxDeclNGen_3347_);
lean_ctor_set(v_reuseFailAlloc_3378_, 4, v___x_3370_);
lean_ctor_set(v_reuseFailAlloc_3378_, 5, v_cache_3348_);
lean_ctor_set(v_reuseFailAlloc_3378_, 6, v_messages_3349_);
lean_ctor_set(v_reuseFailAlloc_3378_, 7, v_infoState_3350_);
lean_ctor_set(v_reuseFailAlloc_3378_, 8, v_snapshotTasks_3351_);
v___x_3372_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3376_; 
v___x_3373_ = lean_st_ref_put(v___y_3334_, v___x_3372_);
v___x_3374_ = lean_box(0);
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 0, v___x_3374_);
v___x_3376_ = v___x_3340_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v___x_3374_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
return v___x_3376_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___boxed(lean_object* v_cls_3383_, lean_object* v_msg_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_){
_start:
{
lean_object* v_res_3390_; 
v_res_3390_ = l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0(v_cls_3383_, v_msg_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_);
lean_dec(v___y_3388_);
lean_dec_ref(v___y_3387_);
lean_dec(v___y_3386_);
lean_dec_ref(v___y_3385_);
return v_res_3390_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3392_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__0));
v___x_3393_ = l_Lean_stringToMessageData(v___x_3392_);
return v___x_3393_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3395_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__2));
v___x_3396_ = l_Lean_stringToMessageData(v___x_3395_);
return v___x_3396_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3398_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__4));
v___x_3399_ = l_Lean_stringToMessageData(v___x_3398_);
return v___x_3399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1(lean_object* v___f_3400_, lean_object* v___x_3401_, lean_object* v_fst_3402_, lean_object* v_cls_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_){
_start:
{
lean_object* v___x_3409_; 
lean_inc(v___y_3407_);
lean_inc_ref(v___y_3406_);
lean_inc(v___y_3405_);
lean_inc_ref(v___y_3404_);
v___x_3409_ = lean_apply_5(v___f_3400_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, lean_box(0));
if (lean_obj_tag(v___x_3409_) == 0)
{
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3441_; 
v_a_3410_ = lean_ctor_get(v___x_3409_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3412_ = v___x_3409_;
v_isShared_3413_ = v_isSharedCheck_3441_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3409_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3441_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
uint8_t v___x_3414_; 
v___x_3414_ = lean_unbox(v_a_3410_);
lean_dec(v_a_3410_);
if (v___x_3414_ == 0)
{
lean_object* v___x_3415_; lean_object* v___x_3417_; 
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
lean_dec(v_cls_3403_);
lean_dec(v_fst_3402_);
lean_dec_ref(v___x_3401_);
v___x_3415_ = lean_box(0);
if (v_isShared_3413_ == 0)
{
lean_ctor_set(v___x_3412_, 0, v___x_3415_);
v___x_3417_ = v___x_3412_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v___x_3415_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
else
{
lean_object* v___x_3419_; 
lean_del_object(v___x_3412_);
lean_inc(v___y_3407_);
lean_inc_ref(v___y_3406_);
lean_inc(v___y_3405_);
lean_inc_ref(v___y_3404_);
lean_inc_ref(v___x_3401_);
v___x_3419_ = lean_infer_type(v___x_3401_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_object* v_a_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; 
v_a_3420_ = lean_ctor_get(v___x_3419_, 0);
lean_inc(v_a_3420_);
lean_dec_ref_known(v___x_3419_, 1);
v___x_3421_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__1, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__1_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__1);
v___x_3422_ = l_Lean_MessageData_ofExpr(v___x_3401_);
v___x_3423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3421_);
lean_ctor_set(v___x_3423_, 1, v___x_3422_);
v___x_3424_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__3, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__3_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__3);
v___x_3425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3423_);
lean_ctor_set(v___x_3425_, 1, v___x_3424_);
v___x_3426_ = l_Lean_MessageData_ofExpr(v_a_3420_);
v___x_3427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3425_);
lean_ctor_set(v___x_3427_, 1, v___x_3426_);
v___x_3428_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__5, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__5_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__5);
v___x_3429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3427_);
lean_ctor_set(v___x_3429_, 1, v___x_3428_);
v___x_3430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3430_, 0, v_fst_3402_);
v___x_3431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3429_);
lean_ctor_set(v___x_3431_, 1, v___x_3430_);
v___x_3432_ = l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0(v_cls_3403_, v___x_3431_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
return v___x_3432_;
}
else
{
lean_object* v_a_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3440_; 
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
lean_dec(v_cls_3403_);
lean_dec(v_fst_3402_);
lean_dec_ref(v___x_3401_);
v_a_3433_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3435_ = v___x_3419_;
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_a_3433_);
lean_dec(v___x_3419_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3438_; 
if (v_isShared_3436_ == 0)
{
v___x_3438_ = v___x_3435_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_a_3433_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
return v___x_3438_;
}
}
}
}
}
}
else
{
lean_object* v_a_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3449_; 
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
lean_dec(v_cls_3403_);
lean_dec(v_fst_3402_);
lean_dec_ref(v___x_3401_);
v_a_3442_ = lean_ctor_get(v___x_3409_, 0);
v_isSharedCheck_3449_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3444_ = v___x_3409_;
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_a_3442_);
lean_dec(v___x_3409_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v___x_3447_; 
if (v_isShared_3445_ == 0)
{
v___x_3447_ = v___x_3444_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_a_3442_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___boxed(lean_object* v___f_3450_, lean_object* v___x_3451_, lean_object* v_fst_3452_, lean_object* v_cls_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_){
_start:
{
lean_object* v_res_3459_; 
v_res_3459_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1(v___f_3450_, v___x_3451_, v_fst_3452_, v_cls_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
return v_res_3459_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3461_; lean_object* v___x_3462_; 
v___x_3461_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0___closed__0));
v___x_3462_ = l_Lean_stringToMessageData(v___x_3461_);
return v___x_3462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0(lean_object* v_cls_3463_, lean_object* v___x_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_){
_start:
{
lean_object* v_options_3473_; uint8_t v_hasTrace_3474_; 
v_options_3473_ = lean_ctor_get(v___y_3467_, 2);
v_hasTrace_3474_ = lean_ctor_get_uint8(v_options_3473_, sizeof(void*)*1);
if (v_hasTrace_3474_ == 0)
{
lean_dec_ref(v___x_3464_);
lean_dec(v_cls_3463_);
goto v___jp_3470_;
}
else
{
lean_object* v_inheritedTraceOptions_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; uint8_t v___x_3478_; 
v_inheritedTraceOptions_3475_ = lean_ctor_get(v___y_3467_, 13);
v___x_3476_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__0___closed__1));
lean_inc(v_cls_3463_);
v___x_3477_ = l_Lean_Name_append(v___x_3476_, v_cls_3463_);
v___x_3478_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3475_, v_options_3473_, v___x_3477_);
lean_dec(v___x_3477_);
if (v___x_3478_ == 0)
{
lean_dec_ref(v___x_3464_);
lean_dec(v_cls_3463_);
goto v___jp_3470_;
}
else
{
lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; 
v___x_3479_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0___closed__1);
v___x_3480_ = l_Lean_MessageData_ofExpr(v___x_3464_);
v___x_3481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3479_);
lean_ctor_set(v___x_3481_, 1, v___x_3480_);
v___x_3482_ = l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0(v_cls_3463_, v___x_3481_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
return v___x_3482_;
}
}
v___jp_3470_:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; 
v___x_3471_ = lean_box(0);
v___x_3472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3472_, 0, v___x_3471_);
return v___x_3472_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0___boxed(lean_object* v_cls_3483_, lean_object* v___x_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_){
_start:
{
lean_object* v_res_3490_; 
v_res_3490_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0(v_cls_3483_, v___x_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3(lean_object* v_as_3495_, size_t v_sz_3496_, size_t v_i_3497_, lean_object* v_b_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_){
_start:
{
uint8_t v___x_3504_; 
v___x_3504_ = lean_usize_dec_lt(v_i_3497_, v_sz_3496_);
if (v___x_3504_ == 0)
{
lean_object* v___x_3505_; 
v___x_3505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3505_, 0, v_b_3498_);
return v___x_3505_;
}
else
{
lean_object* v_fst_3506_; lean_object* v_snd_3507_; lean_object* v_cls_3508_; lean_object* v_a_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___f_3512_; lean_object* v___x_3513_; 
v_fst_3506_ = lean_ctor_get(v_b_3498_, 0);
lean_inc_n(v_fst_3506_, 2);
v_snd_3507_ = lean_ctor_get(v_b_3498_, 1);
lean_inc(v_snd_3507_);
lean_dec_ref(v_b_3498_);
v_cls_3508_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___closed__1));
v_a_3509_ = lean_array_uget_borrowed(v_as_3495_, v_i_3497_);
v___x_3510_ = l_Lean_Expr_fvarId_x21(v_a_3509_);
v___x_3511_ = l_Lean_Meta_FVarSubst_get(v_snd_3507_, v___x_3510_);
lean_inc_ref(v___x_3511_);
v___f_3512_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3512_, 0, v_cls_3508_);
lean_closure_set(v___f_3512_, 1, v___x_3511_);
v___x_3513_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__1___redArg(v_fst_3506_, v___f_3512_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v___x_3514_; lean_object* v___x_3515_; 
lean_dec_ref_known(v___x_3513_, 1);
v___x_3514_ = l_Lean_Expr_fvarId_x21(v___x_3511_);
lean_dec_ref(v___x_3511_);
v___x_3515_ = l_Lean_Meta_substEq(v_fst_3506_, v___x_3514_, v_snd_3507_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v_fst_3517_; lean_object* v_snd_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3528_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_a_3516_);
lean_dec_ref_known(v___x_3515_, 1);
v_fst_3517_ = lean_ctor_get(v_a_3516_, 0);
v_snd_3518_ = lean_ctor_get(v_a_3516_, 1);
v_isSharedCheck_3528_ = !lean_is_exclusive(v_a_3516_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3520_ = v_a_3516_;
v_isShared_3521_ = v_isSharedCheck_3528_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_snd_3518_);
lean_inc(v_fst_3517_);
lean_dec(v_a_3516_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3528_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3523_; 
if (v_isShared_3521_ == 0)
{
lean_ctor_set(v___x_3520_, 1, v_fst_3517_);
lean_ctor_set(v___x_3520_, 0, v_snd_3518_);
v___x_3523_ = v___x_3520_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_snd_3518_);
lean_ctor_set(v_reuseFailAlloc_3527_, 1, v_fst_3517_);
v___x_3523_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
size_t v___x_3524_; size_t v___x_3525_; 
v___x_3524_ = ((size_t)1ULL);
v___x_3525_ = lean_usize_add(v_i_3497_, v___x_3524_);
v_i_3497_ = v___x_3525_;
v_b_3498_ = v___x_3523_;
goto _start;
}
}
}
else
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3536_; 
v_a_3529_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3531_ = v___x_3515_;
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3515_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3534_; 
if (v_isShared_3532_ == 0)
{
v___x_3534_ = v___x_3531_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_a_3529_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
}
}
else
{
lean_object* v_a_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3544_; 
lean_dec_ref(v___x_3511_);
lean_dec(v_snd_3507_);
lean_dec(v_fst_3506_);
v_a_3537_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3539_ = v___x_3513_;
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_a_3537_);
lean_dec(v___x_3513_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3542_; 
if (v_isShared_3540_ == 0)
{
v___x_3542_ = v___x_3539_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_a_3537_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___boxed(lean_object* v_as_3545_, lean_object* v_sz_3546_, lean_object* v_i_3547_, lean_object* v_b_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
size_t v_sz_boxed_3554_; size_t v_i_boxed_3555_; lean_object* v_res_3556_; 
v_sz_boxed_3554_ = lean_unbox_usize(v_sz_3546_);
lean_dec(v_sz_3546_);
v_i_boxed_3555_ = lean_unbox_usize(v_i_3547_);
lean_dec(v_i_3547_);
v_res_3556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3(v_as_3545_, v_sz_boxed_3554_, v_i_boxed_3555_, v_b_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec_ref(v_as_3545_);
return v_res_3556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__8_spec__9___redArg(lean_object* v_x_3557_, lean_object* v_x_3558_, lean_object* v_x_3559_, lean_object* v_x_3560_){
_start:
{
lean_object* v_ks_3561_; lean_object* v_vs_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3586_; 
v_ks_3561_ = lean_ctor_get(v_x_3557_, 0);
v_vs_3562_ = lean_ctor_get(v_x_3557_, 1);
v_isSharedCheck_3586_ = !lean_is_exclusive(v_x_3557_);
if (v_isSharedCheck_3586_ == 0)
{
v___x_3564_ = v_x_3557_;
v_isShared_3565_ = v_isSharedCheck_3586_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_vs_3562_);
lean_inc(v_ks_3561_);
lean_dec(v_x_3557_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3586_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3566_; uint8_t v___x_3567_; 
v___x_3566_ = lean_array_get_size(v_ks_3561_);
v___x_3567_ = lean_nat_dec_lt(v_x_3558_, v___x_3566_);
if (v___x_3567_ == 0)
{
lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3571_; 
lean_dec(v_x_3558_);
v___x_3568_ = lean_array_push(v_ks_3561_, v_x_3559_);
v___x_3569_ = lean_array_push(v_vs_3562_, v_x_3560_);
if (v_isShared_3565_ == 0)
{
lean_ctor_set(v___x_3564_, 1, v___x_3569_);
lean_ctor_set(v___x_3564_, 0, v___x_3568_);
v___x_3571_ = v___x_3564_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v___x_3568_);
lean_ctor_set(v_reuseFailAlloc_3572_, 1, v___x_3569_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
return v___x_3571_;
}
}
else
{
lean_object* v_k_x27_3573_; uint8_t v___x_3574_; 
v_k_x27_3573_ = lean_array_fget_borrowed(v_ks_3561_, v_x_3558_);
v___x_3574_ = l_Lean_instBEqMVarId_beq(v_x_3559_, v_k_x27_3573_);
if (v___x_3574_ == 0)
{
lean_object* v___x_3576_; 
if (v_isShared_3565_ == 0)
{
v___x_3576_ = v___x_3564_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_ks_3561_);
lean_ctor_set(v_reuseFailAlloc_3580_, 1, v_vs_3562_);
v___x_3576_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
lean_object* v___x_3577_; lean_object* v___x_3578_; 
v___x_3577_ = lean_unsigned_to_nat(1u);
v___x_3578_ = lean_nat_add(v_x_3558_, v___x_3577_);
lean_dec(v_x_3558_);
v_x_3557_ = v___x_3576_;
v_x_3558_ = v___x_3578_;
goto _start;
}
}
else
{
lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3584_; 
v___x_3581_ = lean_array_fset(v_ks_3561_, v_x_3558_, v_x_3559_);
v___x_3582_ = lean_array_fset(v_vs_3562_, v_x_3558_, v_x_3560_);
lean_dec(v_x_3558_);
if (v_isShared_3565_ == 0)
{
lean_ctor_set(v___x_3564_, 1, v___x_3582_);
lean_ctor_set(v___x_3564_, 0, v___x_3581_);
v___x_3584_ = v___x_3564_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v___x_3581_);
lean_ctor_set(v_reuseFailAlloc_3585_, 1, v___x_3582_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
return v___x_3584_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__8___redArg(lean_object* v_n_3587_, lean_object* v_k_3588_, lean_object* v_v_3589_){
_start:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; 
v___x_3590_ = lean_unsigned_to_nat(0u);
v___x_3591_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__8_spec__9___redArg(v_n_3587_, v___x_3590_, v_k_3588_, v_v_3589_);
return v___x_3591_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_3592_; 
v___x_3592_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg(lean_object* v_x_3593_, size_t v_x_3594_, size_t v_x_3595_, lean_object* v_x_3596_, lean_object* v_x_3597_){
_start:
{
if (lean_obj_tag(v_x_3593_) == 0)
{
lean_object* v_es_3598_; size_t v___x_3599_; size_t v___x_3600_; lean_object* v_j_3601_; lean_object* v___x_3602_; uint8_t v___x_3603_; 
v_es_3598_ = lean_ctor_get(v_x_3593_, 0);
v___x_3599_ = ((size_t)31ULL);
v___x_3600_ = lean_usize_land(v_x_3594_, v___x_3599_);
v_j_3601_ = lean_usize_to_nat(v___x_3600_);
v___x_3602_ = lean_array_get_size(v_es_3598_);
v___x_3603_ = lean_nat_dec_lt(v_j_3601_, v___x_3602_);
if (v___x_3603_ == 0)
{
lean_dec(v_j_3601_);
lean_dec(v_x_3597_);
lean_dec(v_x_3596_);
return v_x_3593_;
}
else
{
lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3642_; 
lean_inc_ref(v_es_3598_);
v_isSharedCheck_3642_ = !lean_is_exclusive(v_x_3593_);
if (v_isSharedCheck_3642_ == 0)
{
lean_object* v_unused_3643_; 
v_unused_3643_ = lean_ctor_get(v_x_3593_, 0);
lean_dec(v_unused_3643_);
v___x_3605_ = v_x_3593_;
v_isShared_3606_ = v_isSharedCheck_3642_;
goto v_resetjp_3604_;
}
else
{
lean_dec(v_x_3593_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3642_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v_v_3607_; lean_object* v___x_3608_; lean_object* v_xs_x27_3609_; lean_object* v___y_3611_; 
v_v_3607_ = lean_array_fget(v_es_3598_, v_j_3601_);
v___x_3608_ = lean_box(0);
v_xs_x27_3609_ = lean_array_fset(v_es_3598_, v_j_3601_, v___x_3608_);
switch(lean_obj_tag(v_v_3607_))
{
case 0:
{
lean_object* v_key_3616_; lean_object* v_val_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3627_; 
v_key_3616_ = lean_ctor_get(v_v_3607_, 0);
v_val_3617_ = lean_ctor_get(v_v_3607_, 1);
v_isSharedCheck_3627_ = !lean_is_exclusive(v_v_3607_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3619_ = v_v_3607_;
v_isShared_3620_ = v_isSharedCheck_3627_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_val_3617_);
lean_inc(v_key_3616_);
lean_dec(v_v_3607_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3627_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
uint8_t v___x_3621_; 
v___x_3621_ = l_Lean_instBEqMVarId_beq(v_x_3596_, v_key_3616_);
if (v___x_3621_ == 0)
{
lean_object* v___x_3622_; lean_object* v___x_3623_; 
lean_del_object(v___x_3619_);
v___x_3622_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3616_, v_val_3617_, v_x_3596_, v_x_3597_);
v___x_3623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3623_, 0, v___x_3622_);
v___y_3611_ = v___x_3623_;
goto v___jp_3610_;
}
else
{
lean_object* v___x_3625_; 
lean_dec(v_val_3617_);
lean_dec(v_key_3616_);
if (v_isShared_3620_ == 0)
{
lean_ctor_set(v___x_3619_, 1, v_x_3597_);
lean_ctor_set(v___x_3619_, 0, v_x_3596_);
v___x_3625_ = v___x_3619_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v_x_3596_);
lean_ctor_set(v_reuseFailAlloc_3626_, 1, v_x_3597_);
v___x_3625_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
v___y_3611_ = v___x_3625_;
goto v___jp_3610_;
}
}
}
}
case 1:
{
lean_object* v_node_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3640_; 
v_node_3628_ = lean_ctor_get(v_v_3607_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v_v_3607_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3630_ = v_v_3607_;
v_isShared_3631_ = v_isSharedCheck_3640_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_node_3628_);
lean_dec(v_v_3607_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3640_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
size_t v___x_3632_; size_t v___x_3633_; size_t v___x_3634_; size_t v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3638_; 
v___x_3632_ = ((size_t)5ULL);
v___x_3633_ = lean_usize_shift_right(v_x_3594_, v___x_3632_);
v___x_3634_ = ((size_t)1ULL);
v___x_3635_ = lean_usize_add(v_x_3595_, v___x_3634_);
v___x_3636_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg(v_node_3628_, v___x_3633_, v___x_3635_, v_x_3596_, v_x_3597_);
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 0, v___x_3636_);
v___x_3638_ = v___x_3630_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3636_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
v___y_3611_ = v___x_3638_;
goto v___jp_3610_;
}
}
}
default: 
{
lean_object* v___x_3641_; 
v___x_3641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3641_, 0, v_x_3596_);
lean_ctor_set(v___x_3641_, 1, v_x_3597_);
v___y_3611_ = v___x_3641_;
goto v___jp_3610_;
}
}
v___jp_3610_:
{
lean_object* v___x_3612_; lean_object* v___x_3614_; 
v___x_3612_ = lean_array_fset(v_xs_x27_3609_, v_j_3601_, v___y_3611_);
lean_dec(v_j_3601_);
if (v_isShared_3606_ == 0)
{
lean_ctor_set(v___x_3605_, 0, v___x_3612_);
v___x_3614_ = v___x_3605_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v___x_3612_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
}
}
}
else
{
lean_object* v_ks_3644_; lean_object* v_vs_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3663_; 
v_ks_3644_ = lean_ctor_get(v_x_3593_, 0);
v_vs_3645_ = lean_ctor_get(v_x_3593_, 1);
v_isSharedCheck_3663_ = !lean_is_exclusive(v_x_3593_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3647_ = v_x_3593_;
v_isShared_3648_ = v_isSharedCheck_3663_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_vs_3645_);
lean_inc(v_ks_3644_);
lean_dec(v_x_3593_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3663_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3650_; 
if (v_isShared_3648_ == 0)
{
v___x_3650_ = v___x_3647_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_ks_3644_);
lean_ctor_set(v_reuseFailAlloc_3662_, 1, v_vs_3645_);
v___x_3650_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
lean_object* v_newNode_3651_; size_t v___x_3652_; uint8_t v___x_3653_; 
v_newNode_3651_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__8___redArg(v___x_3650_, v_x_3596_, v_x_3597_);
v___x_3652_ = ((size_t)7ULL);
v___x_3653_ = lean_usize_dec_le(v___x_3652_, v_x_3595_);
if (v___x_3653_ == 0)
{
lean_object* v___x_3654_; lean_object* v___x_3655_; uint8_t v___x_3656_; 
v___x_3654_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3651_);
v___x_3655_ = lean_unsigned_to_nat(4u);
v___x_3656_ = lean_nat_dec_lt(v___x_3654_, v___x_3655_);
lean_dec(v___x_3654_);
if (v___x_3656_ == 0)
{
lean_object* v_ks_3657_; lean_object* v_vs_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
v_ks_3657_ = lean_ctor_get(v_newNode_3651_, 0);
lean_inc_ref(v_ks_3657_);
v_vs_3658_ = lean_ctor_get(v_newNode_3651_, 1);
lean_inc_ref(v_vs_3658_);
lean_dec_ref(v_newNode_3651_);
v___x_3659_ = lean_unsigned_to_nat(0u);
v___x_3660_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg___closed__0);
v___x_3661_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__9___redArg(v_x_3595_, v_ks_3657_, v_vs_3658_, v___x_3659_, v___x_3660_);
lean_dec_ref(v_vs_3658_);
lean_dec_ref(v_ks_3657_);
return v___x_3661_;
}
else
{
return v_newNode_3651_;
}
}
else
{
return v_newNode_3651_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__9___redArg(size_t v_depth_3664_, lean_object* v_keys_3665_, lean_object* v_vals_3666_, lean_object* v_i_3667_, lean_object* v_entries_3668_){
_start:
{
lean_object* v___x_3669_; uint8_t v___x_3670_; 
v___x_3669_ = lean_array_get_size(v_keys_3665_);
v___x_3670_ = lean_nat_dec_lt(v_i_3667_, v___x_3669_);
if (v___x_3670_ == 0)
{
lean_dec(v_i_3667_);
return v_entries_3668_;
}
else
{
lean_object* v_k_3671_; lean_object* v_v_3672_; uint64_t v___x_3673_; size_t v_h_3674_; size_t v___x_3675_; lean_object* v___x_3676_; size_t v___x_3677_; size_t v___x_3678_; size_t v___x_3679_; size_t v_h_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; 
v_k_3671_ = lean_array_fget_borrowed(v_keys_3665_, v_i_3667_);
v_v_3672_ = lean_array_fget_borrowed(v_vals_3666_, v_i_3667_);
v___x_3673_ = l_Lean_instHashableMVarId_hash(v_k_3671_);
v_h_3674_ = lean_uint64_to_usize(v___x_3673_);
v___x_3675_ = ((size_t)5ULL);
v___x_3676_ = lean_unsigned_to_nat(1u);
v___x_3677_ = ((size_t)1ULL);
v___x_3678_ = lean_usize_sub(v_depth_3664_, v___x_3677_);
v___x_3679_ = lean_usize_mul(v___x_3675_, v___x_3678_);
v_h_3680_ = lean_usize_shift_right(v_h_3674_, v___x_3679_);
v___x_3681_ = lean_nat_add(v_i_3667_, v___x_3676_);
lean_dec(v_i_3667_);
lean_inc(v_v_3672_);
lean_inc(v_k_3671_);
v___x_3682_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg(v_entries_3668_, v_h_3680_, v_depth_3664_, v_k_3671_, v_v_3672_);
v_i_3667_ = v___x_3681_;
v_entries_3668_ = v___x_3682_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__9___redArg___boxed(lean_object* v_depth_3684_, lean_object* v_keys_3685_, lean_object* v_vals_3686_, lean_object* v_i_3687_, lean_object* v_entries_3688_){
_start:
{
size_t v_depth_boxed_3689_; lean_object* v_res_3690_; 
v_depth_boxed_3689_ = lean_unbox_usize(v_depth_3684_);
lean_dec(v_depth_3684_);
v_res_3690_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__9___redArg(v_depth_boxed_3689_, v_keys_3685_, v_vals_3686_, v_i_3687_, v_entries_3688_);
lean_dec_ref(v_vals_3686_);
lean_dec_ref(v_keys_3685_);
return v_res_3690_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg___boxed(lean_object* v_x_3691_, lean_object* v_x_3692_, lean_object* v_x_3693_, lean_object* v_x_3694_, lean_object* v_x_3695_){
_start:
{
size_t v_x_5628__boxed_3696_; size_t v_x_5629__boxed_3697_; lean_object* v_res_3698_; 
v_x_5628__boxed_3696_ = lean_unbox_usize(v_x_3692_);
lean_dec(v_x_3692_);
v_x_5629__boxed_3697_ = lean_unbox_usize(v_x_3693_);
lean_dec(v_x_3693_);
v_res_3698_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg(v_x_3691_, v_x_5628__boxed_3696_, v_x_5629__boxed_3697_, v_x_3694_, v_x_3695_);
return v_res_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4___redArg(lean_object* v_x_3699_, lean_object* v_x_3700_, lean_object* v_x_3701_){
_start:
{
uint64_t v___x_3702_; size_t v___x_3703_; size_t v___x_3704_; lean_object* v___x_3705_; 
v___x_3702_ = l_Lean_instHashableMVarId_hash(v_x_3700_);
v___x_3703_ = lean_uint64_to_usize(v___x_3702_);
v___x_3704_ = ((size_t)1ULL);
v___x_3705_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg(v_x_3699_, v___x_3703_, v___x_3704_, v_x_3700_, v_x_3701_);
return v___x_3705_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4___redArg(lean_object* v_mvarId_3706_, lean_object* v_val_3707_, lean_object* v___y_3708_){
_start:
{
lean_object* v___x_3710_; lean_object* v_mctx_3711_; lean_object* v_cache_3712_; lean_object* v_zetaDeltaFVarIds_3713_; lean_object* v_postponed_3714_; lean_object* v_diag_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3744_; 
v___x_3710_ = lean_st_ref_take(v___y_3708_);
v_mctx_3711_ = lean_ctor_get(v___x_3710_, 0);
v_cache_3712_ = lean_ctor_get(v___x_3710_, 1);
v_zetaDeltaFVarIds_3713_ = lean_ctor_get(v___x_3710_, 2);
v_postponed_3714_ = lean_ctor_get(v___x_3710_, 3);
v_diag_3715_ = lean_ctor_get(v___x_3710_, 4);
v_isSharedCheck_3744_ = !lean_is_exclusive(v___x_3710_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3717_ = v___x_3710_;
v_isShared_3718_ = v_isSharedCheck_3744_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_diag_3715_);
lean_inc(v_postponed_3714_);
lean_inc(v_zetaDeltaFVarIds_3713_);
lean_inc(v_cache_3712_);
lean_inc(v_mctx_3711_);
lean_dec(v___x_3710_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3744_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v_depth_3719_; lean_object* v_levelAssignDepth_3720_; lean_object* v_lmvarCounter_3721_; lean_object* v_mvarCounter_3722_; lean_object* v_lDecls_3723_; lean_object* v_decls_3724_; lean_object* v_userNames_3725_; lean_object* v_lAssignment_3726_; lean_object* v_eAssignment_3727_; lean_object* v_dAssignment_3728_; lean_object* v_instanceTypedMVars_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3743_; 
v_depth_3719_ = lean_ctor_get(v_mctx_3711_, 0);
v_levelAssignDepth_3720_ = lean_ctor_get(v_mctx_3711_, 1);
v_lmvarCounter_3721_ = lean_ctor_get(v_mctx_3711_, 2);
v_mvarCounter_3722_ = lean_ctor_get(v_mctx_3711_, 3);
v_lDecls_3723_ = lean_ctor_get(v_mctx_3711_, 4);
v_decls_3724_ = lean_ctor_get(v_mctx_3711_, 5);
v_userNames_3725_ = lean_ctor_get(v_mctx_3711_, 6);
v_lAssignment_3726_ = lean_ctor_get(v_mctx_3711_, 7);
v_eAssignment_3727_ = lean_ctor_get(v_mctx_3711_, 8);
v_dAssignment_3728_ = lean_ctor_get(v_mctx_3711_, 9);
v_instanceTypedMVars_3729_ = lean_ctor_get(v_mctx_3711_, 10);
v_isSharedCheck_3743_ = !lean_is_exclusive(v_mctx_3711_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3731_ = v_mctx_3711_;
v_isShared_3732_ = v_isSharedCheck_3743_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_instanceTypedMVars_3729_);
lean_inc(v_dAssignment_3728_);
lean_inc(v_eAssignment_3727_);
lean_inc(v_lAssignment_3726_);
lean_inc(v_userNames_3725_);
lean_inc(v_decls_3724_);
lean_inc(v_lDecls_3723_);
lean_inc(v_mvarCounter_3722_);
lean_inc(v_lmvarCounter_3721_);
lean_inc(v_levelAssignDepth_3720_);
lean_inc(v_depth_3719_);
lean_dec(v_mctx_3711_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3743_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
lean_object* v___x_3733_; lean_object* v___x_3735_; 
v___x_3733_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4___redArg(v_eAssignment_3727_, v_mvarId_3706_, v_val_3707_);
if (v_isShared_3732_ == 0)
{
lean_ctor_set(v___x_3731_, 8, v___x_3733_);
v___x_3735_ = v___x_3731_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_depth_3719_);
lean_ctor_set(v_reuseFailAlloc_3742_, 1, v_levelAssignDepth_3720_);
lean_ctor_set(v_reuseFailAlloc_3742_, 2, v_lmvarCounter_3721_);
lean_ctor_set(v_reuseFailAlloc_3742_, 3, v_mvarCounter_3722_);
lean_ctor_set(v_reuseFailAlloc_3742_, 4, v_lDecls_3723_);
lean_ctor_set(v_reuseFailAlloc_3742_, 5, v_decls_3724_);
lean_ctor_set(v_reuseFailAlloc_3742_, 6, v_userNames_3725_);
lean_ctor_set(v_reuseFailAlloc_3742_, 7, v_lAssignment_3726_);
lean_ctor_set(v_reuseFailAlloc_3742_, 8, v___x_3733_);
lean_ctor_set(v_reuseFailAlloc_3742_, 9, v_dAssignment_3728_);
lean_ctor_set(v_reuseFailAlloc_3742_, 10, v_instanceTypedMVars_3729_);
v___x_3735_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
lean_object* v___x_3737_; 
if (v_isShared_3718_ == 0)
{
lean_ctor_set(v___x_3717_, 0, v___x_3735_);
v___x_3737_ = v___x_3717_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v___x_3735_);
lean_ctor_set(v_reuseFailAlloc_3741_, 1, v_cache_3712_);
lean_ctor_set(v_reuseFailAlloc_3741_, 2, v_zetaDeltaFVarIds_3713_);
lean_ctor_set(v_reuseFailAlloc_3741_, 3, v_postponed_3714_);
lean_ctor_set(v_reuseFailAlloc_3741_, 4, v_diag_3715_);
v___x_3737_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3738_ = lean_st_ref_put(v___y_3708_, v___x_3737_);
v___x_3739_ = lean_box(0);
v___x_3740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3739_);
return v___x_3740_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4___redArg___boxed(lean_object* v_mvarId_3745_, lean_object* v_val_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_){
_start:
{
lean_object* v_res_3749_; 
v_res_3749_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4___redArg(v_mvarId_3745_, v_val_3746_, v___y_3747_);
lean_dec(v___y_3747_);
return v_res_3749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__2(lean_object* v_motive_3750_, lean_object* v_ys_3751_, lean_object* v_e_3752_, lean_object* v___f_3753_, lean_object* v_cls_3754_, uint8_t v___x_3755_, lean_object* v_eqs_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_){
_start:
{
lean_object* v___x_3762_; lean_object* v___x_3763_; uint8_t v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; 
v___x_3762_ = l_Lean_Expr_beta(v_motive_3750_, v_ys_3751_);
v___x_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3762_);
v___x_3764_ = 0;
v___x_3765_ = lean_box(0);
v___x_3766_ = l_Lean_Meta_mkFreshExprMVar(v___x_3763_, v___x_3764_, v___x_3765_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_);
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_object* v_a_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; size_t v_sz_3771_; size_t v___x_3772_; lean_object* v___x_3773_; 
v_a_3767_ = lean_ctor_get(v___x_3766_, 0);
lean_inc(v_a_3767_);
lean_dec_ref_known(v___x_3766_, 1);
v___x_3768_ = l_Lean_Expr_mvarId_x21(v_a_3767_);
v___x_3769_ = lean_box(0);
v___x_3770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3770_, 0, v___x_3768_);
lean_ctor_set(v___x_3770_, 1, v___x_3769_);
v_sz_3771_ = lean_array_size(v_eqs_3756_);
v___x_3772_ = ((size_t)0ULL);
v___x_3773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3(v_eqs_3756_, v_sz_3771_, v___x_3772_, v___x_3770_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_);
if (lean_obj_tag(v___x_3773_) == 0)
{
lean_object* v_a_3774_; lean_object* v_fst_3775_; lean_object* v_snd_3776_; lean_object* v___x_3777_; lean_object* v___f_3778_; lean_object* v___x_3779_; 
v_a_3774_ = lean_ctor_get(v___x_3773_, 0);
lean_inc(v_a_3774_);
lean_dec_ref_known(v___x_3773_, 1);
v_fst_3775_ = lean_ctor_get(v_a_3774_, 0);
lean_inc_n(v_fst_3775_, 3);
v_snd_3776_ = lean_ctor_get(v_a_3774_, 1);
lean_inc(v_snd_3776_);
lean_dec(v_a_3774_);
v___x_3777_ = l_Lean_Meta_FVarSubst_apply(v_snd_3776_, v_e_3752_);
lean_inc_ref(v___x_3777_);
v___f_3778_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___boxed), 9, 4);
lean_closure_set(v___f_3778_, 0, v___f_3753_);
lean_closure_set(v___f_3778_, 1, v___x_3777_);
lean_closure_set(v___f_3778_, 2, v_fst_3775_);
lean_closure_set(v___f_3778_, 3, v_cls_3754_);
v___x_3779_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__1___redArg(v_fst_3775_, v___f_3778_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_);
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v_a_3782_; uint8_t v___x_3783_; uint8_t v___x_3784_; lean_object* v___x_3785_; 
lean_dec_ref_known(v___x_3779_, 1);
v___x_3780_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4___redArg(v_fst_3775_, v___x_3777_, v___y_3758_);
lean_dec_ref(v___x_3780_);
v___x_3781_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__5___redArg(v_a_3767_, v___y_3758_);
v_a_3782_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_a_3782_);
lean_dec_ref(v___x_3781_);
v___x_3783_ = 0;
v___x_3784_ = 1;
v___x_3785_ = l_Lean_Meta_mkLambdaFVars(v_eqs_3756_, v_a_3782_, v___x_3783_, v___x_3755_, v___x_3783_, v___x_3755_, v___x_3784_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_);
return v___x_3785_;
}
else
{
lean_object* v_a_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3793_; 
lean_dec_ref(v___x_3777_);
lean_dec(v_fst_3775_);
lean_dec(v_a_3767_);
v_a_3786_ = lean_ctor_get(v___x_3779_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3779_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3788_ = v___x_3779_;
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_a_3786_);
lean_dec(v___x_3779_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3791_; 
if (v_isShared_3789_ == 0)
{
v___x_3791_ = v___x_3788_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_a_3786_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
}
else
{
lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3801_; 
lean_dec(v_a_3767_);
lean_dec(v_cls_3754_);
lean_dec_ref(v___f_3753_);
v_a_3794_ = lean_ctor_get(v___x_3773_, 0);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3773_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3796_ = v___x_3773_;
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_dec(v___x_3773_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3799_; 
if (v_isShared_3797_ == 0)
{
v___x_3799_ = v___x_3796_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_a_3794_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
}
else
{
lean_dec(v_cls_3754_);
lean_dec_ref(v___f_3753_);
return v___x_3766_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__2___boxed(lean_object* v_motive_3802_, lean_object* v_ys_3803_, lean_object* v_e_3804_, lean_object* v___f_3805_, lean_object* v_cls_3806_, lean_object* v___x_3807_, lean_object* v_eqs_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_){
_start:
{
uint8_t v___x_5839__boxed_3814_; lean_object* v_res_3815_; 
v___x_5839__boxed_3814_ = lean_unbox(v___x_3807_);
v_res_3815_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__2(v_motive_3802_, v_ys_3803_, v_e_3804_, v___f_3805_, v_cls_3806_, v___x_5839__boxed_3814_, v_eqs_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
lean_dec_ref(v_eqs_3808_);
lean_dec_ref(v_e_3804_);
return v_res_3815_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__6(lean_object* v_a_3816_, lean_object* v_a_3817_){
_start:
{
if (lean_obj_tag(v_a_3816_) == 0)
{
lean_object* v___x_3818_; 
v___x_3818_ = l_List_reverse___redArg(v_a_3817_);
return v___x_3818_;
}
else
{
lean_object* v_head_3819_; lean_object* v_tail_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3829_; 
v_head_3819_ = lean_ctor_get(v_a_3816_, 0);
v_tail_3820_ = lean_ctor_get(v_a_3816_, 1);
v_isSharedCheck_3829_ = !lean_is_exclusive(v_a_3816_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3822_ = v_a_3816_;
v_isShared_3823_ = v_isSharedCheck_3829_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_tail_3820_);
lean_inc(v_head_3819_);
lean_dec(v_a_3816_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3829_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
lean_object* v___x_3824_; lean_object* v___x_3826_; 
v___x_3824_ = l_Lean_MessageData_ofExpr(v_head_3819_);
if (v_isShared_3823_ == 0)
{
lean_ctor_set(v___x_3822_, 1, v_a_3817_);
lean_ctor_set(v___x_3822_, 0, v___x_3824_);
v___x_3826_ = v___x_3822_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v___x_3824_);
lean_ctor_set(v_reuseFailAlloc_3828_, 1, v_a_3817_);
v___x_3826_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
v_a_3816_ = v_tail_3820_;
v_a_3817_ = v___x_3826_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__3(void){
_start:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
v___x_3834_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__2));
v___x_3835_ = lean_unsigned_to_nat(2u);
v___x_3836_ = lean_unsigned_to_nat(192u);
v___x_3837_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__1));
v___x_3838_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__2));
v___x_3839_ = l_mkPanicMessageWithDecl(v___x_3838_, v___x_3837_, v___x_3836_, v___x_3835_, v___x_3834_);
return v___x_3839_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__5(void){
_start:
{
lean_object* v___x_3841_; lean_object* v___x_3842_; 
v___x_3841_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__4));
v___x_3842_ = l_Lean_stringToMessageData(v___x_3841_);
return v___x_3842_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__7(void){
_start:
{
lean_object* v___x_3844_; lean_object* v___x_3845_; 
v___x_3844_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__6));
v___x_3845_ = l_Lean_stringToMessageData(v___x_3844_);
return v___x_3845_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__9(void){
_start:
{
lean_object* v___x_3847_; lean_object* v___x_3848_; 
v___x_3847_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__8));
v___x_3848_ = l_Lean_stringToMessageData(v___x_3847_);
return v___x_3848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope(lean_object* v_motive_3849_, lean_object* v_e_3850_, lean_object* v_xs_3851_, lean_object* v_ys_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_){
_start:
{
lean_object* v_cls_3858_; lean_object* v___f_3859_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___x_3873_; lean_object* v_a_3874_; uint8_t v___x_3875_; 
v_cls_3858_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___closed__1));
v___f_3859_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__0));
v___x_3873_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__0(v_cls_3858_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_);
v_a_3874_ = lean_ctor_get(v___x_3873_, 0);
lean_inc(v_a_3874_);
lean_dec_ref(v___x_3873_);
v___x_3875_ = lean_unbox(v_a_3874_);
lean_dec(v_a_3874_);
if (v___x_3875_ == 0)
{
v___y_3861_ = v_a_3853_;
v___y_3862_ = v_a_3854_;
v___y_3863_ = v_a_3855_;
v___y_3864_ = v_a_3856_;
goto v___jp_3860_;
}
else
{
lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; 
v___x_3876_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__5, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__5_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__5);
lean_inc_ref(v_e_3850_);
v___x_3877_ = l_Lean_MessageData_ofExpr(v_e_3850_);
v___x_3878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3878_, 0, v___x_3876_);
lean_ctor_set(v___x_3878_, 1, v___x_3877_);
v___x_3879_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__7, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__7_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__7);
v___x_3880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3878_);
lean_ctor_set(v___x_3880_, 1, v___x_3879_);
lean_inc_ref(v_xs_3851_);
v___x_3881_ = lean_array_to_list(v_xs_3851_);
v___x_3882_ = lean_box(0);
v___x_3883_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__6(v___x_3881_, v___x_3882_);
v___x_3884_ = l_Lean_MessageData_ofList(v___x_3883_);
v___x_3885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3885_, 0, v___x_3880_);
lean_ctor_set(v___x_3885_, 1, v___x_3884_);
v___x_3886_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__9, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__9_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__9);
v___x_3887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3885_);
lean_ctor_set(v___x_3887_, 1, v___x_3886_);
lean_inc_ref(v_ys_3852_);
v___x_3888_ = lean_array_to_list(v_ys_3852_);
v___x_3889_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__6(v___x_3888_, v___x_3882_);
v___x_3890_ = l_Lean_MessageData_ofList(v___x_3889_);
v___x_3891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3887_);
lean_ctor_set(v___x_3891_, 1, v___x_3890_);
v___x_3892_ = l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0(v_cls_3858_, v___x_3891_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_);
if (lean_obj_tag(v___x_3892_) == 0)
{
lean_dec_ref_known(v___x_3892_, 1);
v___y_3861_ = v_a_3853_;
v___y_3862_ = v_a_3854_;
v___y_3863_ = v_a_3855_;
v___y_3864_ = v_a_3856_;
goto v___jp_3860_;
}
else
{
lean_object* v_a_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3900_; 
lean_dec_ref(v_ys_3852_);
lean_dec_ref(v_xs_3851_);
lean_dec_ref(v_e_3850_);
lean_dec_ref(v_motive_3849_);
v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
v_isSharedCheck_3900_ = !lean_is_exclusive(v___x_3892_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3895_ = v___x_3892_;
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_a_3893_);
lean_dec(v___x_3892_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
lean_object* v___x_3898_; 
if (v_isShared_3896_ == 0)
{
v___x_3898_ = v___x_3895_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v_a_3893_);
v___x_3898_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
return v___x_3898_;
}
}
}
}
v___jp_3860_:
{
lean_object* v___x_3865_; lean_object* v___x_3866_; uint8_t v___x_3867_; 
v___x_3865_ = lean_array_get_size(v_xs_3851_);
v___x_3866_ = lean_array_get_size(v_ys_3852_);
v___x_3867_ = lean_nat_dec_eq(v___x_3865_, v___x_3866_);
if (v___x_3867_ == 0)
{
lean_object* v___x_3868_; lean_object* v___x_3869_; 
lean_dec_ref(v_ys_3852_);
lean_dec_ref(v_xs_3851_);
lean_dec_ref(v_e_3850_);
lean_dec_ref(v_motive_3849_);
v___x_3868_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__3, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__3_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__3);
v___x_3869_ = l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__2(v___x_3868_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
return v___x_3869_;
}
else
{
lean_object* v___x_3870_; lean_object* v___f_3871_; lean_object* v___x_3872_; 
v___x_3870_ = lean_box(v___x_3867_);
lean_inc_ref(v_ys_3852_);
v___f_3871_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__2___boxed), 12, 6);
lean_closure_set(v___f_3871_, 0, v_motive_3849_);
lean_closure_set(v___f_3871_, 1, v_ys_3852_);
lean_closure_set(v___f_3871_, 2, v_e_3850_);
lean_closure_set(v___f_3871_, 3, v___f_3859_);
lean_closure_set(v___f_3871_, 4, v_cls_3858_);
lean_closure_set(v___f_3871_, 5, v___x_3870_);
v___x_3872_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope___redArg(v_xs_3851_, v_ys_3852_, v___f_3871_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
return v___x_3872_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___boxed(lean_object* v_motive_3901_, lean_object* v_e_3902_, lean_object* v_xs_3903_, lean_object* v_ys_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_){
_start:
{
lean_object* v_res_3910_; 
v_res_3910_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope(v_motive_3901_, v_e_3902_, v_xs_3903_, v_ys_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_);
lean_dec(v_a_3908_);
lean_dec_ref(v_a_3907_);
lean_dec(v_a_3906_);
lean_dec_ref(v_a_3905_);
return v_res_3910_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4(lean_object* v_mvarId_3911_, lean_object* v_val_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_){
_start:
{
lean_object* v___x_3918_; 
v___x_3918_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4___redArg(v_mvarId_3911_, v_val_3912_, v___y_3914_);
return v___x_3918_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4___boxed(lean_object* v_mvarId_3919_, lean_object* v_val_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_){
_start:
{
lean_object* v_res_3926_; 
v_res_3926_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4(v_mvarId_3919_, v_val_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_);
lean_dec(v___y_3924_);
lean_dec_ref(v___y_3923_);
lean_dec(v___y_3922_);
lean_dec_ref(v___y_3921_);
return v_res_3926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4(lean_object* v_00_u03b2_3927_, lean_object* v_x_3928_, lean_object* v_x_3929_, lean_object* v_x_3930_){
_start:
{
lean_object* v___x_3931_; 
v___x_3931_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4___redArg(v_x_3928_, v_x_3929_, v_x_3930_);
return v___x_3931_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6(lean_object* v_00_u03b2_3932_, lean_object* v_x_3933_, size_t v_x_3934_, size_t v_x_3935_, lean_object* v_x_3936_, lean_object* v_x_3937_){
_start:
{
lean_object* v___x_3938_; 
v___x_3938_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg(v_x_3933_, v_x_3934_, v_x_3935_, v_x_3936_, v_x_3937_);
return v___x_3938_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___boxed(lean_object* v_00_u03b2_3939_, lean_object* v_x_3940_, lean_object* v_x_3941_, lean_object* v_x_3942_, lean_object* v_x_3943_, lean_object* v_x_3944_){
_start:
{
size_t v_x_6148__boxed_3945_; size_t v_x_6149__boxed_3946_; lean_object* v_res_3947_; 
v_x_6148__boxed_3945_ = lean_unbox_usize(v_x_3941_);
lean_dec(v_x_3941_);
v_x_6149__boxed_3946_ = lean_unbox_usize(v_x_3942_);
lean_dec(v_x_3942_);
v_res_3947_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6(v_00_u03b2_3939_, v_x_3940_, v_x_6148__boxed_3945_, v_x_6149__boxed_3946_, v_x_3943_, v_x_3944_);
return v_res_3947_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__8(lean_object* v_00_u03b2_3948_, lean_object* v_n_3949_, lean_object* v_k_3950_, lean_object* v_v_3951_){
_start:
{
lean_object* v___x_3952_; 
v___x_3952_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__8___redArg(v_n_3949_, v_k_3950_, v_v_3951_);
return v___x_3952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__9(lean_object* v_00_u03b2_3953_, size_t v_depth_3954_, lean_object* v_keys_3955_, lean_object* v_vals_3956_, lean_object* v_heq_3957_, lean_object* v_i_3958_, lean_object* v_entries_3959_){
_start:
{
lean_object* v___x_3960_; 
v___x_3960_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__9___redArg(v_depth_3954_, v_keys_3955_, v_vals_3956_, v_i_3958_, v_entries_3959_);
return v___x_3960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__9___boxed(lean_object* v_00_u03b2_3961_, lean_object* v_depth_3962_, lean_object* v_keys_3963_, lean_object* v_vals_3964_, lean_object* v_heq_3965_, lean_object* v_i_3966_, lean_object* v_entries_3967_){
_start:
{
size_t v_depth_boxed_3968_; lean_object* v_res_3969_; 
v_depth_boxed_3968_ = lean_unbox_usize(v_depth_3962_);
lean_dec(v_depth_3962_);
v_res_3969_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__9(v_00_u03b2_3961_, v_depth_boxed_3968_, v_keys_3963_, v_vals_3964_, v_heq_3965_, v_i_3966_, v_entries_3967_);
lean_dec_ref(v_vals_3964_);
lean_dec_ref(v_keys_3963_);
return v_res_3969_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__8_spec__9(lean_object* v_00_u03b2_3970_, lean_object* v_x_3971_, lean_object* v_x_3972_, lean_object* v_x_3973_, lean_object* v_x_3974_){
_start:
{
lean_object* v___x_3975_; 
v___x_3975_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__8_spec__9___redArg(v_x_3971_, v_x_3972_, v_x_3973_, v_x_3974_);
return v___x_3975_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3980_; lean_object* v___x_3981_; 
v___x_3980_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__2));
v___x_3981_ = l_Lean_stringToMessageData(v___x_3980_);
return v___x_3981_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3983_; lean_object* v___x_3984_; 
v___x_3983_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__4));
v___x_3984_ = l_Lean_stringToMessageData(v___x_3983_);
return v___x_3984_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0(lean_object* v_ctor_3985_, lean_object* v_as_3986_, size_t v_sz_3987_, size_t v_i_3988_, lean_object* v_b_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_){
_start:
{
lean_object* v_a_3996_; uint8_t v___x_4000_; 
v___x_4000_ = lean_usize_dec_lt(v_i_3988_, v_sz_3987_);
if (v___x_4000_ == 0)
{
lean_object* v___x_4001_; 
lean_dec(v_ctor_3985_);
v___x_4001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4001_, 0, v_b_3989_);
return v___x_4001_;
}
else
{
lean_object* v_a_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; uint8_t v___x_4005_; 
v_a_4002_ = lean_array_uget_borrowed(v_as_3986_, v_i_3988_);
v___x_4003_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__2));
v___x_4004_ = lean_unsigned_to_nat(3u);
v___x_4005_ = l_Lean_Expr_isAppOfArity(v_a_4002_, v___x_4003_, v___x_4004_);
if (v___x_4005_ == 0)
{
lean_object* v___x_4006_; lean_object* v___x_4007_; uint8_t v___x_4008_; 
v___x_4006_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__1));
v___x_4007_ = lean_unsigned_to_nat(4u);
v___x_4008_ = l_Lean_Expr_isAppOfArity(v_a_4002_, v___x_4006_, v___x_4007_);
if (v___x_4008_ == 0)
{
lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; 
v___x_4009_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__3);
lean_inc(v_a_4002_);
v___x_4010_ = l_Lean_MessageData_ofExpr(v_a_4002_);
v___x_4011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4011_, 0, v___x_4009_);
lean_ctor_set(v___x_4011_, 1, v___x_4010_);
v___x_4012_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__5);
v___x_4013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4013_, 0, v___x_4011_);
lean_ctor_set(v___x_4013_, 1, v___x_4012_);
lean_inc(v_ctor_3985_);
v___x_4014_ = l_Lean_MessageData_ofName(v_ctor_3985_);
v___x_4015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4015_, 0, v___x_4013_);
lean_ctor_set(v___x_4015_, 1, v___x_4014_);
v___x_4016_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0___redArg(v___x_4015_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_);
if (lean_obj_tag(v___x_4016_) == 0)
{
lean_dec_ref_known(v___x_4016_, 1);
v_a_3996_ = v_b_3989_;
goto v___jp_3995_;
}
else
{
lean_object* v_a_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4024_; 
lean_dec_ref(v_b_3989_);
lean_dec(v_ctor_3985_);
v_a_4017_ = lean_ctor_get(v___x_4016_, 0);
v_isSharedCheck_4024_ = !lean_is_exclusive(v___x_4016_);
if (v_isSharedCheck_4024_ == 0)
{
v___x_4019_ = v___x_4016_;
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_a_4017_);
lean_dec(v___x_4016_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___x_4022_; 
if (v_isShared_4020_ == 0)
{
v___x_4022_ = v___x_4019_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v_a_4017_);
v___x_4022_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
return v___x_4022_;
}
}
}
}
else
{
lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
v___x_4025_ = l_Lean_Expr_appFn_x21(v_a_4002_);
v___x_4026_ = l_Lean_Expr_appFn_x21(v___x_4025_);
lean_dec_ref(v___x_4025_);
v___x_4027_ = l_Lean_Expr_appArg_x21(v___x_4026_);
lean_dec_ref(v___x_4026_);
v___x_4028_ = l_Lean_Meta_mkHEqRefl(v___x_4027_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_);
if (lean_obj_tag(v___x_4028_) == 0)
{
lean_object* v_a_4029_; lean_object* v___x_4030_; 
v_a_4029_ = lean_ctor_get(v___x_4028_, 0);
lean_inc(v_a_4029_);
lean_dec_ref_known(v___x_4028_, 1);
v___x_4030_ = l_Lean_Expr_app___override(v_b_3989_, v_a_4029_);
v_a_3996_ = v___x_4030_;
goto v___jp_3995_;
}
else
{
lean_dec_ref(v_b_3989_);
lean_dec(v_ctor_3985_);
return v___x_4028_;
}
}
}
else
{
lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; 
v___x_4031_ = l_Lean_Expr_appFn_x21(v_a_4002_);
v___x_4032_ = l_Lean_Expr_appArg_x21(v___x_4031_);
lean_dec_ref(v___x_4031_);
v___x_4033_ = l_Lean_Meta_mkEqRefl(v___x_4032_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_);
if (lean_obj_tag(v___x_4033_) == 0)
{
lean_object* v_a_4034_; lean_object* v___x_4035_; 
v_a_4034_ = lean_ctor_get(v___x_4033_, 0);
lean_inc(v_a_4034_);
lean_dec_ref_known(v___x_4033_, 1);
v___x_4035_ = l_Lean_Expr_app___override(v_b_3989_, v_a_4034_);
v_a_3996_ = v___x_4035_;
goto v___jp_3995_;
}
else
{
lean_dec_ref(v_b_3989_);
lean_dec(v_ctor_3985_);
return v___x_4033_;
}
}
}
v___jp_3995_:
{
size_t v___x_3997_; size_t v___x_3998_; 
v___x_3997_ = ((size_t)1ULL);
v___x_3998_ = lean_usize_add(v_i_3988_, v___x_3997_);
v_i_3988_ = v___x_3998_;
v_b_3989_ = v_a_3996_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___boxed(lean_object* v_ctor_4036_, lean_object* v_as_4037_, lean_object* v_sz_4038_, lean_object* v_i_4039_, lean_object* v_b_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_){
_start:
{
size_t v_sz_boxed_4046_; size_t v_i_boxed_4047_; lean_object* v_res_4048_; 
v_sz_boxed_4046_ = lean_unbox_usize(v_sz_4038_);
lean_dec(v_sz_4038_);
v_i_boxed_4047_ = lean_unbox_usize(v_i_4039_);
lean_dec(v_i_4039_);
v_res_4048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0(v_ctor_4036_, v_as_4037_, v_sz_boxed_4046_, v_i_boxed_4047_, v_b_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_);
lean_dec(v___y_4044_);
lean_dec_ref(v___y_4043_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
lean_dec_ref(v_as_4037_);
return v_res_4048_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__0(lean_object* v___x_4049_, lean_object* v_head_4050_, lean_object* v_fs1_4051_, uint8_t v___x_4052_, uint8_t v___x_4053_, uint8_t v___x_4054_, lean_object* v_k_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_){
_start:
{
lean_object* v___x_4061_; lean_object* v___x_4062_; 
v___x_4061_ = l_Lean_Expr_getNumHeadForalls(v___x_4049_);
v___x_4062_ = l_Lean_Meta_arrowDomainsN(v___x_4061_, v___x_4049_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
if (lean_obj_tag(v___x_4062_) == 0)
{
lean_object* v_a_4063_; size_t v_sz_4064_; size_t v___x_4065_; lean_object* v___x_4066_; 
v_a_4063_ = lean_ctor_get(v___x_4062_, 0);
lean_inc(v_a_4063_);
lean_dec_ref_known(v___x_4062_, 1);
v_sz_4064_ = lean_array_size(v_a_4063_);
v___x_4065_ = ((size_t)0ULL);
lean_inc_ref(v_k_4055_);
v___x_4066_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0(v_head_4050_, v_a_4063_, v_sz_4064_, v___x_4065_, v_k_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
lean_dec(v_a_4063_);
if (lean_obj_tag(v___x_4066_) == 0)
{
lean_object* v_a_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; 
v_a_4067_ = lean_ctor_get(v___x_4066_, 0);
lean_inc(v_a_4067_);
lean_dec_ref_known(v___x_4066_, 1);
v___x_4068_ = lean_unsigned_to_nat(1u);
v___x_4069_ = lean_mk_empty_array_with_capacity(v___x_4068_);
v___x_4070_ = lean_array_push(v___x_4069_, v_k_4055_);
v___x_4071_ = l_Array_append___redArg(v_fs1_4051_, v___x_4070_);
lean_dec_ref(v___x_4070_);
v___x_4072_ = l_Lean_Meta_mkLambdaFVars(v___x_4071_, v_a_4067_, v___x_4052_, v___x_4053_, v___x_4052_, v___x_4053_, v___x_4054_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
lean_dec_ref(v___x_4071_);
return v___x_4072_;
}
else
{
lean_dec_ref(v_k_4055_);
lean_dec_ref(v_fs1_4051_);
return v___x_4066_;
}
}
else
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4080_; 
lean_dec_ref(v_k_4055_);
lean_dec_ref(v_fs1_4051_);
lean_dec(v_head_4050_);
v_a_4073_ = lean_ctor_get(v___x_4062_, 0);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4062_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4075_ = v___x_4062_;
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v___x_4062_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4078_; 
if (v_isShared_4076_ == 0)
{
v___x_4078_ = v___x_4075_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_a_4073_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
return v___x_4078_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__0___boxed(lean_object* v___x_4081_, lean_object* v_head_4082_, lean_object* v_fs1_4083_, lean_object* v___x_4084_, lean_object* v___x_4085_, lean_object* v___x_4086_, lean_object* v_k_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_){
_start:
{
uint8_t v___x_11665__boxed_4093_; uint8_t v___x_11666__boxed_4094_; uint8_t v___x_11667__boxed_4095_; lean_object* v_res_4096_; 
v___x_11665__boxed_4093_ = lean_unbox(v___x_4084_);
v___x_11666__boxed_4094_ = lean_unbox(v___x_4085_);
v___x_11667__boxed_4095_ = lean_unbox(v___x_4086_);
v_res_4096_ = l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__0(v___x_4081_, v_head_4082_, v_fs1_4083_, v___x_11665__boxed_4093_, v___x_11666__boxed_4094_, v___x_11667__boxed_4095_, v_k_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
lean_dec(v___y_4091_);
lean_dec_ref(v___y_4090_);
lean_dec(v___y_4089_);
lean_dec_ref(v___y_4088_);
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__1(lean_object* v_head_4100_, lean_object* v___x_4101_, lean_object* v___x_4102_, uint8_t v___x_4103_, uint8_t v___x_4104_, uint8_t v___x_4105_, lean_object* v_fs1_4106_, lean_object* v_x_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_){
_start:
{
lean_object* v___x_4113_; 
lean_inc(v_head_4100_);
v___x_4113_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg(v_head_4100_, v___x_4101_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_);
if (lean_obj_tag(v___x_4113_) == 0)
{
lean_object* v_a_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___f_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
v_a_4114_ = lean_ctor_get(v___x_4113_, 0);
lean_inc(v_a_4114_);
lean_dec_ref_known(v___x_4113_, 1);
lean_inc_ref(v___x_4102_);
v___x_4115_ = l_Array_append___redArg(v___x_4102_, v_fs1_4106_);
v___x_4116_ = l_Array_append___redArg(v___x_4115_, v___x_4102_);
lean_dec_ref(v___x_4102_);
v___x_4117_ = l_Array_append___redArg(v___x_4116_, v_fs1_4106_);
v___x_4118_ = l_Lean_Expr_beta(v_a_4114_, v___x_4117_);
v___x_4119_ = lean_box(v___x_4103_);
v___x_4120_ = lean_box(v___x_4104_);
v___x_4121_ = lean_box(v___x_4105_);
lean_inc_ref(v___x_4118_);
v___f_4122_ = lean_alloc_closure((void*)(l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__0___boxed), 12, 6);
lean_closure_set(v___f_4122_, 0, v___x_4118_);
lean_closure_set(v___f_4122_, 1, v_head_4100_);
lean_closure_set(v___f_4122_, 2, v_fs1_4106_);
lean_closure_set(v___f_4122_, 3, v___x_4119_);
lean_closure_set(v___f_4122_, 4, v___x_4120_);
lean_closure_set(v___f_4122_, 5, v___x_4121_);
v___x_4123_ = ((lean_object*)(l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__1___closed__1));
v___x_4124_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_4123_, v___x_4118_, v___f_4122_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_);
return v___x_4124_;
}
else
{
lean_dec_ref(v_fs1_4106_);
lean_dec_ref(v___x_4102_);
lean_dec(v_head_4100_);
return v___x_4113_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__1___boxed(lean_object* v_head_4125_, lean_object* v___x_4126_, lean_object* v___x_4127_, lean_object* v___x_4128_, lean_object* v___x_4129_, lean_object* v___x_4130_, lean_object* v_fs1_4131_, lean_object* v_x_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_){
_start:
{
uint8_t v___x_11741__boxed_4138_; uint8_t v___x_11742__boxed_4139_; uint8_t v___x_11743__boxed_4140_; lean_object* v_res_4141_; 
v___x_11741__boxed_4138_ = lean_unbox(v___x_4128_);
v___x_11742__boxed_4139_ = lean_unbox(v___x_4129_);
v___x_11743__boxed_4140_ = lean_unbox(v___x_4130_);
v_res_4141_ = l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__1(v_head_4125_, v___x_4126_, v___x_4127_, v___x_11741__boxed_4138_, v___x_11742__boxed_4139_, v___x_11743__boxed_4140_, v_fs1_4131_, v_x_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_);
lean_dec(v___y_4136_);
lean_dec_ref(v___y_4135_);
lean_dec(v___y_4134_);
lean_dec_ref(v___y_4133_);
lean_dec_ref(v_x_4132_);
return v_res_4141_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1(lean_object* v___x_4142_, lean_object* v___x_4143_, lean_object* v_tail_4144_, lean_object* v_x_4145_, lean_object* v_x_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_){
_start:
{
if (lean_obj_tag(v_x_4145_) == 0)
{
lean_object* v___x_4152_; lean_object* v___x_4153_; 
lean_dec(v_tail_4144_);
lean_dec_ref(v___x_4143_);
lean_dec_ref(v___x_4142_);
v___x_4152_ = l_List_reverse___redArg(v_x_4146_);
v___x_4153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4153_, 0, v___x_4152_);
return v___x_4153_;
}
else
{
lean_object* v_head_4154_; lean_object* v_tail_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4186_; 
v_head_4154_ = lean_ctor_get(v_x_4145_, 0);
v_tail_4155_ = lean_ctor_get(v_x_4145_, 1);
v_isSharedCheck_4186_ = !lean_is_exclusive(v_x_4145_);
if (v_isSharedCheck_4186_ == 0)
{
v___x_4157_ = v_x_4145_;
v_isShared_4158_ = v_isSharedCheck_4186_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_tail_4155_);
lean_inc(v_head_4154_);
lean_dec(v_x_4145_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4186_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v___y_4160_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; 
lean_inc(v_tail_4144_);
lean_inc(v_head_4154_);
v___x_4174_ = l_Lean_mkConst(v_head_4154_, v_tail_4144_);
v___x_4175_ = l_Lean_mkAppN(v___x_4174_, v___x_4143_);
lean_inc(v___y_4150_);
lean_inc_ref(v___y_4149_);
lean_inc(v___y_4148_);
lean_inc_ref(v___y_4147_);
v___x_4176_ = lean_infer_type(v___x_4175_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_);
if (lean_obj_tag(v___x_4176_) == 0)
{
lean_object* v_a_4177_; uint8_t v___x_4178_; uint8_t v___x_4179_; uint8_t v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___f_4184_; lean_object* v___x_4185_; 
v_a_4177_ = lean_ctor_get(v___x_4176_, 0);
lean_inc(v_a_4177_);
lean_dec_ref_known(v___x_4176_, 1);
v___x_4178_ = 0;
v___x_4179_ = 1;
v___x_4180_ = 1;
v___x_4181_ = lean_box(v___x_4178_);
v___x_4182_ = lean_box(v___x_4179_);
v___x_4183_ = lean_box(v___x_4180_);
lean_inc_ref(v___x_4143_);
lean_inc_ref(v___x_4142_);
v___f_4184_ = lean_alloc_closure((void*)(l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__1___boxed), 13, 6);
lean_closure_set(v___f_4184_, 0, v_head_4154_);
lean_closure_set(v___f_4184_, 1, v___x_4142_);
lean_closure_set(v___f_4184_, 2, v___x_4143_);
lean_closure_set(v___f_4184_, 3, v___x_4181_);
lean_closure_set(v___f_4184_, 4, v___x_4182_);
lean_closure_set(v___f_4184_, 5, v___x_4183_);
v___x_4185_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__3___redArg(v_a_4177_, v___f_4184_, v___x_4178_, v___x_4178_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_);
v___y_4160_ = v___x_4185_;
goto v___jp_4159_;
}
else
{
lean_dec(v_head_4154_);
v___y_4160_ = v___x_4176_;
goto v___jp_4159_;
}
v___jp_4159_:
{
if (lean_obj_tag(v___y_4160_) == 0)
{
lean_object* v_a_4161_; lean_object* v___x_4163_; 
v_a_4161_ = lean_ctor_get(v___y_4160_, 0);
lean_inc(v_a_4161_);
lean_dec_ref_known(v___y_4160_, 1);
if (v_isShared_4158_ == 0)
{
lean_ctor_set(v___x_4157_, 1, v_x_4146_);
lean_ctor_set(v___x_4157_, 0, v_a_4161_);
v___x_4163_ = v___x_4157_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v_a_4161_);
lean_ctor_set(v_reuseFailAlloc_4165_, 1, v_x_4146_);
v___x_4163_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
v_x_4145_ = v_tail_4155_;
v_x_4146_ = v___x_4163_;
goto _start;
}
}
else
{
lean_object* v_a_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4173_; 
lean_del_object(v___x_4157_);
lean_dec(v_tail_4155_);
lean_dec(v_x_4146_);
lean_dec(v_tail_4144_);
lean_dec_ref(v___x_4143_);
lean_dec_ref(v___x_4142_);
v_a_4166_ = lean_ctor_get(v___y_4160_, 0);
v_isSharedCheck_4173_ = !lean_is_exclusive(v___y_4160_);
if (v_isSharedCheck_4173_ == 0)
{
v___x_4168_ = v___y_4160_;
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_a_4166_);
lean_dec(v___y_4160_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v___x_4171_; 
if (v_isShared_4169_ == 0)
{
v___x_4171_ = v___x_4168_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_a_4166_);
v___x_4171_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
return v___x_4171_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___boxed(lean_object* v___x_4187_, lean_object* v___x_4188_, lean_object* v_tail_4189_, lean_object* v_x_4190_, lean_object* v_x_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_){
_start:
{
lean_object* v_res_4197_; 
v_res_4197_ = l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1(v___x_4187_, v___x_4188_, v_tail_4189_, v_x_4190_, v_x_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_);
lean_dec(v___y_4195_);
lean_dec_ref(v___y_4194_);
lean_dec(v___y_4193_);
lean_dec_ref(v___y_4192_);
return v_res_4197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__0(lean_object* v___x_4198_, lean_object* v___x_4199_, uint8_t v___x_4200_, uint8_t v___x_4201_, uint8_t v___x_4202_, lean_object* v___x_4203_, lean_object* v___x_4204_, lean_object* v_tail_4205_, lean_object* v_ctors_4206_, lean_object* v___x_4207_, lean_object* v_xs2_4208_, lean_object* v___x_4209_, lean_object* v___x_4210_, lean_object* v___x_4211_, lean_object* v___x_4212_, lean_object* v_xs1_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_){
_start:
{
lean_object* v___x_4219_; 
v___x_4219_ = l_Lean_Meta_mkLambdaFVars(v___x_4198_, v___x_4199_, v___x_4200_, v___x_4201_, v___x_4200_, v___x_4201_, v___x_4202_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
if (lean_obj_tag(v___x_4219_) == 0)
{
lean_object* v_a_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; 
v_a_4220_ = lean_ctor_get(v___x_4219_, 0);
lean_inc(v_a_4220_);
lean_dec_ref_known(v___x_4219_, 1);
v___x_4221_ = lean_box(0);
lean_inc_ref(v___x_4204_);
v___x_4222_ = l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1(v___x_4203_, v___x_4204_, v_tail_4205_, v_ctors_4206_, v___x_4221_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
if (lean_obj_tag(v___x_4222_) == 0)
{
lean_object* v_a_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; 
v_a_4223_ = lean_ctor_get(v___x_4222_, 0);
lean_inc(v_a_4223_);
lean_dec_ref_known(v___x_4222_, 1);
v___x_4224_ = l_Array_append___redArg(v___x_4207_, v_xs2_4208_);
v___x_4225_ = l_Lean_mkAppN(v___x_4209_, v___x_4224_);
v___x_4226_ = l_Lean_Meta_mkLambdaFVars(v_xs2_4208_, v___x_4225_, v___x_4200_, v___x_4201_, v___x_4200_, v___x_4201_, v___x_4202_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
if (lean_obj_tag(v___x_4226_) == 0)
{
lean_object* v_a_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; 
v_a_4227_ = lean_ctor_get(v___x_4226_, 0);
lean_inc(v_a_4227_);
lean_dec_ref_known(v___x_4226_, 1);
v___x_4228_ = l_Lean_mkConst(v___x_4210_, v___x_4211_);
v___x_4229_ = lean_array_push(v___x_4212_, v_a_4220_);
v___x_4230_ = l_Array_append___redArg(v___x_4204_, v___x_4229_);
lean_dec_ref(v___x_4229_);
v___x_4231_ = l_Array_append___redArg(v___x_4230_, v___x_4198_);
v___x_4232_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v___x_4231_, v_a_4223_);
v___x_4233_ = l_Lean_mkAppN(v___x_4228_, v___x_4232_);
lean_dec_ref(v___x_4232_);
v___x_4234_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope(v_a_4227_, v___x_4233_, v_xs1_4213_, v_xs2_4208_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
if (lean_obj_tag(v___x_4234_) == 0)
{
lean_object* v_a_4235_; lean_object* v___x_4236_; 
v_a_4235_ = lean_ctor_get(v___x_4234_, 0);
lean_inc(v_a_4235_);
lean_dec_ref_known(v___x_4234_, 1);
v___x_4236_ = l_Lean_Meta_mkLambdaFVars(v___x_4224_, v_a_4235_, v___x_4200_, v___x_4201_, v___x_4200_, v___x_4201_, v___x_4202_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
lean_dec_ref(v___x_4224_);
return v___x_4236_;
}
else
{
lean_dec_ref(v___x_4224_);
return v___x_4234_;
}
}
else
{
lean_dec_ref(v___x_4224_);
lean_dec(v_a_4223_);
lean_dec(v_a_4220_);
lean_dec_ref(v_xs1_4213_);
lean_dec_ref(v___x_4212_);
lean_dec(v___x_4211_);
lean_dec(v___x_4210_);
lean_dec_ref(v_xs2_4208_);
lean_dec_ref(v___x_4204_);
return v___x_4226_;
}
}
else
{
lean_object* v_a_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4244_; 
lean_dec(v_a_4220_);
lean_dec_ref(v_xs1_4213_);
lean_dec_ref(v___x_4212_);
lean_dec(v___x_4211_);
lean_dec(v___x_4210_);
lean_dec_ref(v___x_4209_);
lean_dec_ref(v_xs2_4208_);
lean_dec_ref(v___x_4207_);
lean_dec_ref(v___x_4204_);
v_a_4237_ = lean_ctor_get(v___x_4222_, 0);
v_isSharedCheck_4244_ = !lean_is_exclusive(v___x_4222_);
if (v_isSharedCheck_4244_ == 0)
{
v___x_4239_ = v___x_4222_;
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_a_4237_);
lean_dec(v___x_4222_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v___x_4242_; 
if (v_isShared_4240_ == 0)
{
v___x_4242_ = v___x_4239_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v_a_4237_);
v___x_4242_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
return v___x_4242_;
}
}
}
}
else
{
lean_dec_ref(v_xs1_4213_);
lean_dec_ref(v___x_4212_);
lean_dec(v___x_4211_);
lean_dec(v___x_4210_);
lean_dec_ref(v___x_4209_);
lean_dec_ref(v_xs2_4208_);
lean_dec_ref(v___x_4207_);
lean_dec(v_ctors_4206_);
lean_dec(v_tail_4205_);
lean_dec_ref(v___x_4204_);
lean_dec_ref(v___x_4203_);
return v___x_4219_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__0___boxed(lean_object** _args){
lean_object* v___x_4245_ = _args[0];
lean_object* v___x_4246_ = _args[1];
lean_object* v___x_4247_ = _args[2];
lean_object* v___x_4248_ = _args[3];
lean_object* v___x_4249_ = _args[4];
lean_object* v___x_4250_ = _args[5];
lean_object* v___x_4251_ = _args[6];
lean_object* v_tail_4252_ = _args[7];
lean_object* v_ctors_4253_ = _args[8];
lean_object* v___x_4254_ = _args[9];
lean_object* v_xs2_4255_ = _args[10];
lean_object* v___x_4256_ = _args[11];
lean_object* v___x_4257_ = _args[12];
lean_object* v___x_4258_ = _args[13];
lean_object* v___x_4259_ = _args[14];
lean_object* v_xs1_4260_ = _args[15];
lean_object* v___y_4261_ = _args[16];
lean_object* v___y_4262_ = _args[17];
lean_object* v___y_4263_ = _args[18];
lean_object* v___y_4264_ = _args[19];
lean_object* v___y_4265_ = _args[20];
_start:
{
uint8_t v___x_11905__boxed_4266_; uint8_t v___x_11906__boxed_4267_; uint8_t v___x_11907__boxed_4268_; lean_object* v_res_4269_; 
v___x_11905__boxed_4266_ = lean_unbox(v___x_4247_);
v___x_11906__boxed_4267_ = lean_unbox(v___x_4248_);
v___x_11907__boxed_4268_ = lean_unbox(v___x_4249_);
v_res_4269_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__0(v___x_4245_, v___x_4246_, v___x_11905__boxed_4266_, v___x_11906__boxed_4267_, v___x_11907__boxed_4268_, v___x_4250_, v___x_4251_, v_tail_4252_, v_ctors_4253_, v___x_4254_, v_xs2_4255_, v___x_4256_, v___x_4257_, v___x_4258_, v___x_4259_, v_xs1_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4263_);
lean_dec(v___y_4262_);
lean_dec_ref(v___y_4261_);
lean_dec_ref(v___x_4245_);
return v_res_4269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2_spec__3___redArg(lean_object* v_bs_4270_, lean_object* v_k_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_){
_start:
{
lean_object* v___x_4277_; 
v___x_4277_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_4270_, v_k_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_);
if (lean_obj_tag(v___x_4277_) == 0)
{
lean_object* v_a_4278_; lean_object* v___x_4280_; uint8_t v_isShared_4281_; uint8_t v_isSharedCheck_4285_; 
v_a_4278_ = lean_ctor_get(v___x_4277_, 0);
v_isSharedCheck_4285_ = !lean_is_exclusive(v___x_4277_);
if (v_isSharedCheck_4285_ == 0)
{
v___x_4280_ = v___x_4277_;
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
else
{
lean_inc(v_a_4278_);
lean_dec(v___x_4277_);
v___x_4280_ = lean_box(0);
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
v_resetjp_4279_:
{
lean_object* v___x_4283_; 
if (v_isShared_4281_ == 0)
{
v___x_4283_ = v___x_4280_;
goto v_reusejp_4282_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v_a_4278_);
v___x_4283_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4282_;
}
v_reusejp_4282_:
{
return v___x_4283_;
}
}
}
else
{
lean_object* v_a_4286_; lean_object* v___x_4288_; uint8_t v_isShared_4289_; uint8_t v_isSharedCheck_4293_; 
v_a_4286_ = lean_ctor_get(v___x_4277_, 0);
v_isSharedCheck_4293_ = !lean_is_exclusive(v___x_4277_);
if (v_isSharedCheck_4293_ == 0)
{
v___x_4288_ = v___x_4277_;
v_isShared_4289_ = v_isSharedCheck_4293_;
goto v_resetjp_4287_;
}
else
{
lean_inc(v_a_4286_);
lean_dec(v___x_4277_);
v___x_4288_ = lean_box(0);
v_isShared_4289_ = v_isSharedCheck_4293_;
goto v_resetjp_4287_;
}
v_resetjp_4287_:
{
lean_object* v___x_4291_; 
if (v_isShared_4289_ == 0)
{
v___x_4291_ = v___x_4288_;
goto v_reusejp_4290_;
}
else
{
lean_object* v_reuseFailAlloc_4292_; 
v_reuseFailAlloc_4292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4292_, 0, v_a_4286_);
v___x_4291_ = v_reuseFailAlloc_4292_;
goto v_reusejp_4290_;
}
v_reusejp_4290_:
{
return v___x_4291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2_spec__3___redArg___boxed(lean_object* v_bs_4294_, lean_object* v_k_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_){
_start:
{
lean_object* v_res_4301_; 
v_res_4301_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2_spec__3___redArg(v_bs_4294_, v_k_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_);
lean_dec(v___y_4299_);
lean_dec_ref(v___y_4298_);
lean_dec(v___y_4297_);
lean_dec_ref(v___y_4296_);
lean_dec_ref(v_bs_4294_);
return v_res_4301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2_spec__2(size_t v_sz_4302_, size_t v_i_4303_, lean_object* v_bs_4304_){
_start:
{
uint8_t v___x_4305_; 
v___x_4305_ = lean_usize_dec_lt(v_i_4303_, v_sz_4302_);
if (v___x_4305_ == 0)
{
return v_bs_4304_;
}
else
{
lean_object* v_v_4306_; lean_object* v___x_4307_; lean_object* v_bs_x27_4308_; lean_object* v___x_4309_; uint8_t v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; size_t v___x_4313_; size_t v___x_4314_; lean_object* v___x_4315_; 
v_v_4306_ = lean_array_uget(v_bs_4304_, v_i_4303_);
v___x_4307_ = lean_unsigned_to_nat(0u);
v_bs_x27_4308_ = lean_array_uset(v_bs_4304_, v_i_4303_, v___x_4307_);
v___x_4309_ = l_Lean_Expr_fvarId_x21(v_v_4306_);
lean_dec(v_v_4306_);
v___x_4310_ = 1;
v___x_4311_ = lean_box(v___x_4310_);
v___x_4312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4312_, 0, v___x_4309_);
lean_ctor_set(v___x_4312_, 1, v___x_4311_);
v___x_4313_ = ((size_t)1ULL);
v___x_4314_ = lean_usize_add(v_i_4303_, v___x_4313_);
v___x_4315_ = lean_array_uset(v_bs_x27_4308_, v_i_4303_, v___x_4312_);
v_i_4303_ = v___x_4314_;
v_bs_4304_ = v___x_4315_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2_spec__2___boxed(lean_object* v_sz_4317_, lean_object* v_i_4318_, lean_object* v_bs_4319_){
_start:
{
size_t v_sz_boxed_4320_; size_t v_i_boxed_4321_; lean_object* v_res_4322_; 
v_sz_boxed_4320_ = lean_unbox_usize(v_sz_4317_);
lean_dec(v_sz_4317_);
v_i_boxed_4321_ = lean_unbox_usize(v_i_4318_);
lean_dec(v_i_4318_);
v_res_4322_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2_spec__2(v_sz_boxed_4320_, v_i_boxed_4321_, v_bs_4319_);
return v_res_4322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2___redArg(lean_object* v_bs_4323_, lean_object* v_k_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_){
_start:
{
size_t v_sz_4330_; size_t v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; 
v_sz_4330_ = lean_array_size(v_bs_4323_);
v___x_4331_ = ((size_t)0ULL);
v___x_4332_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2_spec__2(v_sz_4330_, v___x_4331_, v_bs_4323_);
v___x_4333_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2_spec__3___redArg(v___x_4332_, v_k_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
lean_dec_ref(v___x_4332_);
return v___x_4333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2___redArg___boxed(lean_object* v_bs_4334_, lean_object* v_k_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_){
_start:
{
lean_object* v_res_4341_; 
v_res_4341_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2___redArg(v_bs_4334_, v_k_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_);
lean_dec(v___y_4339_);
lean_dec_ref(v___y_4338_);
lean_dec(v___y_4337_);
lean_dec_ref(v___y_4336_);
return v_res_4341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__1(lean_object* v_xs1_4342_, lean_object* v___x_4343_, lean_object* v___x_4344_, lean_object* v_numParams_4345_, lean_object* v___x_4346_, lean_object* v___x_4347_, lean_object* v_tail_4348_, lean_object* v_ctors_4349_, lean_object* v___x_4350_, lean_object* v___x_4351_, lean_object* v_xs2_4352_, lean_object* v_x_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_){
_start:
{
lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; uint8_t v___x_4371_; uint8_t v___x_4372_; uint8_t v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___f_4377_; lean_object* v___x_4378_; 
lean_inc_ref_n(v_xs1_4342_, 3);
v___x_4359_ = l_Array_append___redArg(v_xs1_4342_, v_xs2_4352_);
lean_inc_ref_n(v___x_4343_, 2);
v___x_4360_ = lean_array_push(v___x_4359_, v___x_4343_);
lean_inc(v_numParams_4345_);
v___x_4361_ = l_Array_toSubarray___redArg(v_xs1_4342_, v___x_4344_, v_numParams_4345_);
v___x_4362_ = l_Subarray_copy___redArg(v___x_4361_);
v___x_4363_ = lean_array_get_size(v_xs1_4342_);
v___x_4364_ = l_Array_toSubarray___redArg(v_xs1_4342_, v_numParams_4345_, v___x_4363_);
v___x_4365_ = l_Subarray_copy___redArg(v___x_4364_);
v___x_4366_ = lean_mk_empty_array_with_capacity(v___x_4346_);
lean_inc_ref(v___x_4366_);
v___x_4367_ = lean_array_push(v___x_4366_, v___x_4343_);
v___x_4368_ = l_Array_append___redArg(v___x_4367_, v_xs1_4342_);
lean_inc_ref(v___x_4368_);
v___x_4369_ = l_Array_append___redArg(v___x_4368_, v_xs1_4342_);
lean_inc_ref(v___x_4347_);
v___x_4370_ = l_Lean_mkAppN(v___x_4347_, v___x_4369_);
lean_dec_ref(v___x_4369_);
v___x_4371_ = 0;
v___x_4372_ = 1;
v___x_4373_ = 1;
v___x_4374_ = lean_box(v___x_4371_);
v___x_4375_ = lean_box(v___x_4372_);
v___x_4376_ = lean_box(v___x_4373_);
v___f_4377_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__0___boxed), 21, 16);
lean_closure_set(v___f_4377_, 0, v___x_4365_);
lean_closure_set(v___f_4377_, 1, v___x_4370_);
lean_closure_set(v___f_4377_, 2, v___x_4374_);
lean_closure_set(v___f_4377_, 3, v___x_4375_);
lean_closure_set(v___f_4377_, 4, v___x_4376_);
lean_closure_set(v___f_4377_, 5, v___x_4343_);
lean_closure_set(v___f_4377_, 6, v___x_4362_);
lean_closure_set(v___f_4377_, 7, v_tail_4348_);
lean_closure_set(v___f_4377_, 8, v_ctors_4349_);
lean_closure_set(v___f_4377_, 9, v___x_4368_);
lean_closure_set(v___f_4377_, 10, v_xs2_4352_);
lean_closure_set(v___f_4377_, 11, v___x_4347_);
lean_closure_set(v___f_4377_, 12, v___x_4350_);
lean_closure_set(v___f_4377_, 13, v___x_4351_);
lean_closure_set(v___f_4377_, 14, v___x_4366_);
lean_closure_set(v___f_4377_, 15, v_xs1_4342_);
v___x_4378_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2___redArg(v___x_4360_, v___f_4377_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_);
return v___x_4378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__1___boxed(lean_object** _args){
lean_object* v_xs1_4379_ = _args[0];
lean_object* v___x_4380_ = _args[1];
lean_object* v___x_4381_ = _args[2];
lean_object* v_numParams_4382_ = _args[3];
lean_object* v___x_4383_ = _args[4];
lean_object* v___x_4384_ = _args[5];
lean_object* v_tail_4385_ = _args[6];
lean_object* v_ctors_4386_ = _args[7];
lean_object* v___x_4387_ = _args[8];
lean_object* v___x_4388_ = _args[9];
lean_object* v_xs2_4389_ = _args[10];
lean_object* v_x_4390_ = _args[11];
lean_object* v___y_4391_ = _args[12];
lean_object* v___y_4392_ = _args[13];
lean_object* v___y_4393_ = _args[14];
lean_object* v___y_4394_ = _args[15];
lean_object* v___y_4395_ = _args[16];
_start:
{
lean_object* v_res_4396_; 
v_res_4396_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__1(v_xs1_4379_, v___x_4380_, v___x_4381_, v_numParams_4382_, v___x_4383_, v___x_4384_, v_tail_4385_, v_ctors_4386_, v___x_4387_, v___x_4388_, v_xs2_4389_, v_x_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_);
lean_dec(v___y_4394_);
lean_dec_ref(v___y_4393_);
lean_dec(v___y_4392_);
lean_dec_ref(v___y_4391_);
lean_dec_ref(v_x_4390_);
lean_dec(v___x_4383_);
return v_res_4396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__2(lean_object* v___x_4397_, lean_object* v___x_4398_, lean_object* v_numParams_4399_, lean_object* v___x_4400_, lean_object* v___x_4401_, lean_object* v_tail_4402_, lean_object* v_ctors_4403_, lean_object* v___x_4404_, lean_object* v___x_4405_, lean_object* v___x_4406_, lean_object* v_xs1_4407_, lean_object* v_t_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_){
_start:
{
lean_object* v___f_4414_; uint8_t v___x_4415_; lean_object* v___x_4416_; 
v___f_4414_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__1___boxed), 17, 10);
lean_closure_set(v___f_4414_, 0, v_xs1_4407_);
lean_closure_set(v___f_4414_, 1, v___x_4397_);
lean_closure_set(v___f_4414_, 2, v___x_4398_);
lean_closure_set(v___f_4414_, 3, v_numParams_4399_);
lean_closure_set(v___f_4414_, 4, v___x_4400_);
lean_closure_set(v___f_4414_, 5, v___x_4401_);
lean_closure_set(v___f_4414_, 6, v_tail_4402_);
lean_closure_set(v___f_4414_, 7, v_ctors_4403_);
lean_closure_set(v___f_4414_, 8, v___x_4404_);
lean_closure_set(v___f_4414_, 9, v___x_4405_);
v___x_4415_ = 0;
v___x_4416_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(v_t_4408_, v___x_4406_, v___f_4414_, v___x_4415_, v___x_4415_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_);
return v___x_4416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__2___boxed(lean_object** _args){
lean_object* v___x_4417_ = _args[0];
lean_object* v___x_4418_ = _args[1];
lean_object* v_numParams_4419_ = _args[2];
lean_object* v___x_4420_ = _args[3];
lean_object* v___x_4421_ = _args[4];
lean_object* v_tail_4422_ = _args[5];
lean_object* v_ctors_4423_ = _args[6];
lean_object* v___x_4424_ = _args[7];
lean_object* v___x_4425_ = _args[8];
lean_object* v___x_4426_ = _args[9];
lean_object* v_xs1_4427_ = _args[10];
lean_object* v_t_4428_ = _args[11];
lean_object* v___y_4429_ = _args[12];
lean_object* v___y_4430_ = _args[13];
lean_object* v___y_4431_ = _args[14];
lean_object* v___y_4432_ = _args[15];
lean_object* v___y_4433_ = _args[16];
_start:
{
lean_object* v_res_4434_; 
v_res_4434_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__2(v___x_4417_, v___x_4418_, v_numParams_4419_, v___x_4420_, v___x_4421_, v_tail_4422_, v_ctors_4423_, v___x_4424_, v___x_4425_, v___x_4426_, v_xs1_4427_, v_t_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_);
lean_dec(v___y_4432_);
lean_dec_ref(v___y_4431_);
lean_dec(v___y_4430_);
lean_dec_ref(v___y_4429_);
return v_res_4434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__3(lean_object* v_val_4435_, lean_object* v___x_4436_, lean_object* v___x_4437_, lean_object* v___x_4438_, lean_object* v_tail_4439_, lean_object* v___x_4440_, lean_object* v___x_4441_, lean_object* v_xs_4442_, lean_object* v_t_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_){
_start:
{
lean_object* v_numParams_4449_; lean_object* v_numIndices_4450_; lean_object* v_ctors_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___f_4457_; uint8_t v___x_4458_; lean_object* v___x_4459_; 
v_numParams_4449_ = lean_ctor_get(v_val_4435_, 1);
lean_inc(v_numParams_4449_);
v_numIndices_4450_ = lean_ctor_get(v_val_4435_, 2);
lean_inc(v_numIndices_4450_);
v_ctors_4451_ = lean_ctor_get(v_val_4435_, 4);
lean_inc(v_ctors_4451_);
lean_dec_ref(v_val_4435_);
v___x_4452_ = lean_unsigned_to_nat(0u);
v___x_4453_ = lean_array_get_borrowed(v___x_4436_, v_xs_4442_, v___x_4452_);
v___x_4454_ = lean_nat_add(v_numParams_4449_, v_numIndices_4450_);
lean_dec(v_numIndices_4450_);
v___x_4455_ = lean_nat_add(v___x_4454_, v___x_4437_);
lean_dec(v___x_4454_);
v___x_4456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4456_, 0, v___x_4455_);
lean_inc_ref(v___x_4456_);
lean_inc(v___x_4453_);
v___f_4457_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__2___boxed), 17, 10);
lean_closure_set(v___f_4457_, 0, v___x_4453_);
lean_closure_set(v___f_4457_, 1, v___x_4452_);
lean_closure_set(v___f_4457_, 2, v_numParams_4449_);
lean_closure_set(v___f_4457_, 3, v___x_4437_);
lean_closure_set(v___f_4457_, 4, v___x_4438_);
lean_closure_set(v___f_4457_, 5, v_tail_4439_);
lean_closure_set(v___f_4457_, 6, v_ctors_4451_);
lean_closure_set(v___f_4457_, 7, v___x_4440_);
lean_closure_set(v___f_4457_, 8, v___x_4441_);
lean_closure_set(v___f_4457_, 9, v___x_4456_);
v___x_4458_ = 0;
v___x_4459_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(v_t_4443_, v___x_4456_, v___f_4457_, v___x_4458_, v___x_4458_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_);
return v___x_4459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__3___boxed(lean_object* v_val_4460_, lean_object* v___x_4461_, lean_object* v___x_4462_, lean_object* v___x_4463_, lean_object* v_tail_4464_, lean_object* v___x_4465_, lean_object* v___x_4466_, lean_object* v_xs_4467_, lean_object* v_t_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_){
_start:
{
lean_object* v_res_4474_; 
v_res_4474_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__3(v_val_4460_, v___x_4461_, v___x_4462_, v___x_4463_, v_tail_4464_, v___x_4465_, v___x_4466_, v_xs_4467_, v_t_4468_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_);
lean_dec(v___y_4472_);
lean_dec_ref(v___y_4471_);
lean_dec(v___y_4470_);
lean_dec_ref(v___y_4469_);
lean_dec_ref(v_xs_4467_);
lean_dec_ref(v___x_4461_);
return v_res_4474_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__2(void){
_start:
{
lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; 
v___x_4478_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___closed__1));
v___x_4479_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__0___closed__1));
v___x_4480_ = l_Lean_Name_append(v___x_4479_, v___x_4478_);
return v___x_4480_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__4(void){
_start:
{
lean_object* v___x_4482_; lean_object* v___x_4483_; 
v___x_4482_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__3));
v___x_4483_ = l_Lean_stringToMessageData(v___x_4482_);
return v___x_4483_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__6(void){
_start:
{
lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; 
v___x_4485_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__4));
v___x_4486_ = lean_unsigned_to_nat(58u);
v___x_4487_ = lean_unsigned_to_nat(216u);
v___x_4488_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__5));
v___x_4489_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__2));
v___x_4490_ = l_mkPanicMessageWithDecl(v___x_4489_, v___x_4488_, v___x_4487_, v___x_4486_, v___x_4485_);
return v___x_4490_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__7(void){
_start:
{
lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; 
v___x_4491_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__6));
v___x_4492_ = lean_unsigned_to_nat(60u);
v___x_4493_ = lean_unsigned_to_nat(213u);
v___x_4494_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__5));
v___x_4495_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__2));
v___x_4496_ = l_mkPanicMessageWithDecl(v___x_4495_, v___x_4494_, v___x_4493_, v___x_4492_, v___x_4491_);
return v___x_4496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp(lean_object* v_indName_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_){
_start:
{
lean_object* v___x_4503_; lean_object* v_declName_4504_; lean_object* v_noConfusionTypeName_4505_; lean_object* v___x_4506_; 
v___x_4503_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__0));
lean_inc_n(v_indName_4497_, 3);
v_declName_4504_ = l_Lean_Name_str___override(v_indName_4497_, v___x_4503_);
v_noConfusionTypeName_4505_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionTypeName(v_indName_4497_);
v___x_4506_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(v_indName_4497_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_);
if (lean_obj_tag(v___x_4506_) == 0)
{
lean_object* v_a_4507_; 
v_a_4507_ = lean_ctor_get(v___x_4506_, 0);
lean_inc(v_a_4507_);
lean_dec_ref_known(v___x_4506_, 1);
if (lean_obj_tag(v_a_4507_) == 5)
{
lean_object* v_val_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; 
v_val_4508_ = lean_ctor_get(v_a_4507_, 0);
lean_inc_ref(v_val_4508_);
lean_dec_ref_known(v_a_4507_, 1);
v___x_4509_ = l_Lean_mkCasesOnName(v_indName_4497_);
lean_inc(v___x_4509_);
v___x_4510_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__1(v___x_4509_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_);
if (lean_obj_tag(v___x_4510_) == 0)
{
lean_object* v_a_4511_; lean_object* v_levelParams_4512_; lean_object* v___x_4514_; uint8_t v_isShared_4515_; uint8_t v_isSharedCheck_4679_; 
v_a_4511_ = lean_ctor_get(v___x_4510_, 0);
lean_inc(v_a_4511_);
lean_dec_ref_known(v___x_4510_, 1);
v_levelParams_4512_ = lean_ctor_get(v_a_4511_, 1);
v_isSharedCheck_4679_ = !lean_is_exclusive(v_a_4511_);
if (v_isSharedCheck_4679_ == 0)
{
lean_object* v_unused_4680_; lean_object* v_unused_4681_; 
v_unused_4680_ = lean_ctor_get(v_a_4511_, 2);
lean_dec(v_unused_4680_);
v_unused_4681_ = lean_ctor_get(v_a_4511_, 0);
lean_dec(v_unused_4681_);
v___x_4514_ = v_a_4511_;
v_isShared_4515_ = v_isSharedCheck_4679_;
goto v_resetjp_4513_;
}
else
{
lean_inc(v_levelParams_4512_);
lean_dec(v_a_4511_);
v___x_4514_ = lean_box(0);
v_isShared_4515_ = v_isSharedCheck_4679_;
goto v_resetjp_4513_;
}
v_resetjp_4513_:
{
lean_object* v___x_4516_; lean_object* v___x_4517_; 
v___x_4516_ = lean_box(0);
lean_inc(v_levelParams_4512_);
v___x_4517_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__2(v_levelParams_4512_, v___x_4516_);
if (lean_obj_tag(v___x_4517_) == 1)
{
lean_object* v_options_4518_; lean_object* v_tail_4519_; lean_object* v_inheritedTraceOptions_4520_; uint8_t v_hasTrace_4521_; lean_object* v___x_4522_; lean_object* v___y_4524_; lean_object* v___y_4525_; lean_object* v___y_4526_; lean_object* v___y_4527_; 
v_options_4518_ = lean_ctor_get(v_a_4500_, 2);
v_tail_4519_ = lean_ctor_get(v___x_4517_, 1);
lean_inc(v_tail_4519_);
v_inheritedTraceOptions_4520_ = lean_ctor_get(v_a_4500_, 13);
v_hasTrace_4521_ = lean_ctor_get_uint8(v_options_4518_, sizeof(void*)*1);
v___x_4522_ = l_Lean_instInhabitedExpr;
if (v_hasTrace_4521_ == 0)
{
v___y_4524_ = v_a_4498_;
v___y_4525_ = v_a_4499_;
v___y_4526_ = v_a_4500_;
v___y_4527_ = v_a_4501_;
goto v___jp_4523_;
}
else
{
lean_object* v___x_4670_; lean_object* v___x_4671_; uint8_t v___x_4672_; 
v___x_4670_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___closed__1));
v___x_4671_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__2, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__2_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__2);
v___x_4672_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4520_, v_options_4518_, v___x_4671_);
if (v___x_4672_ == 0)
{
v___y_4524_ = v_a_4498_;
v___y_4525_ = v_a_4499_;
v___y_4526_ = v_a_4500_;
v___y_4527_ = v_a_4501_;
goto v___jp_4523_;
}
else
{
lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; 
v___x_4673_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__4, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__4_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__4);
lean_inc(v_declName_4504_);
v___x_4674_ = l_Lean_MessageData_ofName(v_declName_4504_);
v___x_4675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4675_, 0, v___x_4673_);
lean_ctor_set(v___x_4675_, 1, v___x_4674_);
v___x_4676_ = l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0(v___x_4670_, v___x_4675_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_);
if (lean_obj_tag(v___x_4676_) == 0)
{
lean_dec_ref_known(v___x_4676_, 1);
v___y_4524_ = v_a_4498_;
v___y_4525_ = v_a_4499_;
v___y_4526_ = v_a_4500_;
v___y_4527_ = v_a_4501_;
goto v___jp_4523_;
}
else
{
lean_dec(v_tail_4519_);
lean_dec_ref_known(v___x_4517_, 2);
lean_del_object(v___x_4514_);
lean_dec(v_levelParams_4512_);
lean_dec(v___x_4509_);
lean_dec_ref(v_val_4508_);
lean_dec(v_noConfusionTypeName_4505_);
lean_dec(v_declName_4504_);
return v___x_4676_;
}
}
}
v___jp_4523_:
{
lean_object* v___x_4528_; lean_object* v___x_4529_; 
lean_inc_ref(v___x_4517_);
v___x_4528_ = l_Lean_mkConst(v_noConfusionTypeName_4505_, v___x_4517_);
lean_inc(v___y_4527_);
lean_inc_ref(v___y_4526_);
lean_inc(v___y_4525_);
lean_inc_ref(v___y_4524_);
lean_inc_ref(v___x_4528_);
v___x_4529_ = lean_infer_type(v___x_4528_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_);
if (lean_obj_tag(v___x_4529_) == 0)
{
lean_object* v_a_4530_; lean_object* v___x_4531_; lean_object* v___f_4532_; lean_object* v___x_4533_; uint8_t v___x_4534_; lean_object* v___x_4535_; 
v_a_4530_ = lean_ctor_get(v___x_4529_, 0);
lean_inc(v_a_4530_);
lean_dec_ref_known(v___x_4529_, 1);
v___x_4531_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_val_4508_);
v___f_4532_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__3___boxed), 14, 7);
lean_closure_set(v___f_4532_, 0, v_val_4508_);
lean_closure_set(v___f_4532_, 1, v___x_4522_);
lean_closure_set(v___f_4532_, 2, v___x_4531_);
lean_closure_set(v___f_4532_, 3, v___x_4528_);
lean_closure_set(v___f_4532_, 4, v_tail_4519_);
lean_closure_set(v___f_4532_, 5, v___x_4509_);
lean_closure_set(v___f_4532_, 6, v___x_4517_);
v___x_4533_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__1));
v___x_4534_ = 0;
v___x_4535_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(v_a_4530_, v___x_4533_, v___f_4532_, v___x_4534_, v___x_4534_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_);
if (lean_obj_tag(v___x_4535_) == 0)
{
lean_object* v_a_4536_; lean_object* v___x_4537_; 
v_a_4536_ = lean_ctor_get(v___x_4535_, 0);
lean_inc_n(v_a_4536_, 2);
lean_dec_ref_known(v___x_4535_, 1);
lean_inc(v___y_4527_);
lean_inc_ref(v___y_4526_);
lean_inc(v___y_4525_);
lean_inc_ref(v___y_4524_);
v___x_4537_ = lean_infer_type(v_a_4536_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_);
if (lean_obj_tag(v___x_4537_) == 0)
{
lean_object* v_a_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v_a_4541_; lean_object* v___x_4543_; uint8_t v_isShared_4544_; uint8_t v_isSharedCheck_4645_; 
v_a_4538_ = lean_ctor_get(v___x_4537_, 0);
lean_inc(v_a_4538_);
lean_dec_ref_known(v___x_4537_, 1);
v___x_4539_ = lean_box(1);
lean_inc(v_declName_4504_);
v___x_4540_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__6___redArg(v_declName_4504_, v_levelParams_4512_, v_a_4538_, v_a_4536_, v___x_4539_, v___y_4527_);
v_a_4541_ = lean_ctor_get(v___x_4540_, 0);
v_isSharedCheck_4645_ = !lean_is_exclusive(v___x_4540_);
if (v_isSharedCheck_4645_ == 0)
{
v___x_4543_ = v___x_4540_;
v_isShared_4544_ = v_isSharedCheck_4645_;
goto v_resetjp_4542_;
}
else
{
lean_inc(v_a_4541_);
lean_dec(v___x_4540_);
v___x_4543_ = lean_box(0);
v_isShared_4544_ = v_isSharedCheck_4645_;
goto v_resetjp_4542_;
}
v_resetjp_4542_:
{
lean_object* v___x_4546_; 
if (v_isShared_4544_ == 0)
{
lean_ctor_set_tag(v___x_4543_, 1);
v___x_4546_ = v___x_4543_;
goto v_reusejp_4545_;
}
else
{
lean_object* v_reuseFailAlloc_4644_; 
v_reuseFailAlloc_4644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4644_, 0, v_a_4541_);
v___x_4546_ = v_reuseFailAlloc_4644_;
goto v_reusejp_4545_;
}
v_reusejp_4545_:
{
lean_object* v___x_4547_; 
v___x_4547_ = l_Lean_addDecl(v___x_4546_, v___x_4534_, v___y_4526_, v___y_4527_);
if (lean_obj_tag(v___x_4547_) == 0)
{
lean_object* v___x_4548_; lean_object* v___x_4550_; uint8_t v_isShared_4551_; uint8_t v_isSharedCheck_4642_; 
lean_dec_ref_known(v___x_4547_, 1);
lean_inc(v_declName_4504_);
v___x_4548_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7(v_declName_4504_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_);
v_isSharedCheck_4642_ = !lean_is_exclusive(v___x_4548_);
if (v_isSharedCheck_4642_ == 0)
{
lean_object* v_unused_4643_; 
v_unused_4643_ = lean_ctor_get(v___x_4548_, 0);
lean_dec(v_unused_4643_);
v___x_4550_ = v___x_4548_;
v_isShared_4551_ = v_isSharedCheck_4642_;
goto v_resetjp_4549_;
}
else
{
lean_dec(v___x_4548_);
v___x_4550_ = lean_box(0);
v_isShared_4551_ = v_isSharedCheck_4642_;
goto v_resetjp_4549_;
}
v_resetjp_4549_:
{
lean_object* v___x_4552_; lean_object* v_numParams_4553_; lean_object* v_numIndices_4554_; lean_object* v_env_4555_; lean_object* v_nextMacroScope_4556_; lean_object* v_ngen_4557_; lean_object* v_auxDeclNGen_4558_; lean_object* v_traceState_4559_; lean_object* v_messages_4560_; lean_object* v_infoState_4561_; lean_object* v_snapshotTasks_4562_; lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4640_; 
v___x_4552_ = lean_st_ref_take(v___y_4527_);
v_numParams_4553_ = lean_ctor_get(v_val_4508_, 1);
lean_inc(v_numParams_4553_);
v_numIndices_4554_ = lean_ctor_get(v_val_4508_, 2);
lean_inc(v_numIndices_4554_);
lean_dec_ref(v_val_4508_);
v_env_4555_ = lean_ctor_get(v___x_4552_, 0);
v_nextMacroScope_4556_ = lean_ctor_get(v___x_4552_, 1);
v_ngen_4557_ = lean_ctor_get(v___x_4552_, 2);
v_auxDeclNGen_4558_ = lean_ctor_get(v___x_4552_, 3);
v_traceState_4559_ = lean_ctor_get(v___x_4552_, 4);
v_messages_4560_ = lean_ctor_get(v___x_4552_, 6);
v_infoState_4561_ = lean_ctor_get(v___x_4552_, 7);
v_snapshotTasks_4562_ = lean_ctor_get(v___x_4552_, 8);
v_isSharedCheck_4640_ = !lean_is_exclusive(v___x_4552_);
if (v_isSharedCheck_4640_ == 0)
{
lean_object* v_unused_4641_; 
v_unused_4641_ = lean_ctor_get(v___x_4552_, 5);
lean_dec(v_unused_4641_);
v___x_4564_ = v___x_4552_;
v_isShared_4565_ = v_isSharedCheck_4640_;
goto v_resetjp_4563_;
}
else
{
lean_inc(v_snapshotTasks_4562_);
lean_inc(v_infoState_4561_);
lean_inc(v_messages_4560_);
lean_inc(v_traceState_4559_);
lean_inc(v_auxDeclNGen_4558_);
lean_inc(v_ngen_4557_);
lean_inc(v_nextMacroScope_4556_);
lean_inc(v_env_4555_);
lean_dec(v___x_4552_);
v___x_4564_ = lean_box(0);
v_isShared_4565_ = v_isSharedCheck_4640_;
goto v_resetjp_4563_;
}
v_resetjp_4563_:
{
lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4580_; 
v___x_4566_ = lean_unsigned_to_nat(3u);
v___x_4567_ = lean_nat_add(v_numParams_4553_, v_numIndices_4554_);
v___x_4568_ = lean_nat_add(v___x_4567_, v___x_4531_);
lean_dec(v___x_4567_);
v___x_4569_ = lean_nat_mul(v___x_4566_, v___x_4568_);
lean_dec(v___x_4568_);
v___x_4570_ = lean_nat_add(v___x_4531_, v___x_4569_);
lean_dec(v___x_4569_);
v___x_4571_ = lean_nat_add(v___x_4531_, v_numParams_4553_);
v___x_4572_ = lean_nat_add(v___x_4571_, v_numIndices_4554_);
lean_dec(v___x_4571_);
v___x_4573_ = lean_unsigned_to_nat(2u);
v___x_4574_ = lean_nat_mul(v___x_4573_, v_numParams_4553_);
lean_dec(v_numParams_4553_);
v___x_4575_ = lean_nat_add(v___x_4531_, v___x_4574_);
lean_dec(v___x_4574_);
v___x_4576_ = lean_nat_mul(v___x_4573_, v_numIndices_4554_);
lean_dec(v_numIndices_4554_);
v___x_4577_ = lean_nat_add(v___x_4575_, v___x_4576_);
lean_dec(v___x_4576_);
lean_dec(v___x_4575_);
v___x_4578_ = lean_nat_add(v___x_4577_, v___x_4531_);
lean_dec(v___x_4577_);
if (v_isShared_4515_ == 0)
{
lean_ctor_set(v___x_4514_, 2, v___x_4578_);
lean_ctor_set(v___x_4514_, 1, v___x_4572_);
lean_ctor_set(v___x_4514_, 0, v___x_4570_);
v___x_4580_ = v___x_4514_;
goto v_reusejp_4579_;
}
else
{
lean_object* v_reuseFailAlloc_4639_; 
v_reuseFailAlloc_4639_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4639_, 0, v___x_4570_);
lean_ctor_set(v_reuseFailAlloc_4639_, 1, v___x_4572_);
lean_ctor_set(v_reuseFailAlloc_4639_, 2, v___x_4578_);
v___x_4580_ = v_reuseFailAlloc_4639_;
goto v_reusejp_4579_;
}
v_reusejp_4579_:
{
lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4584_; 
lean_inc(v_declName_4504_);
v___x_4581_ = l_Lean_markNoConfusion(v_env_4555_, v_declName_4504_, v___x_4580_);
v___x_4582_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2);
if (v_isShared_4565_ == 0)
{
lean_ctor_set(v___x_4564_, 5, v___x_4582_);
lean_ctor_set(v___x_4564_, 0, v___x_4581_);
v___x_4584_ = v___x_4564_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4638_; 
v_reuseFailAlloc_4638_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4638_, 0, v___x_4581_);
lean_ctor_set(v_reuseFailAlloc_4638_, 1, v_nextMacroScope_4556_);
lean_ctor_set(v_reuseFailAlloc_4638_, 2, v_ngen_4557_);
lean_ctor_set(v_reuseFailAlloc_4638_, 3, v_auxDeclNGen_4558_);
lean_ctor_set(v_reuseFailAlloc_4638_, 4, v_traceState_4559_);
lean_ctor_set(v_reuseFailAlloc_4638_, 5, v___x_4582_);
lean_ctor_set(v_reuseFailAlloc_4638_, 6, v_messages_4560_);
lean_ctor_set(v_reuseFailAlloc_4638_, 7, v_infoState_4561_);
lean_ctor_set(v_reuseFailAlloc_4638_, 8, v_snapshotTasks_4562_);
v___x_4584_ = v_reuseFailAlloc_4638_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v_mctx_4587_; lean_object* v_zetaDeltaFVarIds_4588_; lean_object* v_postponed_4589_; lean_object* v_diag_4590_; lean_object* v___x_4592_; uint8_t v_isShared_4593_; uint8_t v_isSharedCheck_4636_; 
v___x_4585_ = lean_st_ref_put(v___y_4527_, v___x_4584_);
v___x_4586_ = lean_st_ref_take(v___y_4525_);
v_mctx_4587_ = lean_ctor_get(v___x_4586_, 0);
v_zetaDeltaFVarIds_4588_ = lean_ctor_get(v___x_4586_, 2);
v_postponed_4589_ = lean_ctor_get(v___x_4586_, 3);
v_diag_4590_ = lean_ctor_get(v___x_4586_, 4);
v_isSharedCheck_4636_ = !lean_is_exclusive(v___x_4586_);
if (v_isSharedCheck_4636_ == 0)
{
lean_object* v_unused_4637_; 
v_unused_4637_ = lean_ctor_get(v___x_4586_, 1);
lean_dec(v_unused_4637_);
v___x_4592_ = v___x_4586_;
v_isShared_4593_ = v_isSharedCheck_4636_;
goto v_resetjp_4591_;
}
else
{
lean_inc(v_diag_4590_);
lean_inc(v_postponed_4589_);
lean_inc(v_zetaDeltaFVarIds_4588_);
lean_inc(v_mctx_4587_);
lean_dec(v___x_4586_);
v___x_4592_ = lean_box(0);
v_isShared_4593_ = v_isSharedCheck_4636_;
goto v_resetjp_4591_;
}
v_resetjp_4591_:
{
lean_object* v___x_4594_; lean_object* v___x_4596_; 
v___x_4594_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3);
if (v_isShared_4593_ == 0)
{
lean_ctor_set(v___x_4592_, 1, v___x_4594_);
v___x_4596_ = v___x_4592_;
goto v_reusejp_4595_;
}
else
{
lean_object* v_reuseFailAlloc_4635_; 
v_reuseFailAlloc_4635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4635_, 0, v_mctx_4587_);
lean_ctor_set(v_reuseFailAlloc_4635_, 1, v___x_4594_);
lean_ctor_set(v_reuseFailAlloc_4635_, 2, v_zetaDeltaFVarIds_4588_);
lean_ctor_set(v_reuseFailAlloc_4635_, 3, v_postponed_4589_);
lean_ctor_set(v_reuseFailAlloc_4635_, 4, v_diag_4590_);
v___x_4596_ = v_reuseFailAlloc_4635_;
goto v_reusejp_4595_;
}
v_reusejp_4595_:
{
lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v_env_4599_; lean_object* v_nextMacroScope_4600_; lean_object* v_ngen_4601_; lean_object* v_auxDeclNGen_4602_; lean_object* v_traceState_4603_; lean_object* v_messages_4604_; lean_object* v_infoState_4605_; lean_object* v_snapshotTasks_4606_; lean_object* v___x_4608_; uint8_t v_isShared_4609_; uint8_t v_isSharedCheck_4633_; 
v___x_4597_ = lean_st_ref_put(v___y_4525_, v___x_4596_);
v___x_4598_ = lean_st_ref_take(v___y_4527_);
v_env_4599_ = lean_ctor_get(v___x_4598_, 0);
v_nextMacroScope_4600_ = lean_ctor_get(v___x_4598_, 1);
v_ngen_4601_ = lean_ctor_get(v___x_4598_, 2);
v_auxDeclNGen_4602_ = lean_ctor_get(v___x_4598_, 3);
v_traceState_4603_ = lean_ctor_get(v___x_4598_, 4);
v_messages_4604_ = lean_ctor_get(v___x_4598_, 6);
v_infoState_4605_ = lean_ctor_get(v___x_4598_, 7);
v_snapshotTasks_4606_ = lean_ctor_get(v___x_4598_, 8);
v_isSharedCheck_4633_ = !lean_is_exclusive(v___x_4598_);
if (v_isSharedCheck_4633_ == 0)
{
lean_object* v_unused_4634_; 
v_unused_4634_ = lean_ctor_get(v___x_4598_, 5);
lean_dec(v_unused_4634_);
v___x_4608_ = v___x_4598_;
v_isShared_4609_ = v_isSharedCheck_4633_;
goto v_resetjp_4607_;
}
else
{
lean_inc(v_snapshotTasks_4606_);
lean_inc(v_infoState_4605_);
lean_inc(v_messages_4604_);
lean_inc(v_traceState_4603_);
lean_inc(v_auxDeclNGen_4602_);
lean_inc(v_ngen_4601_);
lean_inc(v_nextMacroScope_4600_);
lean_inc(v_env_4599_);
lean_dec(v___x_4598_);
v___x_4608_ = lean_box(0);
v_isShared_4609_ = v_isSharedCheck_4633_;
goto v_resetjp_4607_;
}
v_resetjp_4607_:
{
lean_object* v___x_4610_; lean_object* v___x_4612_; 
v___x_4610_ = l_Lean_addProtected(v_env_4599_, v_declName_4504_);
if (v_isShared_4609_ == 0)
{
lean_ctor_set(v___x_4608_, 5, v___x_4582_);
lean_ctor_set(v___x_4608_, 0, v___x_4610_);
v___x_4612_ = v___x_4608_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4632_; 
v_reuseFailAlloc_4632_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4632_, 0, v___x_4610_);
lean_ctor_set(v_reuseFailAlloc_4632_, 1, v_nextMacroScope_4600_);
lean_ctor_set(v_reuseFailAlloc_4632_, 2, v_ngen_4601_);
lean_ctor_set(v_reuseFailAlloc_4632_, 3, v_auxDeclNGen_4602_);
lean_ctor_set(v_reuseFailAlloc_4632_, 4, v_traceState_4603_);
lean_ctor_set(v_reuseFailAlloc_4632_, 5, v___x_4582_);
lean_ctor_set(v_reuseFailAlloc_4632_, 6, v_messages_4604_);
lean_ctor_set(v_reuseFailAlloc_4632_, 7, v_infoState_4605_);
lean_ctor_set(v_reuseFailAlloc_4632_, 8, v_snapshotTasks_4606_);
v___x_4612_ = v_reuseFailAlloc_4632_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v_mctx_4615_; lean_object* v_zetaDeltaFVarIds_4616_; lean_object* v_postponed_4617_; lean_object* v_diag_4618_; lean_object* v___x_4620_; uint8_t v_isShared_4621_; uint8_t v_isSharedCheck_4630_; 
v___x_4613_ = lean_st_ref_put(v___y_4527_, v___x_4612_);
v___x_4614_ = lean_st_ref_take(v___y_4525_);
v_mctx_4615_ = lean_ctor_get(v___x_4614_, 0);
v_zetaDeltaFVarIds_4616_ = lean_ctor_get(v___x_4614_, 2);
v_postponed_4617_ = lean_ctor_get(v___x_4614_, 3);
v_diag_4618_ = lean_ctor_get(v___x_4614_, 4);
v_isSharedCheck_4630_ = !lean_is_exclusive(v___x_4614_);
if (v_isSharedCheck_4630_ == 0)
{
lean_object* v_unused_4631_; 
v_unused_4631_ = lean_ctor_get(v___x_4614_, 1);
lean_dec(v_unused_4631_);
v___x_4620_ = v___x_4614_;
v_isShared_4621_ = v_isSharedCheck_4630_;
goto v_resetjp_4619_;
}
else
{
lean_inc(v_diag_4618_);
lean_inc(v_postponed_4617_);
lean_inc(v_zetaDeltaFVarIds_4616_);
lean_inc(v_mctx_4615_);
lean_dec(v___x_4614_);
v___x_4620_ = lean_box(0);
v_isShared_4621_ = v_isSharedCheck_4630_;
goto v_resetjp_4619_;
}
v_resetjp_4619_:
{
lean_object* v___x_4623_; 
if (v_isShared_4621_ == 0)
{
lean_ctor_set(v___x_4620_, 1, v___x_4594_);
v___x_4623_ = v___x_4620_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4629_; 
v_reuseFailAlloc_4629_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4629_, 0, v_mctx_4615_);
lean_ctor_set(v_reuseFailAlloc_4629_, 1, v___x_4594_);
lean_ctor_set(v_reuseFailAlloc_4629_, 2, v_zetaDeltaFVarIds_4616_);
lean_ctor_set(v_reuseFailAlloc_4629_, 3, v_postponed_4617_);
lean_ctor_set(v_reuseFailAlloc_4629_, 4, v_diag_4618_);
v___x_4623_ = v_reuseFailAlloc_4629_;
goto v_reusejp_4622_;
}
v_reusejp_4622_:
{
lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4627_; 
v___x_4624_ = lean_st_ref_put(v___y_4525_, v___x_4623_);
v___x_4625_ = lean_box(0);
if (v_isShared_4551_ == 0)
{
lean_ctor_set(v___x_4550_, 0, v___x_4625_);
v___x_4627_ = v___x_4550_;
goto v_reusejp_4626_;
}
else
{
lean_object* v_reuseFailAlloc_4628_; 
v_reuseFailAlloc_4628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4628_, 0, v___x_4625_);
v___x_4627_ = v_reuseFailAlloc_4628_;
goto v_reusejp_4626_;
}
v_reusejp_4626_:
{
return v___x_4627_;
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
}
}
else
{
lean_del_object(v___x_4514_);
lean_dec_ref(v_val_4508_);
lean_dec(v_declName_4504_);
return v___x_4547_;
}
}
}
}
else
{
lean_object* v_a_4646_; lean_object* v___x_4648_; uint8_t v_isShared_4649_; uint8_t v_isSharedCheck_4653_; 
lean_dec(v_a_4536_);
lean_del_object(v___x_4514_);
lean_dec(v_levelParams_4512_);
lean_dec_ref(v_val_4508_);
lean_dec(v_declName_4504_);
v_a_4646_ = lean_ctor_get(v___x_4537_, 0);
v_isSharedCheck_4653_ = !lean_is_exclusive(v___x_4537_);
if (v_isSharedCheck_4653_ == 0)
{
v___x_4648_ = v___x_4537_;
v_isShared_4649_ = v_isSharedCheck_4653_;
goto v_resetjp_4647_;
}
else
{
lean_inc(v_a_4646_);
lean_dec(v___x_4537_);
v___x_4648_ = lean_box(0);
v_isShared_4649_ = v_isSharedCheck_4653_;
goto v_resetjp_4647_;
}
v_resetjp_4647_:
{
lean_object* v___x_4651_; 
if (v_isShared_4649_ == 0)
{
v___x_4651_ = v___x_4648_;
goto v_reusejp_4650_;
}
else
{
lean_object* v_reuseFailAlloc_4652_; 
v_reuseFailAlloc_4652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4652_, 0, v_a_4646_);
v___x_4651_ = v_reuseFailAlloc_4652_;
goto v_reusejp_4650_;
}
v_reusejp_4650_:
{
return v___x_4651_;
}
}
}
}
else
{
lean_object* v_a_4654_; lean_object* v___x_4656_; uint8_t v_isShared_4657_; uint8_t v_isSharedCheck_4661_; 
lean_del_object(v___x_4514_);
lean_dec(v_levelParams_4512_);
lean_dec_ref(v_val_4508_);
lean_dec(v_declName_4504_);
v_a_4654_ = lean_ctor_get(v___x_4535_, 0);
v_isSharedCheck_4661_ = !lean_is_exclusive(v___x_4535_);
if (v_isSharedCheck_4661_ == 0)
{
v___x_4656_ = v___x_4535_;
v_isShared_4657_ = v_isSharedCheck_4661_;
goto v_resetjp_4655_;
}
else
{
lean_inc(v_a_4654_);
lean_dec(v___x_4535_);
v___x_4656_ = lean_box(0);
v_isShared_4657_ = v_isSharedCheck_4661_;
goto v_resetjp_4655_;
}
v_resetjp_4655_:
{
lean_object* v___x_4659_; 
if (v_isShared_4657_ == 0)
{
v___x_4659_ = v___x_4656_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4660_; 
v_reuseFailAlloc_4660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4660_, 0, v_a_4654_);
v___x_4659_ = v_reuseFailAlloc_4660_;
goto v_reusejp_4658_;
}
v_reusejp_4658_:
{
return v___x_4659_;
}
}
}
}
else
{
lean_object* v_a_4662_; lean_object* v___x_4664_; uint8_t v_isShared_4665_; uint8_t v_isSharedCheck_4669_; 
lean_dec_ref(v___x_4528_);
lean_dec(v_tail_4519_);
lean_dec_ref_known(v___x_4517_, 2);
lean_del_object(v___x_4514_);
lean_dec(v_levelParams_4512_);
lean_dec(v___x_4509_);
lean_dec_ref(v_val_4508_);
lean_dec(v_declName_4504_);
v_a_4662_ = lean_ctor_get(v___x_4529_, 0);
v_isSharedCheck_4669_ = !lean_is_exclusive(v___x_4529_);
if (v_isSharedCheck_4669_ == 0)
{
v___x_4664_ = v___x_4529_;
v_isShared_4665_ = v_isSharedCheck_4669_;
goto v_resetjp_4663_;
}
else
{
lean_inc(v_a_4662_);
lean_dec(v___x_4529_);
v___x_4664_ = lean_box(0);
v_isShared_4665_ = v_isSharedCheck_4669_;
goto v_resetjp_4663_;
}
v_resetjp_4663_:
{
lean_object* v___x_4667_; 
if (v_isShared_4665_ == 0)
{
v___x_4667_ = v___x_4664_;
goto v_reusejp_4666_;
}
else
{
lean_object* v_reuseFailAlloc_4668_; 
v_reuseFailAlloc_4668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4668_, 0, v_a_4662_);
v___x_4667_ = v_reuseFailAlloc_4668_;
goto v_reusejp_4666_;
}
v_reusejp_4666_:
{
return v___x_4667_;
}
}
}
}
}
else
{
lean_object* v___x_4677_; lean_object* v___x_4678_; 
lean_dec(v___x_4517_);
lean_del_object(v___x_4514_);
lean_dec(v_levelParams_4512_);
lean_dec(v___x_4509_);
lean_dec_ref(v_val_4508_);
lean_dec(v_noConfusionTypeName_4505_);
lean_dec(v_declName_4504_);
v___x_4677_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__6, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__6_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__6);
v___x_4678_ = l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8(v___x_4677_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_);
return v___x_4678_;
}
}
}
else
{
lean_object* v_a_4682_; lean_object* v___x_4684_; uint8_t v_isShared_4685_; uint8_t v_isSharedCheck_4689_; 
lean_dec(v___x_4509_);
lean_dec_ref(v_val_4508_);
lean_dec(v_noConfusionTypeName_4505_);
lean_dec(v_declName_4504_);
v_a_4682_ = lean_ctor_get(v___x_4510_, 0);
v_isSharedCheck_4689_ = !lean_is_exclusive(v___x_4510_);
if (v_isSharedCheck_4689_ == 0)
{
v___x_4684_ = v___x_4510_;
v_isShared_4685_ = v_isSharedCheck_4689_;
goto v_resetjp_4683_;
}
else
{
lean_inc(v_a_4682_);
lean_dec(v___x_4510_);
v___x_4684_ = lean_box(0);
v_isShared_4685_ = v_isSharedCheck_4689_;
goto v_resetjp_4683_;
}
v_resetjp_4683_:
{
lean_object* v___x_4687_; 
if (v_isShared_4685_ == 0)
{
v___x_4687_ = v___x_4684_;
goto v_reusejp_4686_;
}
else
{
lean_object* v_reuseFailAlloc_4688_; 
v_reuseFailAlloc_4688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4688_, 0, v_a_4682_);
v___x_4687_ = v_reuseFailAlloc_4688_;
goto v_reusejp_4686_;
}
v_reusejp_4686_:
{
return v___x_4687_;
}
}
}
}
else
{
lean_object* v___x_4690_; lean_object* v___x_4691_; 
lean_dec(v_a_4507_);
lean_dec(v_noConfusionTypeName_4505_);
lean_dec(v_declName_4504_);
lean_dec(v_indName_4497_);
v___x_4690_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__7, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__7_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__7);
v___x_4691_ = l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8(v___x_4690_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_);
return v___x_4691_;
}
}
else
{
lean_object* v_a_4692_; lean_object* v___x_4694_; uint8_t v_isShared_4695_; uint8_t v_isSharedCheck_4699_; 
lean_dec(v_noConfusionTypeName_4505_);
lean_dec(v_declName_4504_);
lean_dec(v_indName_4497_);
v_a_4692_ = lean_ctor_get(v___x_4506_, 0);
v_isSharedCheck_4699_ = !lean_is_exclusive(v___x_4506_);
if (v_isSharedCheck_4699_ == 0)
{
v___x_4694_ = v___x_4506_;
v_isShared_4695_ = v_isSharedCheck_4699_;
goto v_resetjp_4693_;
}
else
{
lean_inc(v_a_4692_);
lean_dec(v___x_4506_);
v___x_4694_ = lean_box(0);
v_isShared_4695_ = v_isSharedCheck_4699_;
goto v_resetjp_4693_;
}
v_resetjp_4693_:
{
lean_object* v___x_4697_; 
if (v_isShared_4695_ == 0)
{
v___x_4697_ = v___x_4694_;
goto v_reusejp_4696_;
}
else
{
lean_object* v_reuseFailAlloc_4698_; 
v_reuseFailAlloc_4698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4698_, 0, v_a_4692_);
v___x_4697_ = v_reuseFailAlloc_4698_;
goto v_reusejp_4696_;
}
v_reusejp_4696_:
{
return v___x_4697_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___boxed(lean_object* v_indName_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_){
_start:
{
lean_object* v_res_4706_; 
v_res_4706_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp(v_indName_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_);
lean_dec(v_a_4704_);
lean_dec_ref(v_a_4703_);
lean_dec(v_a_4702_);
lean_dec_ref(v_a_4701_);
return v_res_4706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2_spec__3(lean_object* v_00_u03b1_4707_, lean_object* v_bs_4708_, lean_object* v_k_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_){
_start:
{
lean_object* v___x_4715_; 
v___x_4715_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2_spec__3___redArg(v_bs_4708_, v_k_4709_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_);
return v___x_4715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4716_, lean_object* v_bs_4717_, lean_object* v_k_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_){
_start:
{
lean_object* v_res_4724_; 
v_res_4724_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2_spec__3(v_00_u03b1_4716_, v_bs_4717_, v_k_4718_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_);
lean_dec(v___y_4722_);
lean_dec_ref(v___y_4721_);
lean_dec(v___y_4720_);
lean_dec_ref(v___y_4719_);
lean_dec_ref(v_bs_4717_);
return v_res_4724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2(lean_object* v_00_u03b1_4725_, lean_object* v_bs_4726_, lean_object* v_k_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_){
_start:
{
lean_object* v___x_4733_; 
v___x_4733_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2___redArg(v_bs_4726_, v_k_4727_, v___y_4728_, v___y_4729_, v___y_4730_, v___y_4731_);
return v___x_4733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2___boxed(lean_object* v_00_u03b1_4734_, lean_object* v_bs_4735_, lean_object* v_k_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_){
_start:
{
lean_object* v_res_4742_; 
v_res_4742_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2(v_00_u03b1_4734_, v_bs_4735_, v_k_4736_, v___y_4737_, v___y_4738_, v___y_4739_, v___y_4740_);
lean_dec(v___y_4740_);
lean_dec_ref(v___y_4739_);
lean_dec(v___y_4738_);
lean_dec_ref(v___y_4737_);
return v_res_4742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1(lean_object* v_as_4743_, size_t v_sz_4744_, size_t v_i_4745_, lean_object* v_b_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_){
_start:
{
lean_object* v_a_4753_; uint8_t v___x_4757_; 
v___x_4757_ = lean_usize_dec_lt(v_i_4745_, v_sz_4744_);
if (v___x_4757_ == 0)
{
lean_object* v___x_4758_; 
v___x_4758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4758_, 0, v_b_4746_);
return v___x_4758_;
}
else
{
lean_object* v___x_4759_; 
lean_inc(v___y_4750_);
lean_inc_ref(v___y_4749_);
lean_inc(v___y_4748_);
lean_inc_ref(v___y_4747_);
lean_inc_ref(v_b_4746_);
v___x_4759_ = lean_infer_type(v_b_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_);
if (lean_obj_tag(v___x_4759_) == 0)
{
lean_object* v_a_4760_; lean_object* v___x_4761_; 
v_a_4760_ = lean_ctor_get(v___x_4759_, 0);
lean_inc(v_a_4760_);
lean_dec_ref_known(v___x_4759_, 1);
v___x_4761_ = l_Lean_Meta_whnfForall(v_a_4760_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_);
if (lean_obj_tag(v___x_4761_) == 0)
{
lean_object* v_a_4762_; lean_object* v_a_4763_; lean_object* v___x_4764_; 
v_a_4762_ = lean_ctor_get(v___x_4761_, 0);
lean_inc(v_a_4762_);
lean_dec_ref_known(v___x_4761_, 1);
v_a_4763_ = lean_array_uget_borrowed(v_as_4743_, v_i_4745_);
lean_inc(v___y_4750_);
lean_inc_ref(v___y_4749_);
lean_inc(v___y_4748_);
lean_inc_ref(v___y_4747_);
lean_inc(v_a_4763_);
v___x_4764_ = lean_infer_type(v_a_4763_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_);
if (lean_obj_tag(v___x_4764_) == 0)
{
lean_object* v_a_4765_; lean_object* v___x_4768_; uint8_t v___x_4769_; 
v_a_4765_ = lean_ctor_get(v___x_4764_, 0);
lean_inc(v_a_4765_);
lean_dec_ref_known(v___x_4764_, 1);
v___x_4768_ = l_Lean_Expr_bindingDomain_x21(v_a_4762_);
lean_dec(v_a_4762_);
v___x_4769_ = l_Lean_Expr_isHEq(v___x_4768_);
lean_dec_ref(v___x_4768_);
if (v___x_4769_ == 0)
{
lean_dec(v_a_4765_);
goto v___jp_4766_;
}
else
{
uint8_t v___x_4770_; 
v___x_4770_ = l_Lean_Expr_isEq(v_a_4765_);
lean_dec(v_a_4765_);
if (v___x_4770_ == 0)
{
goto v___jp_4766_;
}
else
{
lean_object* v___x_4771_; 
lean_inc(v_a_4763_);
v___x_4771_ = l_Lean_Meta_mkHEqOfEq(v_a_4763_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_);
if (lean_obj_tag(v___x_4771_) == 0)
{
lean_object* v_a_4772_; lean_object* v___x_4773_; 
v_a_4772_ = lean_ctor_get(v___x_4771_, 0);
lean_inc(v_a_4772_);
lean_dec_ref_known(v___x_4771_, 1);
v___x_4773_ = l_Lean_Expr_app___override(v_b_4746_, v_a_4772_);
v_a_4753_ = v___x_4773_;
goto v___jp_4752_;
}
else
{
lean_dec_ref(v_b_4746_);
return v___x_4771_;
}
}
}
v___jp_4766_:
{
lean_object* v___x_4767_; 
lean_inc(v_a_4763_);
v___x_4767_ = l_Lean_Expr_app___override(v_b_4746_, v_a_4763_);
v_a_4753_ = v___x_4767_;
goto v___jp_4752_;
}
}
else
{
lean_dec(v_a_4762_);
lean_dec_ref(v_b_4746_);
return v___x_4764_;
}
}
else
{
lean_dec_ref(v_b_4746_);
return v___x_4761_;
}
}
else
{
lean_dec_ref(v_b_4746_);
return v___x_4759_;
}
}
v___jp_4752_:
{
size_t v___x_4754_; size_t v___x_4755_; 
v___x_4754_ = ((size_t)1ULL);
v___x_4755_ = lean_usize_add(v_i_4745_, v___x_4754_);
v_i_4745_ = v___x_4755_;
v_b_4746_ = v_a_4753_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1___boxed(lean_object* v_as_4774_, lean_object* v_sz_4775_, lean_object* v_i_4776_, lean_object* v_b_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_){
_start:
{
size_t v_sz_boxed_4783_; size_t v_i_boxed_4784_; lean_object* v_res_4785_; 
v_sz_boxed_4783_ = lean_unbox_usize(v_sz_4775_);
lean_dec(v_sz_4775_);
v_i_boxed_4784_ = lean_unbox_usize(v_i_4776_);
lean_dec(v_i_4776_);
v_res_4785_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1(v_as_4774_, v_sz_boxed_4783_, v_i_boxed_4784_, v_b_4777_, v___y_4778_, v___y_4779_, v___y_4780_, v___y_4781_);
lean_dec(v___y_4781_);
lean_dec_ref(v___y_4780_);
lean_dec(v___y_4779_);
lean_dec_ref(v___y_4778_);
lean_dec_ref(v_as_4774_);
return v_res_4785_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_4787_; lean_object* v___x_4788_; 
v___x_4787_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg___closed__0));
v___x_4788_ = l_Lean_stringToMessageData(v___x_4787_);
return v___x_4788_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_4790_; lean_object* v___x_4791_; 
v___x_4790_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg___closed__2));
v___x_4791_ = l_Lean_stringToMessageData(v___x_4790_);
return v___x_4791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg(lean_object* v_range_4792_, lean_object* v_b_4793_, lean_object* v_i_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_){
_start:
{
lean_object* v_stop_4800_; lean_object* v_step_4801_; lean_object* v_a_4803_; uint8_t v___x_4806_; 
v_stop_4800_ = lean_ctor_get(v_range_4792_, 1);
v_step_4801_ = lean_ctor_get(v_range_4792_, 2);
v___x_4806_ = lean_nat_dec_lt(v_i_4794_, v_stop_4800_);
if (v___x_4806_ == 0)
{
lean_object* v___x_4807_; 
lean_dec(v_i_4794_);
v___x_4807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4807_, 0, v_b_4793_);
return v___x_4807_;
}
else
{
lean_object* v___x_4808_; 
lean_inc(v___y_4798_);
lean_inc_ref(v___y_4797_);
lean_inc(v___y_4796_);
lean_inc_ref(v___y_4795_);
lean_inc_ref(v_b_4793_);
v___x_4808_ = lean_infer_type(v_b_4793_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_);
if (lean_obj_tag(v___x_4808_) == 0)
{
lean_object* v_a_4809_; lean_object* v___x_4810_; 
v_a_4809_ = lean_ctor_get(v___x_4808_, 0);
lean_inc(v_a_4809_);
lean_dec_ref_known(v___x_4808_, 1);
v___x_4810_ = l_Lean_Meta_whnfForall(v_a_4809_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_);
if (lean_obj_tag(v___x_4810_) == 0)
{
lean_object* v_a_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; 
v_a_4811_ = lean_ctor_get(v___x_4810_, 0);
lean_inc(v_a_4811_);
lean_dec_ref_known(v___x_4810_, 1);
v___x_4812_ = l_Lean_Expr_bindingDomain_x21(v_a_4811_);
lean_dec(v_a_4811_);
lean_inc(v___y_4798_);
lean_inc_ref(v___y_4797_);
lean_inc(v___y_4796_);
lean_inc_ref(v___y_4795_);
v___x_4813_ = lean_whnf(v___x_4812_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_);
if (lean_obj_tag(v___x_4813_) == 0)
{
lean_object* v_a_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; uint8_t v___x_4817_; 
v_a_4814_ = lean_ctor_get(v___x_4813_, 0);
lean_inc(v_a_4814_);
lean_dec_ref_known(v___x_4813_, 1);
v___x_4815_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__1));
v___x_4816_ = lean_unsigned_to_nat(4u);
v___x_4817_ = l_Lean_Expr_isAppOfArity(v_a_4814_, v___x_4815_, v___x_4816_);
if (v___x_4817_ == 0)
{
lean_object* v___x_4818_; lean_object* v___x_4819_; uint8_t v___x_4820_; 
v___x_4818_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__2));
v___x_4819_ = lean_unsigned_to_nat(3u);
v___x_4820_ = l_Lean_Expr_isAppOfArity(v_a_4814_, v___x_4818_, v___x_4819_);
if (v___x_4820_ == 0)
{
lean_object* v___x_4821_; 
lean_dec(v_i_4794_);
lean_inc(v___y_4798_);
lean_inc_ref(v___y_4797_);
lean_inc(v___y_4796_);
lean_inc_ref(v___y_4795_);
v___x_4821_ = lean_infer_type(v_b_4793_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_);
if (lean_obj_tag(v___x_4821_) == 0)
{
lean_object* v_a_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v_a_4832_; lean_object* v___x_4834_; uint8_t v_isShared_4835_; uint8_t v_isSharedCheck_4839_; 
v_a_4822_ = lean_ctor_get(v___x_4821_, 0);
lean_inc(v_a_4822_);
lean_dec_ref_known(v___x_4821_, 1);
v___x_4823_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg___closed__1, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg___closed__1_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg___closed__1);
v___x_4824_ = l_Lean_MessageData_ofExpr(v_a_4814_);
v___x_4825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4825_, 0, v___x_4823_);
lean_ctor_set(v___x_4825_, 1, v___x_4824_);
v___x_4826_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg___closed__3, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg___closed__3_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg___closed__3);
v___x_4827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4827_, 0, v___x_4825_);
lean_ctor_set(v___x_4827_, 1, v___x_4826_);
v___x_4828_ = lean_unsigned_to_nat(30u);
v___x_4829_ = l_Lean_inlineExpr(v_a_4822_, v___x_4828_);
v___x_4830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4830_, 0, v___x_4827_);
lean_ctor_set(v___x_4830_, 1, v___x_4829_);
v___x_4831_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0___redArg(v___x_4830_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_);
v_a_4832_ = lean_ctor_get(v___x_4831_, 0);
v_isSharedCheck_4839_ = !lean_is_exclusive(v___x_4831_);
if (v_isSharedCheck_4839_ == 0)
{
v___x_4834_ = v___x_4831_;
v_isShared_4835_ = v_isSharedCheck_4839_;
goto v_resetjp_4833_;
}
else
{
lean_inc(v_a_4832_);
lean_dec(v___x_4831_);
v___x_4834_ = lean_box(0);
v_isShared_4835_ = v_isSharedCheck_4839_;
goto v_resetjp_4833_;
}
v_resetjp_4833_:
{
lean_object* v___x_4837_; 
if (v_isShared_4835_ == 0)
{
v___x_4837_ = v___x_4834_;
goto v_reusejp_4836_;
}
else
{
lean_object* v_reuseFailAlloc_4838_; 
v_reuseFailAlloc_4838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4838_, 0, v_a_4832_);
v___x_4837_ = v_reuseFailAlloc_4838_;
goto v_reusejp_4836_;
}
v_reusejp_4836_:
{
return v___x_4837_;
}
}
}
else
{
lean_dec(v_a_4814_);
return v___x_4821_;
}
}
else
{
lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; 
v___x_4840_ = l_Lean_Expr_appFn_x21(v_a_4814_);
lean_dec(v_a_4814_);
v___x_4841_ = l_Lean_Expr_appArg_x21(v___x_4840_);
lean_dec_ref(v___x_4840_);
v___x_4842_ = l_Lean_Meta_mkEqRefl(v___x_4841_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_);
if (lean_obj_tag(v___x_4842_) == 0)
{
lean_object* v_a_4843_; lean_object* v___x_4844_; 
v_a_4843_ = lean_ctor_get(v___x_4842_, 0);
lean_inc(v_a_4843_);
lean_dec_ref_known(v___x_4842_, 1);
v___x_4844_ = l_Lean_Expr_app___override(v_b_4793_, v_a_4843_);
v_a_4803_ = v___x_4844_;
goto v___jp_4802_;
}
else
{
lean_dec(v_i_4794_);
lean_dec_ref(v_b_4793_);
return v___x_4842_;
}
}
}
else
{
lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; 
v___x_4845_ = l_Lean_Expr_appFn_x21(v_a_4814_);
lean_dec(v_a_4814_);
v___x_4846_ = l_Lean_Expr_appFn_x21(v___x_4845_);
lean_dec_ref(v___x_4845_);
v___x_4847_ = l_Lean_Expr_appArg_x21(v___x_4846_);
lean_dec_ref(v___x_4846_);
v___x_4848_ = l_Lean_Meta_mkHEqRefl(v___x_4847_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_);
if (lean_obj_tag(v___x_4848_) == 0)
{
lean_object* v_a_4849_; lean_object* v___x_4850_; 
v_a_4849_ = lean_ctor_get(v___x_4848_, 0);
lean_inc(v_a_4849_);
lean_dec_ref_known(v___x_4848_, 1);
v___x_4850_ = l_Lean_Expr_app___override(v_b_4793_, v_a_4849_);
v_a_4803_ = v___x_4850_;
goto v___jp_4802_;
}
else
{
lean_dec(v_i_4794_);
lean_dec_ref(v_b_4793_);
return v___x_4848_;
}
}
}
else
{
lean_dec(v_i_4794_);
lean_dec_ref(v_b_4793_);
return v___x_4813_;
}
}
else
{
lean_dec(v_i_4794_);
lean_dec_ref(v_b_4793_);
return v___x_4810_;
}
}
else
{
lean_dec(v_i_4794_);
lean_dec_ref(v_b_4793_);
return v___x_4808_;
}
}
v___jp_4802_:
{
lean_object* v___x_4804_; 
v___x_4804_ = lean_nat_add(v_i_4794_, v_step_4801_);
lean_dec(v_i_4794_);
v_b_4793_ = v_a_4803_;
v_i_4794_ = v___x_4804_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg___boxed(lean_object* v_range_4851_, lean_object* v_b_4852_, lean_object* v_i_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_){
_start:
{
lean_object* v_res_4859_; 
v_res_4859_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg(v_range_4851_, v_b_4852_, v_i_4853_, v___y_4854_, v___y_4855_, v___y_4856_, v___y_4857_);
lean_dec(v___y_4857_);
lean_dec_ref(v___y_4856_);
lean_dec(v___y_4855_);
lean_dec_ref(v___y_4854_);
lean_dec_ref(v_range_4851_);
return v_res_4859_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__0(lean_object* v___x_4860_, lean_object* v___x_4861_, lean_object* v___x_4862_, lean_object* v_xs_4863_, lean_object* v___x_4864_, lean_object* v___x_4865_, lean_object* v___x_4866_, lean_object* v___x_4867_, lean_object* v___x_4868_, lean_object* v___x_4869_, lean_object* v___x_4870_, lean_object* v_eqs_4871_, lean_object* v_P_4872_, lean_object* v___x_4873_, lean_object* v_eqvs_4874_, uint8_t v_a_4875_, uint8_t v___x_4876_, lean_object* v_head_4877_, lean_object* v___x_4878_, lean_object* v___x_4879_, lean_object* v_numParams_4880_, lean_object* v_numFields_4881_, lean_object* v___x_4882_, lean_object* v___x_4883_, lean_object* v_k_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_, lean_object* v___y_4887_, lean_object* v___y_4888_){
_start:
{
lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; 
v___x_4890_ = l_Lean_mkConst(v___x_4860_, v___x_4861_);
v___x_4891_ = l_Array_append___redArg(v___x_4862_, v_xs_4863_);
v___x_4892_ = l_Array_append___redArg(v___x_4891_, v___x_4864_);
lean_inc_ref_n(v___x_4865_, 2);
v___x_4893_ = lean_array_push(v___x_4865_, v___x_4866_);
v___x_4894_ = l_Array_append___redArg(v___x_4892_, v___x_4893_);
lean_dec_ref(v___x_4893_);
v___x_4895_ = l_Array_append___redArg(v___x_4894_, v_xs_4863_);
v___x_4896_ = l_Array_append___redArg(v___x_4895_, v___x_4867_);
v___x_4897_ = lean_array_push(v___x_4865_, v___x_4868_);
v___x_4898_ = l_Array_append___redArg(v___x_4896_, v___x_4897_);
lean_dec_ref(v___x_4897_);
v___x_4899_ = l_Lean_mkAppN(v___x_4890_, v___x_4898_);
lean_dec_ref(v___x_4898_);
v___x_4900_ = lean_array_get_size(v_xs_4863_);
lean_inc(v___x_4870_);
lean_inc(v___x_4869_);
v___x_4901_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4901_, 0, v___x_4869_);
lean_ctor_set(v___x_4901_, 1, v___x_4900_);
lean_ctor_set(v___x_4901_, 2, v___x_4870_);
v___x_4902_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg(v___x_4901_, v___x_4899_, v___x_4869_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_);
lean_dec_ref_known(v___x_4901_, 3);
if (lean_obj_tag(v___x_4902_) == 0)
{
lean_object* v_a_4903_; size_t v_sz_4904_; size_t v___x_4905_; lean_object* v___x_4906_; 
v_a_4903_ = lean_ctor_get(v___x_4902_, 0);
lean_inc(v_a_4903_);
lean_dec_ref_known(v___x_4902_, 1);
v_sz_4904_ = lean_array_size(v_eqs_4871_);
v___x_4905_ = ((size_t)0ULL);
v___x_4906_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1(v_eqs_4871_, v_sz_4904_, v___x_4905_, v_a_4903_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_);
if (lean_obj_tag(v___x_4906_) == 0)
{
lean_object* v_a_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; 
v_a_4907_ = lean_ctor_get(v___x_4906_, 0);
lean_inc(v_a_4907_);
lean_dec_ref_known(v___x_4906_, 1);
lean_inc_ref(v_k_4884_);
v___x_4908_ = l_Lean_Expr_app___override(v_a_4907_, v_k_4884_);
v___x_4909_ = l_Lean_Meta_mkExpectedTypeHint(v___x_4908_, v_P_4872_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_);
if (lean_obj_tag(v___x_4909_) == 0)
{
lean_object* v_a_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; uint8_t v___x_4914_; lean_object* v___x_4915_; 
v_a_4910_ = lean_ctor_get(v___x_4909_, 0);
lean_inc(v_a_4910_);
lean_dec_ref_known(v___x_4909_, 1);
v___x_4911_ = l_Array_append___redArg(v___x_4873_, v_eqvs_4874_);
v___x_4912_ = lean_array_push(v___x_4865_, v_k_4884_);
v___x_4913_ = l_Array_append___redArg(v___x_4911_, v___x_4912_);
lean_dec_ref(v___x_4912_);
v___x_4914_ = 1;
v___x_4915_ = l_Lean_Meta_mkLambdaFVars(v___x_4913_, v_a_4910_, v_a_4875_, v___x_4876_, v_a_4875_, v___x_4876_, v___x_4914_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_);
lean_dec_ref(v___x_4913_);
if (lean_obj_tag(v___x_4915_) == 0)
{
lean_object* v_a_4916_; lean_object* v___x_4917_; 
v_a_4916_ = lean_ctor_get(v___x_4915_, 0);
lean_inc_n(v_a_4916_, 2);
lean_dec_ref_known(v___x_4915_, 1);
lean_inc(v___y_4888_);
lean_inc_ref(v___y_4887_);
lean_inc(v___y_4886_);
lean_inc_ref(v___y_4885_);
v___x_4917_ = lean_infer_type(v_a_4916_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_);
if (lean_obj_tag(v___x_4917_) == 0)
{
lean_object* v_a_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v_a_4922_; lean_object* v___x_4924_; uint8_t v_isShared_4925_; uint8_t v_isSharedCheck_4982_; 
v_a_4918_ = lean_ctor_get(v___x_4917_, 0);
lean_inc(v_a_4918_);
lean_dec_ref_known(v___x_4917_, 1);
v___x_4919_ = l_Lean_Name_str___override(v_head_4877_, v___x_4878_);
v___x_4920_ = lean_box(1);
lean_inc(v___x_4919_);
v___x_4921_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__6___redArg(v___x_4919_, v___x_4879_, v_a_4918_, v_a_4916_, v___x_4920_, v___y_4888_);
v_a_4922_ = lean_ctor_get(v___x_4921_, 0);
v_isSharedCheck_4982_ = !lean_is_exclusive(v___x_4921_);
if (v_isSharedCheck_4982_ == 0)
{
v___x_4924_ = v___x_4921_;
v_isShared_4925_ = v_isSharedCheck_4982_;
goto v_resetjp_4923_;
}
else
{
lean_inc(v_a_4922_);
lean_dec(v___x_4921_);
v___x_4924_ = lean_box(0);
v_isShared_4925_ = v_isSharedCheck_4982_;
goto v_resetjp_4923_;
}
v_resetjp_4923_:
{
lean_object* v___x_4927_; 
if (v_isShared_4925_ == 0)
{
lean_ctor_set_tag(v___x_4924_, 1);
v___x_4927_ = v___x_4924_;
goto v_reusejp_4926_;
}
else
{
lean_object* v_reuseFailAlloc_4981_; 
v_reuseFailAlloc_4981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4981_, 0, v_a_4922_);
v___x_4927_ = v_reuseFailAlloc_4981_;
goto v_reusejp_4926_;
}
v_reusejp_4926_:
{
lean_object* v___x_4928_; 
v___x_4928_ = l_Lean_addDecl(v___x_4927_, v_a_4875_, v___y_4887_, v___y_4888_);
if (lean_obj_tag(v___x_4928_) == 0)
{
lean_object* v___x_4929_; lean_object* v___x_4931_; uint8_t v_isShared_4932_; uint8_t v_isSharedCheck_4979_; 
lean_dec_ref_known(v___x_4928_, 1);
lean_inc(v___x_4919_);
v___x_4929_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7(v___x_4919_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_);
v_isSharedCheck_4979_ = !lean_is_exclusive(v___x_4929_);
if (v_isSharedCheck_4979_ == 0)
{
lean_object* v_unused_4980_; 
v_unused_4980_ = lean_ctor_get(v___x_4929_, 0);
lean_dec(v_unused_4980_);
v___x_4931_ = v___x_4929_;
v_isShared_4932_ = v_isSharedCheck_4979_;
goto v_resetjp_4930_;
}
else
{
lean_dec(v___x_4929_);
v___x_4931_ = lean_box(0);
v_isShared_4932_ = v_isSharedCheck_4979_;
goto v_resetjp_4930_;
}
v_resetjp_4930_:
{
lean_object* v___x_4933_; lean_object* v_env_4934_; lean_object* v_nextMacroScope_4935_; lean_object* v_ngen_4936_; lean_object* v_auxDeclNGen_4937_; lean_object* v_traceState_4938_; lean_object* v_messages_4939_; lean_object* v_infoState_4940_; lean_object* v_snapshotTasks_4941_; lean_object* v___x_4943_; uint8_t v_isShared_4944_; uint8_t v_isSharedCheck_4977_; 
v___x_4933_ = lean_st_ref_take(v___y_4888_);
v_env_4934_ = lean_ctor_get(v___x_4933_, 0);
v_nextMacroScope_4935_ = lean_ctor_get(v___x_4933_, 1);
v_ngen_4936_ = lean_ctor_get(v___x_4933_, 2);
v_auxDeclNGen_4937_ = lean_ctor_get(v___x_4933_, 3);
v_traceState_4938_ = lean_ctor_get(v___x_4933_, 4);
v_messages_4939_ = lean_ctor_get(v___x_4933_, 6);
v_infoState_4940_ = lean_ctor_get(v___x_4933_, 7);
v_snapshotTasks_4941_ = lean_ctor_get(v___x_4933_, 8);
v_isSharedCheck_4977_ = !lean_is_exclusive(v___x_4933_);
if (v_isSharedCheck_4977_ == 0)
{
lean_object* v_unused_4978_; 
v_unused_4978_ = lean_ctor_get(v___x_4933_, 5);
lean_dec(v_unused_4978_);
v___x_4943_ = v___x_4933_;
v_isShared_4944_ = v_isSharedCheck_4977_;
goto v_resetjp_4942_;
}
else
{
lean_inc(v_snapshotTasks_4941_);
lean_inc(v_infoState_4940_);
lean_inc(v_messages_4939_);
lean_inc(v_traceState_4938_);
lean_inc(v_auxDeclNGen_4937_);
lean_inc(v_ngen_4936_);
lean_inc(v_nextMacroScope_4935_);
lean_inc(v_env_4934_);
lean_dec(v___x_4933_);
v___x_4943_ = lean_box(0);
v_isShared_4944_ = v_isSharedCheck_4977_;
goto v_resetjp_4942_;
}
v_resetjp_4942_:
{
lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4956_; 
v___x_4945_ = lean_nat_add(v_numParams_4880_, v___x_4870_);
lean_dec(v___x_4870_);
v___x_4946_ = lean_unsigned_to_nat(2u);
v___x_4947_ = lean_nat_mul(v___x_4946_, v_numFields_4881_);
v___x_4948_ = lean_nat_add(v___x_4945_, v___x_4947_);
lean_dec(v___x_4947_);
lean_dec(v___x_4945_);
v___x_4949_ = lean_array_get_size(v_eqvs_4874_);
v___x_4950_ = lean_nat_add(v___x_4948_, v___x_4949_);
lean_dec(v___x_4948_);
v___x_4951_ = l_Lean_Expr_getNumHeadForalls(v___x_4882_);
v___x_4952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4952_, 0, v___x_4950_);
lean_ctor_set(v___x_4952_, 1, v___x_4951_);
v___x_4953_ = l_Lean_markNoConfusion(v_env_4934_, v___x_4919_, v___x_4952_);
v___x_4954_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2);
if (v_isShared_4944_ == 0)
{
lean_ctor_set(v___x_4943_, 5, v___x_4954_);
lean_ctor_set(v___x_4943_, 0, v___x_4953_);
v___x_4956_ = v___x_4943_;
goto v_reusejp_4955_;
}
else
{
lean_object* v_reuseFailAlloc_4976_; 
v_reuseFailAlloc_4976_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4976_, 0, v___x_4953_);
lean_ctor_set(v_reuseFailAlloc_4976_, 1, v_nextMacroScope_4935_);
lean_ctor_set(v_reuseFailAlloc_4976_, 2, v_ngen_4936_);
lean_ctor_set(v_reuseFailAlloc_4976_, 3, v_auxDeclNGen_4937_);
lean_ctor_set(v_reuseFailAlloc_4976_, 4, v_traceState_4938_);
lean_ctor_set(v_reuseFailAlloc_4976_, 5, v___x_4954_);
lean_ctor_set(v_reuseFailAlloc_4976_, 6, v_messages_4939_);
lean_ctor_set(v_reuseFailAlloc_4976_, 7, v_infoState_4940_);
lean_ctor_set(v_reuseFailAlloc_4976_, 8, v_snapshotTasks_4941_);
v___x_4956_ = v_reuseFailAlloc_4976_;
goto v_reusejp_4955_;
}
v_reusejp_4955_:
{
lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v_mctx_4959_; lean_object* v_zetaDeltaFVarIds_4960_; lean_object* v_postponed_4961_; lean_object* v_diag_4962_; lean_object* v___x_4964_; uint8_t v_isShared_4965_; uint8_t v_isSharedCheck_4974_; 
v___x_4957_ = lean_st_ref_put(v___y_4888_, v___x_4956_);
v___x_4958_ = lean_st_ref_take(v___y_4886_);
v_mctx_4959_ = lean_ctor_get(v___x_4958_, 0);
v_zetaDeltaFVarIds_4960_ = lean_ctor_get(v___x_4958_, 2);
v_postponed_4961_ = lean_ctor_get(v___x_4958_, 3);
v_diag_4962_ = lean_ctor_get(v___x_4958_, 4);
v_isSharedCheck_4974_ = !lean_is_exclusive(v___x_4958_);
if (v_isSharedCheck_4974_ == 0)
{
lean_object* v_unused_4975_; 
v_unused_4975_ = lean_ctor_get(v___x_4958_, 1);
lean_dec(v_unused_4975_);
v___x_4964_ = v___x_4958_;
v_isShared_4965_ = v_isSharedCheck_4974_;
goto v_resetjp_4963_;
}
else
{
lean_inc(v_diag_4962_);
lean_inc(v_postponed_4961_);
lean_inc(v_zetaDeltaFVarIds_4960_);
lean_inc(v_mctx_4959_);
lean_dec(v___x_4958_);
v___x_4964_ = lean_box(0);
v_isShared_4965_ = v_isSharedCheck_4974_;
goto v_resetjp_4963_;
}
v_resetjp_4963_:
{
lean_object* v___x_4966_; lean_object* v___x_4968_; 
v___x_4966_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3);
if (v_isShared_4965_ == 0)
{
lean_ctor_set(v___x_4964_, 1, v___x_4966_);
v___x_4968_ = v___x_4964_;
goto v_reusejp_4967_;
}
else
{
lean_object* v_reuseFailAlloc_4973_; 
v_reuseFailAlloc_4973_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4973_, 0, v_mctx_4959_);
lean_ctor_set(v_reuseFailAlloc_4973_, 1, v___x_4966_);
lean_ctor_set(v_reuseFailAlloc_4973_, 2, v_zetaDeltaFVarIds_4960_);
lean_ctor_set(v_reuseFailAlloc_4973_, 3, v_postponed_4961_);
lean_ctor_set(v_reuseFailAlloc_4973_, 4, v_diag_4962_);
v___x_4968_ = v_reuseFailAlloc_4973_;
goto v_reusejp_4967_;
}
v_reusejp_4967_:
{
lean_object* v___x_4969_; lean_object* v___x_4971_; 
v___x_4969_ = lean_st_ref_put(v___y_4886_, v___x_4968_);
if (v_isShared_4932_ == 0)
{
lean_ctor_set(v___x_4931_, 0, v___x_4883_);
v___x_4971_ = v___x_4931_;
goto v_reusejp_4970_;
}
else
{
lean_object* v_reuseFailAlloc_4972_; 
v_reuseFailAlloc_4972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4972_, 0, v___x_4883_);
v___x_4971_ = v_reuseFailAlloc_4972_;
goto v_reusejp_4970_;
}
v_reusejp_4970_:
{
return v___x_4971_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_4919_);
lean_dec(v___x_4870_);
return v___x_4928_;
}
}
}
}
else
{
lean_object* v_a_4983_; lean_object* v___x_4985_; uint8_t v_isShared_4986_; uint8_t v_isSharedCheck_4990_; 
lean_dec(v_a_4916_);
lean_dec(v___x_4879_);
lean_dec_ref(v___x_4878_);
lean_dec(v_head_4877_);
lean_dec(v___x_4870_);
v_a_4983_ = lean_ctor_get(v___x_4917_, 0);
v_isSharedCheck_4990_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_4990_ == 0)
{
v___x_4985_ = v___x_4917_;
v_isShared_4986_ = v_isSharedCheck_4990_;
goto v_resetjp_4984_;
}
else
{
lean_inc(v_a_4983_);
lean_dec(v___x_4917_);
v___x_4985_ = lean_box(0);
v_isShared_4986_ = v_isSharedCheck_4990_;
goto v_resetjp_4984_;
}
v_resetjp_4984_:
{
lean_object* v___x_4988_; 
if (v_isShared_4986_ == 0)
{
v___x_4988_ = v___x_4985_;
goto v_reusejp_4987_;
}
else
{
lean_object* v_reuseFailAlloc_4989_; 
v_reuseFailAlloc_4989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4989_, 0, v_a_4983_);
v___x_4988_ = v_reuseFailAlloc_4989_;
goto v_reusejp_4987_;
}
v_reusejp_4987_:
{
return v___x_4988_;
}
}
}
}
else
{
lean_object* v_a_4991_; lean_object* v___x_4993_; uint8_t v_isShared_4994_; uint8_t v_isSharedCheck_4998_; 
lean_dec(v___x_4879_);
lean_dec_ref(v___x_4878_);
lean_dec(v_head_4877_);
lean_dec(v___x_4870_);
v_a_4991_ = lean_ctor_get(v___x_4915_, 0);
v_isSharedCheck_4998_ = !lean_is_exclusive(v___x_4915_);
if (v_isSharedCheck_4998_ == 0)
{
v___x_4993_ = v___x_4915_;
v_isShared_4994_ = v_isSharedCheck_4998_;
goto v_resetjp_4992_;
}
else
{
lean_inc(v_a_4991_);
lean_dec(v___x_4915_);
v___x_4993_ = lean_box(0);
v_isShared_4994_ = v_isSharedCheck_4998_;
goto v_resetjp_4992_;
}
v_resetjp_4992_:
{
lean_object* v___x_4996_; 
if (v_isShared_4994_ == 0)
{
v___x_4996_ = v___x_4993_;
goto v_reusejp_4995_;
}
else
{
lean_object* v_reuseFailAlloc_4997_; 
v_reuseFailAlloc_4997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4997_, 0, v_a_4991_);
v___x_4996_ = v_reuseFailAlloc_4997_;
goto v_reusejp_4995_;
}
v_reusejp_4995_:
{
return v___x_4996_;
}
}
}
}
else
{
lean_object* v_a_4999_; lean_object* v___x_5001_; uint8_t v_isShared_5002_; uint8_t v_isSharedCheck_5006_; 
lean_dec_ref(v_k_4884_);
lean_dec(v___x_4879_);
lean_dec_ref(v___x_4878_);
lean_dec(v_head_4877_);
lean_dec_ref(v___x_4873_);
lean_dec(v___x_4870_);
lean_dec_ref(v___x_4865_);
v_a_4999_ = lean_ctor_get(v___x_4909_, 0);
v_isSharedCheck_5006_ = !lean_is_exclusive(v___x_4909_);
if (v_isSharedCheck_5006_ == 0)
{
v___x_5001_ = v___x_4909_;
v_isShared_5002_ = v_isSharedCheck_5006_;
goto v_resetjp_5000_;
}
else
{
lean_inc(v_a_4999_);
lean_dec(v___x_4909_);
v___x_5001_ = lean_box(0);
v_isShared_5002_ = v_isSharedCheck_5006_;
goto v_resetjp_5000_;
}
v_resetjp_5000_:
{
lean_object* v___x_5004_; 
if (v_isShared_5002_ == 0)
{
v___x_5004_ = v___x_5001_;
goto v_reusejp_5003_;
}
else
{
lean_object* v_reuseFailAlloc_5005_; 
v_reuseFailAlloc_5005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5005_, 0, v_a_4999_);
v___x_5004_ = v_reuseFailAlloc_5005_;
goto v_reusejp_5003_;
}
v_reusejp_5003_:
{
return v___x_5004_;
}
}
}
}
else
{
lean_object* v_a_5007_; lean_object* v___x_5009_; uint8_t v_isShared_5010_; uint8_t v_isSharedCheck_5014_; 
lean_dec_ref(v_k_4884_);
lean_dec(v___x_4879_);
lean_dec_ref(v___x_4878_);
lean_dec(v_head_4877_);
lean_dec_ref(v___x_4873_);
lean_dec_ref(v_P_4872_);
lean_dec(v___x_4870_);
lean_dec_ref(v___x_4865_);
v_a_5007_ = lean_ctor_get(v___x_4906_, 0);
v_isSharedCheck_5014_ = !lean_is_exclusive(v___x_4906_);
if (v_isSharedCheck_5014_ == 0)
{
v___x_5009_ = v___x_4906_;
v_isShared_5010_ = v_isSharedCheck_5014_;
goto v_resetjp_5008_;
}
else
{
lean_inc(v_a_5007_);
lean_dec(v___x_4906_);
v___x_5009_ = lean_box(0);
v_isShared_5010_ = v_isSharedCheck_5014_;
goto v_resetjp_5008_;
}
v_resetjp_5008_:
{
lean_object* v___x_5012_; 
if (v_isShared_5010_ == 0)
{
v___x_5012_ = v___x_5009_;
goto v_reusejp_5011_;
}
else
{
lean_object* v_reuseFailAlloc_5013_; 
v_reuseFailAlloc_5013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5013_, 0, v_a_5007_);
v___x_5012_ = v_reuseFailAlloc_5013_;
goto v_reusejp_5011_;
}
v_reusejp_5011_:
{
return v___x_5012_;
}
}
}
}
else
{
lean_object* v_a_5015_; lean_object* v___x_5017_; uint8_t v_isShared_5018_; uint8_t v_isSharedCheck_5022_; 
lean_dec_ref(v_k_4884_);
lean_dec(v___x_4879_);
lean_dec_ref(v___x_4878_);
lean_dec(v_head_4877_);
lean_dec_ref(v___x_4873_);
lean_dec_ref(v_P_4872_);
lean_dec(v___x_4870_);
lean_dec_ref(v___x_4865_);
v_a_5015_ = lean_ctor_get(v___x_4902_, 0);
v_isSharedCheck_5022_ = !lean_is_exclusive(v___x_4902_);
if (v_isSharedCheck_5022_ == 0)
{
v___x_5017_ = v___x_4902_;
v_isShared_5018_ = v_isSharedCheck_5022_;
goto v_resetjp_5016_;
}
else
{
lean_inc(v_a_5015_);
lean_dec(v___x_4902_);
v___x_5017_ = lean_box(0);
v_isShared_5018_ = v_isSharedCheck_5022_;
goto v_resetjp_5016_;
}
v_resetjp_5016_:
{
lean_object* v___x_5020_; 
if (v_isShared_5018_ == 0)
{
v___x_5020_ = v___x_5017_;
goto v_reusejp_5019_;
}
else
{
lean_object* v_reuseFailAlloc_5021_; 
v_reuseFailAlloc_5021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5021_, 0, v_a_5015_);
v___x_5020_ = v_reuseFailAlloc_5021_;
goto v_reusejp_5019_;
}
v_reusejp_5019_:
{
return v___x_5020_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_5023_ = _args[0];
lean_object* v___x_5024_ = _args[1];
lean_object* v___x_5025_ = _args[2];
lean_object* v_xs_5026_ = _args[3];
lean_object* v___x_5027_ = _args[4];
lean_object* v___x_5028_ = _args[5];
lean_object* v___x_5029_ = _args[6];
lean_object* v___x_5030_ = _args[7];
lean_object* v___x_5031_ = _args[8];
lean_object* v___x_5032_ = _args[9];
lean_object* v___x_5033_ = _args[10];
lean_object* v_eqs_5034_ = _args[11];
lean_object* v_P_5035_ = _args[12];
lean_object* v___x_5036_ = _args[13];
lean_object* v_eqvs_5037_ = _args[14];
lean_object* v_a_5038_ = _args[15];
lean_object* v___x_5039_ = _args[16];
lean_object* v_head_5040_ = _args[17];
lean_object* v___x_5041_ = _args[18];
lean_object* v___x_5042_ = _args[19];
lean_object* v_numParams_5043_ = _args[20];
lean_object* v_numFields_5044_ = _args[21];
lean_object* v___x_5045_ = _args[22];
lean_object* v___x_5046_ = _args[23];
lean_object* v_k_5047_ = _args[24];
lean_object* v___y_5048_ = _args[25];
lean_object* v___y_5049_ = _args[26];
lean_object* v___y_5050_ = _args[27];
lean_object* v___y_5051_ = _args[28];
lean_object* v___y_5052_ = _args[29];
_start:
{
uint8_t v_a_17547__boxed_5053_; uint8_t v___x_17548__boxed_5054_; lean_object* v_res_5055_; 
v_a_17547__boxed_5053_ = lean_unbox(v_a_5038_);
v___x_17548__boxed_5054_ = lean_unbox(v___x_5039_);
v_res_5055_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__0(v___x_5023_, v___x_5024_, v___x_5025_, v_xs_5026_, v___x_5027_, v___x_5028_, v___x_5029_, v___x_5030_, v___x_5031_, v___x_5032_, v___x_5033_, v_eqs_5034_, v_P_5035_, v___x_5036_, v_eqvs_5037_, v_a_17547__boxed_5053_, v___x_17548__boxed_5054_, v_head_5040_, v___x_5041_, v___x_5042_, v_numParams_5043_, v_numFields_5044_, v___x_5045_, v___x_5046_, v_k_5047_, v___y_5048_, v___y_5049_, v___y_5050_, v___y_5051_);
lean_dec(v___y_5051_);
lean_dec_ref(v___y_5050_);
lean_dec(v___y_5049_);
lean_dec_ref(v___y_5048_);
lean_dec_ref(v___x_5045_);
lean_dec(v_numFields_5044_);
lean_dec(v_numParams_5043_);
lean_dec_ref(v_eqvs_5037_);
lean_dec_ref(v_eqs_5034_);
lean_dec_ref(v___x_5030_);
lean_dec_ref(v___x_5027_);
lean_dec_ref(v_xs_5026_);
return v_res_5055_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__1(lean_object* v_head_5056_, lean_object* v_P_5057_, lean_object* v___x_5058_, lean_object* v_xs_5059_, lean_object* v_fields2_5060_, lean_object* v___x_5061_, lean_object* v___x_5062_, lean_object* v___x_5063_, lean_object* v___x_5064_, lean_object* v___x_5065_, lean_object* v___x_5066_, lean_object* v___x_5067_, lean_object* v___x_5068_, lean_object* v___x_5069_, lean_object* v___x_5070_, lean_object* v___x_5071_, uint8_t v_a_5072_, uint8_t v___x_5073_, lean_object* v___x_5074_, lean_object* v___x_5075_, lean_object* v_numParams_5076_, lean_object* v_numFields_5077_, lean_object* v___x_5078_, lean_object* v_eqvs_5079_, lean_object* v_eqs_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_){
_start:
{
lean_object* v___x_5086_; 
lean_inc_ref(v_P_5057_);
lean_inc(v_head_5056_);
v___x_5086_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg(v_head_5056_, v_P_5057_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_);
if (lean_obj_tag(v___x_5086_) == 0)
{
lean_object* v_a_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___f_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; 
v_a_5087_ = lean_ctor_get(v___x_5086_, 0);
lean_inc(v_a_5087_);
lean_dec_ref_known(v___x_5086_, 1);
v___x_5088_ = l_Array_append___redArg(v___x_5058_, v_xs_5059_);
v___x_5089_ = l_Array_append___redArg(v___x_5088_, v_fields2_5060_);
v___x_5090_ = l_Lean_Expr_beta(v_a_5087_, v___x_5089_);
v___x_5091_ = lean_box(v_a_5072_);
v___x_5092_ = lean_box(v___x_5073_);
lean_inc_ref(v___x_5090_);
v___f_5093_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__0___boxed), 30, 24);
lean_closure_set(v___f_5093_, 0, v___x_5061_);
lean_closure_set(v___f_5093_, 1, v___x_5062_);
lean_closure_set(v___f_5093_, 2, v___x_5063_);
lean_closure_set(v___f_5093_, 3, v_xs_5059_);
lean_closure_set(v___f_5093_, 4, v___x_5064_);
lean_closure_set(v___f_5093_, 5, v___x_5065_);
lean_closure_set(v___f_5093_, 6, v___x_5066_);
lean_closure_set(v___f_5093_, 7, v___x_5067_);
lean_closure_set(v___f_5093_, 8, v___x_5068_);
lean_closure_set(v___f_5093_, 9, v___x_5069_);
lean_closure_set(v___f_5093_, 10, v___x_5070_);
lean_closure_set(v___f_5093_, 11, v_eqs_5080_);
lean_closure_set(v___f_5093_, 12, v_P_5057_);
lean_closure_set(v___f_5093_, 13, v___x_5071_);
lean_closure_set(v___f_5093_, 14, v_eqvs_5079_);
lean_closure_set(v___f_5093_, 15, v___x_5091_);
lean_closure_set(v___f_5093_, 16, v___x_5092_);
lean_closure_set(v___f_5093_, 17, v_head_5056_);
lean_closure_set(v___f_5093_, 18, v___x_5074_);
lean_closure_set(v___f_5093_, 19, v___x_5075_);
lean_closure_set(v___f_5093_, 20, v_numParams_5076_);
lean_closure_set(v___f_5093_, 21, v_numFields_5077_);
lean_closure_set(v___f_5093_, 22, v___x_5090_);
lean_closure_set(v___f_5093_, 23, v___x_5078_);
v___x_5094_ = ((lean_object*)(l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__1___closed__1));
v___x_5095_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_5094_, v___x_5090_, v___f_5093_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_);
return v___x_5095_;
}
else
{
lean_object* v_a_5096_; lean_object* v___x_5098_; uint8_t v_isShared_5099_; uint8_t v_isSharedCheck_5103_; 
lean_dec_ref(v_eqs_5080_);
lean_dec_ref(v_eqvs_5079_);
lean_dec(v_numFields_5077_);
lean_dec(v_numParams_5076_);
lean_dec(v___x_5075_);
lean_dec_ref(v___x_5074_);
lean_dec_ref(v___x_5071_);
lean_dec(v___x_5070_);
lean_dec(v___x_5069_);
lean_dec_ref(v___x_5068_);
lean_dec_ref(v___x_5067_);
lean_dec_ref(v___x_5066_);
lean_dec_ref(v___x_5065_);
lean_dec_ref(v___x_5064_);
lean_dec_ref(v___x_5063_);
lean_dec(v___x_5062_);
lean_dec(v___x_5061_);
lean_dec_ref(v_xs_5059_);
lean_dec_ref(v___x_5058_);
lean_dec_ref(v_P_5057_);
lean_dec(v_head_5056_);
v_a_5096_ = lean_ctor_get(v___x_5086_, 0);
v_isSharedCheck_5103_ = !lean_is_exclusive(v___x_5086_);
if (v_isSharedCheck_5103_ == 0)
{
v___x_5098_ = v___x_5086_;
v_isShared_5099_ = v_isSharedCheck_5103_;
goto v_resetjp_5097_;
}
else
{
lean_inc(v_a_5096_);
lean_dec(v___x_5086_);
v___x_5098_ = lean_box(0);
v_isShared_5099_ = v_isSharedCheck_5103_;
goto v_resetjp_5097_;
}
v_resetjp_5097_:
{
lean_object* v___x_5101_; 
if (v_isShared_5099_ == 0)
{
v___x_5101_ = v___x_5098_;
goto v_reusejp_5100_;
}
else
{
lean_object* v_reuseFailAlloc_5102_; 
v_reuseFailAlloc_5102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5102_, 0, v_a_5096_);
v___x_5101_ = v_reuseFailAlloc_5102_;
goto v_reusejp_5100_;
}
v_reusejp_5100_:
{
return v___x_5101_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_head_5104_ = _args[0];
lean_object* v_P_5105_ = _args[1];
lean_object* v___x_5106_ = _args[2];
lean_object* v_xs_5107_ = _args[3];
lean_object* v_fields2_5108_ = _args[4];
lean_object* v___x_5109_ = _args[5];
lean_object* v___x_5110_ = _args[6];
lean_object* v___x_5111_ = _args[7];
lean_object* v___x_5112_ = _args[8];
lean_object* v___x_5113_ = _args[9];
lean_object* v___x_5114_ = _args[10];
lean_object* v___x_5115_ = _args[11];
lean_object* v___x_5116_ = _args[12];
lean_object* v___x_5117_ = _args[13];
lean_object* v___x_5118_ = _args[14];
lean_object* v___x_5119_ = _args[15];
lean_object* v_a_5120_ = _args[16];
lean_object* v___x_5121_ = _args[17];
lean_object* v___x_5122_ = _args[18];
lean_object* v___x_5123_ = _args[19];
lean_object* v_numParams_5124_ = _args[20];
lean_object* v_numFields_5125_ = _args[21];
lean_object* v___x_5126_ = _args[22];
lean_object* v_eqvs_5127_ = _args[23];
lean_object* v_eqs_5128_ = _args[24];
lean_object* v___y_5129_ = _args[25];
lean_object* v___y_5130_ = _args[26];
lean_object* v___y_5131_ = _args[27];
lean_object* v___y_5132_ = _args[28];
lean_object* v___y_5133_ = _args[29];
_start:
{
uint8_t v_a_17868__boxed_5134_; uint8_t v___x_17869__boxed_5135_; lean_object* v_res_5136_; 
v_a_17868__boxed_5134_ = lean_unbox(v_a_5120_);
v___x_17869__boxed_5135_ = lean_unbox(v___x_5121_);
v_res_5136_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__1(v_head_5104_, v_P_5105_, v___x_5106_, v_xs_5107_, v_fields2_5108_, v___x_5109_, v___x_5110_, v___x_5111_, v___x_5112_, v___x_5113_, v___x_5114_, v___x_5115_, v___x_5116_, v___x_5117_, v___x_5118_, v___x_5119_, v_a_17868__boxed_5134_, v___x_17869__boxed_5135_, v___x_5122_, v___x_5123_, v_numParams_5124_, v_numFields_5125_, v___x_5126_, v_eqvs_5127_, v_eqs_5128_, v___y_5129_, v___y_5130_, v___y_5131_, v___y_5132_);
lean_dec(v___y_5132_);
lean_dec_ref(v___y_5131_);
lean_dec(v___y_5130_);
lean_dec_ref(v___y_5129_);
lean_dec_ref(v_fields2_5108_);
return v_res_5136_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__2___closed__0(void){
_start:
{
lean_object* v___x_5137_; lean_object* v_dummy_5138_; 
v___x_5137_ = lean_box(0);
v_dummy_5138_ = l_Lean_Expr_sort___override(v___x_5137_);
return v_dummy_5138_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__2(lean_object* v___x_5139_, lean_object* v_val_5140_, lean_object* v___x_5141_, lean_object* v_head_5142_, lean_object* v_P_5143_, lean_object* v___x_5144_, lean_object* v_xs_5145_, lean_object* v_fields2_5146_, lean_object* v___x_5147_, lean_object* v___x_5148_, lean_object* v___x_5149_, lean_object* v___x_5150_, lean_object* v___x_5151_, lean_object* v___x_5152_, lean_object* v___x_5153_, uint8_t v_a_5154_, uint8_t v___x_5155_, lean_object* v___x_5156_, lean_object* v___x_5157_, lean_object* v_numParams_5158_, lean_object* v_numFields_5159_, lean_object* v___x_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_){
_start:
{
lean_object* v___x_5166_; 
lean_inc(v___y_5164_);
lean_inc_ref(v___y_5163_);
lean_inc(v___y_5162_);
lean_inc_ref(v___y_5161_);
lean_inc_ref(v___x_5139_);
v___x_5166_ = lean_infer_type(v___x_5139_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_);
if (lean_obj_tag(v___x_5166_) == 0)
{
lean_object* v_a_5167_; lean_object* v___x_5168_; 
v_a_5167_ = lean_ctor_get(v___x_5166_, 0);
lean_inc(v_a_5167_);
lean_dec_ref_known(v___x_5166_, 1);
lean_inc(v___y_5164_);
lean_inc_ref(v___y_5163_);
lean_inc(v___y_5162_);
lean_inc_ref(v___y_5161_);
v___x_5168_ = lean_whnf(v_a_5167_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_);
if (lean_obj_tag(v___x_5168_) == 0)
{
lean_object* v_a_5169_; lean_object* v_numIndices_5170_; lean_object* v___x_5171_; 
v_a_5169_ = lean_ctor_get(v___x_5168_, 0);
lean_inc(v_a_5169_);
lean_dec_ref_known(v___x_5168_, 1);
v_numIndices_5170_ = lean_ctor_get(v_val_5140_, 2);
lean_inc(v_numIndices_5170_);
lean_dec_ref(v_val_5140_);
lean_inc(v___y_5164_);
lean_inc_ref(v___y_5163_);
lean_inc(v___y_5162_);
lean_inc_ref(v___y_5161_);
lean_inc_ref(v___x_5141_);
v___x_5171_ = lean_infer_type(v___x_5141_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_);
if (lean_obj_tag(v___x_5171_) == 0)
{
lean_object* v_a_5172_; lean_object* v___x_5173_; 
v_a_5172_ = lean_ctor_get(v___x_5171_, 0);
lean_inc(v_a_5172_);
lean_dec_ref_known(v___x_5171_, 1);
lean_inc(v___y_5164_);
lean_inc_ref(v___y_5163_);
lean_inc(v___y_5162_);
lean_inc_ref(v___y_5161_);
v___x_5173_ = lean_whnf(v_a_5172_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_);
if (lean_obj_tag(v___x_5173_) == 0)
{
lean_object* v_a_5174_; lean_object* v_dummy_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___f_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; 
v_a_5174_ = lean_ctor_get(v___x_5173_, 0);
lean_inc(v_a_5174_);
lean_dec_ref_known(v___x_5173_, 1);
v_dummy_5175_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__2___closed__0, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__2___closed__0_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__2___closed__0);
lean_inc_n(v_numIndices_5170_, 2);
v___x_5176_ = lean_mk_array(v_numIndices_5170_, v_dummy_5175_);
lean_inc_ref(v___x_5176_);
v___x_5177_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v_numIndices_5170_, v_a_5169_, v___x_5176_);
v___x_5178_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v_numIndices_5170_, v_a_5174_, v___x_5176_);
v___x_5179_ = lean_box(v_a_5154_);
v___x_5180_ = lean_box(v___x_5155_);
lean_inc_ref(v___x_5141_);
lean_inc_ref(v___x_5178_);
lean_inc_ref(v___x_5139_);
lean_inc_ref(v___x_5177_);
v___f_5181_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__1___boxed), 30, 23);
lean_closure_set(v___f_5181_, 0, v_head_5142_);
lean_closure_set(v___f_5181_, 1, v_P_5143_);
lean_closure_set(v___f_5181_, 2, v___x_5144_);
lean_closure_set(v___f_5181_, 3, v_xs_5145_);
lean_closure_set(v___f_5181_, 4, v_fields2_5146_);
lean_closure_set(v___f_5181_, 5, v___x_5147_);
lean_closure_set(v___f_5181_, 6, v___x_5148_);
lean_closure_set(v___f_5181_, 7, v___x_5149_);
lean_closure_set(v___f_5181_, 8, v___x_5177_);
lean_closure_set(v___f_5181_, 9, v___x_5150_);
lean_closure_set(v___f_5181_, 10, v___x_5139_);
lean_closure_set(v___f_5181_, 11, v___x_5178_);
lean_closure_set(v___f_5181_, 12, v___x_5141_);
lean_closure_set(v___f_5181_, 13, v___x_5151_);
lean_closure_set(v___f_5181_, 14, v___x_5152_);
lean_closure_set(v___f_5181_, 15, v___x_5153_);
lean_closure_set(v___f_5181_, 16, v___x_5179_);
lean_closure_set(v___f_5181_, 17, v___x_5180_);
lean_closure_set(v___f_5181_, 18, v___x_5156_);
lean_closure_set(v___f_5181_, 19, v___x_5157_);
lean_closure_set(v___f_5181_, 20, v_numParams_5158_);
lean_closure_set(v___f_5181_, 21, v_numFields_5159_);
lean_closure_set(v___f_5181_, 22, v___x_5160_);
v___x_5182_ = lean_array_push(v___x_5177_, v___x_5139_);
v___x_5183_ = lean_array_push(v___x_5178_, v___x_5141_);
v___x_5184_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope___redArg(v___x_5182_, v___x_5183_, v___f_5181_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_);
lean_dec(v___y_5164_);
lean_dec_ref(v___y_5163_);
lean_dec(v___y_5162_);
lean_dec_ref(v___y_5161_);
return v___x_5184_;
}
else
{
lean_object* v_a_5185_; lean_object* v___x_5187_; uint8_t v_isShared_5188_; uint8_t v_isSharedCheck_5192_; 
lean_dec(v_numIndices_5170_);
lean_dec(v_a_5169_);
lean_dec(v___y_5164_);
lean_dec_ref(v___y_5163_);
lean_dec(v___y_5162_);
lean_dec_ref(v___y_5161_);
lean_dec(v_numFields_5159_);
lean_dec(v_numParams_5158_);
lean_dec(v___x_5157_);
lean_dec_ref(v___x_5156_);
lean_dec_ref(v___x_5153_);
lean_dec(v___x_5152_);
lean_dec(v___x_5151_);
lean_dec_ref(v___x_5150_);
lean_dec_ref(v___x_5149_);
lean_dec(v___x_5148_);
lean_dec(v___x_5147_);
lean_dec_ref(v_fields2_5146_);
lean_dec_ref(v_xs_5145_);
lean_dec_ref(v___x_5144_);
lean_dec_ref(v_P_5143_);
lean_dec(v_head_5142_);
lean_dec_ref(v___x_5141_);
lean_dec_ref(v___x_5139_);
v_a_5185_ = lean_ctor_get(v___x_5173_, 0);
v_isSharedCheck_5192_ = !lean_is_exclusive(v___x_5173_);
if (v_isSharedCheck_5192_ == 0)
{
v___x_5187_ = v___x_5173_;
v_isShared_5188_ = v_isSharedCheck_5192_;
goto v_resetjp_5186_;
}
else
{
lean_inc(v_a_5185_);
lean_dec(v___x_5173_);
v___x_5187_ = lean_box(0);
v_isShared_5188_ = v_isSharedCheck_5192_;
goto v_resetjp_5186_;
}
v_resetjp_5186_:
{
lean_object* v___x_5190_; 
if (v_isShared_5188_ == 0)
{
v___x_5190_ = v___x_5187_;
goto v_reusejp_5189_;
}
else
{
lean_object* v_reuseFailAlloc_5191_; 
v_reuseFailAlloc_5191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5191_, 0, v_a_5185_);
v___x_5190_ = v_reuseFailAlloc_5191_;
goto v_reusejp_5189_;
}
v_reusejp_5189_:
{
return v___x_5190_;
}
}
}
}
else
{
lean_object* v_a_5193_; lean_object* v___x_5195_; uint8_t v_isShared_5196_; uint8_t v_isSharedCheck_5200_; 
lean_dec(v_numIndices_5170_);
lean_dec(v_a_5169_);
lean_dec(v___y_5164_);
lean_dec_ref(v___y_5163_);
lean_dec(v___y_5162_);
lean_dec_ref(v___y_5161_);
lean_dec(v_numFields_5159_);
lean_dec(v_numParams_5158_);
lean_dec(v___x_5157_);
lean_dec_ref(v___x_5156_);
lean_dec_ref(v___x_5153_);
lean_dec(v___x_5152_);
lean_dec(v___x_5151_);
lean_dec_ref(v___x_5150_);
lean_dec_ref(v___x_5149_);
lean_dec(v___x_5148_);
lean_dec(v___x_5147_);
lean_dec_ref(v_fields2_5146_);
lean_dec_ref(v_xs_5145_);
lean_dec_ref(v___x_5144_);
lean_dec_ref(v_P_5143_);
lean_dec(v_head_5142_);
lean_dec_ref(v___x_5141_);
lean_dec_ref(v___x_5139_);
v_a_5193_ = lean_ctor_get(v___x_5171_, 0);
v_isSharedCheck_5200_ = !lean_is_exclusive(v___x_5171_);
if (v_isSharedCheck_5200_ == 0)
{
v___x_5195_ = v___x_5171_;
v_isShared_5196_ = v_isSharedCheck_5200_;
goto v_resetjp_5194_;
}
else
{
lean_inc(v_a_5193_);
lean_dec(v___x_5171_);
v___x_5195_ = lean_box(0);
v_isShared_5196_ = v_isSharedCheck_5200_;
goto v_resetjp_5194_;
}
v_resetjp_5194_:
{
lean_object* v___x_5198_; 
if (v_isShared_5196_ == 0)
{
v___x_5198_ = v___x_5195_;
goto v_reusejp_5197_;
}
else
{
lean_object* v_reuseFailAlloc_5199_; 
v_reuseFailAlloc_5199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5199_, 0, v_a_5193_);
v___x_5198_ = v_reuseFailAlloc_5199_;
goto v_reusejp_5197_;
}
v_reusejp_5197_:
{
return v___x_5198_;
}
}
}
}
else
{
lean_object* v_a_5201_; lean_object* v___x_5203_; uint8_t v_isShared_5204_; uint8_t v_isSharedCheck_5208_; 
lean_dec(v___y_5164_);
lean_dec_ref(v___y_5163_);
lean_dec(v___y_5162_);
lean_dec_ref(v___y_5161_);
lean_dec(v_numFields_5159_);
lean_dec(v_numParams_5158_);
lean_dec(v___x_5157_);
lean_dec_ref(v___x_5156_);
lean_dec_ref(v___x_5153_);
lean_dec(v___x_5152_);
lean_dec(v___x_5151_);
lean_dec_ref(v___x_5150_);
lean_dec_ref(v___x_5149_);
lean_dec(v___x_5148_);
lean_dec(v___x_5147_);
lean_dec_ref(v_fields2_5146_);
lean_dec_ref(v_xs_5145_);
lean_dec_ref(v___x_5144_);
lean_dec_ref(v_P_5143_);
lean_dec(v_head_5142_);
lean_dec_ref(v___x_5141_);
lean_dec_ref(v_val_5140_);
lean_dec_ref(v___x_5139_);
v_a_5201_ = lean_ctor_get(v___x_5168_, 0);
v_isSharedCheck_5208_ = !lean_is_exclusive(v___x_5168_);
if (v_isSharedCheck_5208_ == 0)
{
v___x_5203_ = v___x_5168_;
v_isShared_5204_ = v_isSharedCheck_5208_;
goto v_resetjp_5202_;
}
else
{
lean_inc(v_a_5201_);
lean_dec(v___x_5168_);
v___x_5203_ = lean_box(0);
v_isShared_5204_ = v_isSharedCheck_5208_;
goto v_resetjp_5202_;
}
v_resetjp_5202_:
{
lean_object* v___x_5206_; 
if (v_isShared_5204_ == 0)
{
v___x_5206_ = v___x_5203_;
goto v_reusejp_5205_;
}
else
{
lean_object* v_reuseFailAlloc_5207_; 
v_reuseFailAlloc_5207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5207_, 0, v_a_5201_);
v___x_5206_ = v_reuseFailAlloc_5207_;
goto v_reusejp_5205_;
}
v_reusejp_5205_:
{
return v___x_5206_;
}
}
}
}
else
{
lean_object* v_a_5209_; lean_object* v___x_5211_; uint8_t v_isShared_5212_; uint8_t v_isSharedCheck_5216_; 
lean_dec(v___y_5164_);
lean_dec_ref(v___y_5163_);
lean_dec(v___y_5162_);
lean_dec_ref(v___y_5161_);
lean_dec(v_numFields_5159_);
lean_dec(v_numParams_5158_);
lean_dec(v___x_5157_);
lean_dec_ref(v___x_5156_);
lean_dec_ref(v___x_5153_);
lean_dec(v___x_5152_);
lean_dec(v___x_5151_);
lean_dec_ref(v___x_5150_);
lean_dec_ref(v___x_5149_);
lean_dec(v___x_5148_);
lean_dec(v___x_5147_);
lean_dec_ref(v_fields2_5146_);
lean_dec_ref(v_xs_5145_);
lean_dec_ref(v___x_5144_);
lean_dec_ref(v_P_5143_);
lean_dec(v_head_5142_);
lean_dec_ref(v___x_5141_);
lean_dec_ref(v_val_5140_);
lean_dec_ref(v___x_5139_);
v_a_5209_ = lean_ctor_get(v___x_5166_, 0);
v_isSharedCheck_5216_ = !lean_is_exclusive(v___x_5166_);
if (v_isSharedCheck_5216_ == 0)
{
v___x_5211_ = v___x_5166_;
v_isShared_5212_ = v_isSharedCheck_5216_;
goto v_resetjp_5210_;
}
else
{
lean_inc(v_a_5209_);
lean_dec(v___x_5166_);
v___x_5211_ = lean_box(0);
v_isShared_5212_ = v_isSharedCheck_5216_;
goto v_resetjp_5210_;
}
v_resetjp_5210_:
{
lean_object* v___x_5214_; 
if (v_isShared_5212_ == 0)
{
v___x_5214_ = v___x_5211_;
goto v_reusejp_5213_;
}
else
{
lean_object* v_reuseFailAlloc_5215_; 
v_reuseFailAlloc_5215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5215_, 0, v_a_5209_);
v___x_5214_ = v_reuseFailAlloc_5215_;
goto v_reusejp_5213_;
}
v_reusejp_5213_:
{
return v___x_5214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_5217_ = _args[0];
lean_object* v_val_5218_ = _args[1];
lean_object* v___x_5219_ = _args[2];
lean_object* v_head_5220_ = _args[3];
lean_object* v_P_5221_ = _args[4];
lean_object* v___x_5222_ = _args[5];
lean_object* v_xs_5223_ = _args[6];
lean_object* v_fields2_5224_ = _args[7];
lean_object* v___x_5225_ = _args[8];
lean_object* v___x_5226_ = _args[9];
lean_object* v___x_5227_ = _args[10];
lean_object* v___x_5228_ = _args[11];
lean_object* v___x_5229_ = _args[12];
lean_object* v___x_5230_ = _args[13];
lean_object* v___x_5231_ = _args[14];
lean_object* v_a_5232_ = _args[15];
lean_object* v___x_5233_ = _args[16];
lean_object* v___x_5234_ = _args[17];
lean_object* v___x_5235_ = _args[18];
lean_object* v_numParams_5236_ = _args[19];
lean_object* v_numFields_5237_ = _args[20];
lean_object* v___x_5238_ = _args[21];
lean_object* v___y_5239_ = _args[22];
lean_object* v___y_5240_ = _args[23];
lean_object* v___y_5241_ = _args[24];
lean_object* v___y_5242_ = _args[25];
lean_object* v___y_5243_ = _args[26];
_start:
{
uint8_t v_a_17975__boxed_5244_; uint8_t v___x_17976__boxed_5245_; lean_object* v_res_5246_; 
v_a_17975__boxed_5244_ = lean_unbox(v_a_5232_);
v___x_17976__boxed_5245_ = lean_unbox(v___x_5233_);
v_res_5246_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__2(v___x_5217_, v_val_5218_, v___x_5219_, v_head_5220_, v_P_5221_, v___x_5222_, v_xs_5223_, v_fields2_5224_, v___x_5225_, v___x_5226_, v___x_5227_, v___x_5228_, v___x_5229_, v___x_5230_, v___x_5231_, v_a_17975__boxed_5244_, v___x_17976__boxed_5245_, v___x_5234_, v___x_5235_, v_numParams_5236_, v_numFields_5237_, v___x_5238_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_);
return v_res_5246_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__3(lean_object* v_P_5247_, lean_object* v_xs_5248_, lean_object* v_fields1_5249_, lean_object* v_head_5250_, lean_object* v_tail_5251_, lean_object* v_val_5252_, lean_object* v___x_5253_, lean_object* v___x_5254_, lean_object* v___x_5255_, uint8_t v_a_5256_, uint8_t v___x_5257_, lean_object* v___x_5258_, lean_object* v___x_5259_, lean_object* v_numParams_5260_, lean_object* v_numFields_5261_, lean_object* v___x_5262_, lean_object* v_fields2_5263_, lean_object* v_x_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_){
_start:
{
lean_object* v___x_5270_; lean_object* v___x_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___f_5283_; lean_object* v___x_5284_; lean_object* v___x_5285_; 
v___x_5270_ = lean_unsigned_to_nat(1u);
v___x_5271_ = lean_mk_empty_array_with_capacity(v___x_5270_);
lean_inc_ref(v_P_5247_);
lean_inc_ref(v___x_5271_);
v___x_5272_ = lean_array_push(v___x_5271_, v_P_5247_);
lean_inc_ref_n(v_xs_5248_, 3);
v___x_5273_ = l_Array_append___redArg(v_xs_5248_, v___x_5272_);
v___x_5274_ = l_Array_append___redArg(v___x_5273_, v_fields1_5249_);
v___x_5275_ = l_Array_append___redArg(v___x_5274_, v_fields2_5263_);
lean_inc(v_head_5250_);
v___x_5276_ = l_Lean_mkConst(v_head_5250_, v_tail_5251_);
v___x_5277_ = l_Array_append___redArg(v_xs_5248_, v_fields1_5249_);
lean_inc_ref(v___x_5276_);
v___x_5278_ = l_Lean_mkAppN(v___x_5276_, v___x_5277_);
v___x_5279_ = l_Array_append___redArg(v_xs_5248_, v_fields2_5263_);
v___x_5280_ = l_Lean_mkAppN(v___x_5276_, v___x_5279_);
lean_dec_ref(v___x_5279_);
v___x_5281_ = lean_box(v_a_5256_);
v___x_5282_ = lean_box(v___x_5257_);
lean_inc_ref(v___x_5275_);
lean_inc_ref(v_fields2_5263_);
v___f_5283_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__2___boxed), 27, 22);
lean_closure_set(v___f_5283_, 0, v___x_5278_);
lean_closure_set(v___f_5283_, 1, v_val_5252_);
lean_closure_set(v___f_5283_, 2, v___x_5280_);
lean_closure_set(v___f_5283_, 3, v_head_5250_);
lean_closure_set(v___f_5283_, 4, v_P_5247_);
lean_closure_set(v___f_5283_, 5, v___x_5277_);
lean_closure_set(v___f_5283_, 6, v_xs_5248_);
lean_closure_set(v___f_5283_, 7, v_fields2_5263_);
lean_closure_set(v___f_5283_, 8, v___x_5253_);
lean_closure_set(v___f_5283_, 9, v___x_5254_);
lean_closure_set(v___f_5283_, 10, v___x_5272_);
lean_closure_set(v___f_5283_, 11, v___x_5271_);
lean_closure_set(v___f_5283_, 12, v___x_5255_);
lean_closure_set(v___f_5283_, 13, v___x_5270_);
lean_closure_set(v___f_5283_, 14, v___x_5275_);
lean_closure_set(v___f_5283_, 15, v___x_5281_);
lean_closure_set(v___f_5283_, 16, v___x_5282_);
lean_closure_set(v___f_5283_, 17, v___x_5258_);
lean_closure_set(v___f_5283_, 18, v___x_5259_);
lean_closure_set(v___f_5283_, 19, v_numParams_5260_);
lean_closure_set(v___f_5283_, 20, v_numFields_5261_);
lean_closure_set(v___f_5283_, 21, v___x_5262_);
v___x_5284_ = lean_alloc_closure((void*)(l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2___boxed), 8, 3);
lean_closure_set(v___x_5284_, 0, lean_box(0));
lean_closure_set(v___x_5284_, 1, v___x_5275_);
lean_closure_set(v___x_5284_, 2, v___f_5283_);
v___x_5285_ = l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__2___redArg(v_fields2_5263_, v___x_5284_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_);
return v___x_5285_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_P_5286_ = _args[0];
lean_object* v_xs_5287_ = _args[1];
lean_object* v_fields1_5288_ = _args[2];
lean_object* v_head_5289_ = _args[3];
lean_object* v_tail_5290_ = _args[4];
lean_object* v_val_5291_ = _args[5];
lean_object* v___x_5292_ = _args[6];
lean_object* v___x_5293_ = _args[7];
lean_object* v___x_5294_ = _args[8];
lean_object* v_a_5295_ = _args[9];
lean_object* v___x_5296_ = _args[10];
lean_object* v___x_5297_ = _args[11];
lean_object* v___x_5298_ = _args[12];
lean_object* v_numParams_5299_ = _args[13];
lean_object* v_numFields_5300_ = _args[14];
lean_object* v___x_5301_ = _args[15];
lean_object* v_fields2_5302_ = _args[16];
lean_object* v_x_5303_ = _args[17];
lean_object* v___y_5304_ = _args[18];
lean_object* v___y_5305_ = _args[19];
lean_object* v___y_5306_ = _args[20];
lean_object* v___y_5307_ = _args[21];
lean_object* v___y_5308_ = _args[22];
_start:
{
uint8_t v_a_18134__boxed_5309_; uint8_t v___x_18135__boxed_5310_; lean_object* v_res_5311_; 
v_a_18134__boxed_5309_ = lean_unbox(v_a_5295_);
v___x_18135__boxed_5310_ = lean_unbox(v___x_5296_);
v_res_5311_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__3(v_P_5286_, v_xs_5287_, v_fields1_5288_, v_head_5289_, v_tail_5290_, v_val_5291_, v___x_5292_, v___x_5293_, v___x_5294_, v_a_18134__boxed_5309_, v___x_18135__boxed_5310_, v___x_5297_, v___x_5298_, v_numParams_5299_, v_numFields_5300_, v___x_5301_, v_fields2_5302_, v_x_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_);
lean_dec(v___y_5307_);
lean_dec_ref(v___y_5306_);
lean_dec(v___y_5305_);
lean_dec_ref(v___y_5304_);
lean_dec_ref(v_x_5303_);
lean_dec_ref(v_fields1_5288_);
return v_res_5311_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__4(lean_object* v_P_5312_, lean_object* v_xs_5313_, lean_object* v_head_5314_, lean_object* v_tail_5315_, lean_object* v_val_5316_, lean_object* v___x_5317_, lean_object* v___x_5318_, lean_object* v___x_5319_, uint8_t v_a_5320_, uint8_t v___x_5321_, lean_object* v___x_5322_, lean_object* v___x_5323_, lean_object* v_numParams_5324_, lean_object* v_numFields_5325_, lean_object* v___x_5326_, lean_object* v_t_5327_, lean_object* v___x_5328_, lean_object* v_fields1_5329_, lean_object* v_x_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_){
_start:
{
lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___f_5338_; lean_object* v___x_5339_; 
v___x_5336_ = lean_box(v_a_5320_);
v___x_5337_ = lean_box(v___x_5321_);
v___f_5338_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__3___boxed), 23, 16);
lean_closure_set(v___f_5338_, 0, v_P_5312_);
lean_closure_set(v___f_5338_, 1, v_xs_5313_);
lean_closure_set(v___f_5338_, 2, v_fields1_5329_);
lean_closure_set(v___f_5338_, 3, v_head_5314_);
lean_closure_set(v___f_5338_, 4, v_tail_5315_);
lean_closure_set(v___f_5338_, 5, v_val_5316_);
lean_closure_set(v___f_5338_, 6, v___x_5317_);
lean_closure_set(v___f_5338_, 7, v___x_5318_);
lean_closure_set(v___f_5338_, 8, v___x_5319_);
lean_closure_set(v___f_5338_, 9, v___x_5336_);
lean_closure_set(v___f_5338_, 10, v___x_5337_);
lean_closure_set(v___f_5338_, 11, v___x_5322_);
lean_closure_set(v___f_5338_, 12, v___x_5323_);
lean_closure_set(v___f_5338_, 13, v_numParams_5324_);
lean_closure_set(v___f_5338_, 14, v_numFields_5325_);
lean_closure_set(v___f_5338_, 15, v___x_5326_);
v___x_5339_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(v_t_5327_, v___x_5328_, v___f_5338_, v_a_5320_, v_a_5320_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_);
return v___x_5339_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_P_5340_ = _args[0];
lean_object* v_xs_5341_ = _args[1];
lean_object* v_head_5342_ = _args[2];
lean_object* v_tail_5343_ = _args[3];
lean_object* v_val_5344_ = _args[4];
lean_object* v___x_5345_ = _args[5];
lean_object* v___x_5346_ = _args[6];
lean_object* v___x_5347_ = _args[7];
lean_object* v_a_5348_ = _args[8];
lean_object* v___x_5349_ = _args[9];
lean_object* v___x_5350_ = _args[10];
lean_object* v___x_5351_ = _args[11];
lean_object* v_numParams_5352_ = _args[12];
lean_object* v_numFields_5353_ = _args[13];
lean_object* v___x_5354_ = _args[14];
lean_object* v_t_5355_ = _args[15];
lean_object* v___x_5356_ = _args[16];
lean_object* v_fields1_5357_ = _args[17];
lean_object* v_x_5358_ = _args[18];
lean_object* v___y_5359_ = _args[19];
lean_object* v___y_5360_ = _args[20];
lean_object* v___y_5361_ = _args[21];
lean_object* v___y_5362_ = _args[22];
lean_object* v___y_5363_ = _args[23];
_start:
{
uint8_t v_a_18217__boxed_5364_; uint8_t v___x_18218__boxed_5365_; lean_object* v_res_5366_; 
v_a_18217__boxed_5364_ = lean_unbox(v_a_5348_);
v___x_18218__boxed_5365_ = lean_unbox(v___x_5349_);
v_res_5366_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__4(v_P_5340_, v_xs_5341_, v_head_5342_, v_tail_5343_, v_val_5344_, v___x_5345_, v___x_5346_, v___x_5347_, v_a_18217__boxed_5364_, v___x_18218__boxed_5365_, v___x_5350_, v___x_5351_, v_numParams_5352_, v_numFields_5353_, v___x_5354_, v_t_5355_, v___x_5356_, v_fields1_5357_, v_x_5358_, v___y_5359_, v___y_5360_, v___y_5361_, v___y_5362_);
lean_dec(v___y_5362_);
lean_dec_ref(v___y_5361_);
lean_dec(v___y_5360_);
lean_dec_ref(v___y_5359_);
lean_dec_ref(v_x_5358_);
return v_res_5366_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__5(lean_object* v_numFields_5367_, lean_object* v_xs_5368_, lean_object* v_head_5369_, lean_object* v_tail_5370_, lean_object* v_val_5371_, lean_object* v___x_5372_, lean_object* v___x_5373_, lean_object* v___x_5374_, uint8_t v_a_5375_, uint8_t v___x_5376_, lean_object* v___x_5377_, lean_object* v___x_5378_, lean_object* v_numParams_5379_, lean_object* v___x_5380_, lean_object* v_t_5381_, lean_object* v_P_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_){
_start:
{
lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___f_5391_; lean_object* v___x_5392_; 
lean_inc(v_numFields_5367_);
v___x_5388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5388_, 0, v_numFields_5367_);
v___x_5389_ = lean_box(v_a_5375_);
v___x_5390_ = lean_box(v___x_5376_);
lean_inc_ref(v___x_5388_);
lean_inc_ref(v_t_5381_);
v___f_5391_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__4___boxed), 24, 17);
lean_closure_set(v___f_5391_, 0, v_P_5382_);
lean_closure_set(v___f_5391_, 1, v_xs_5368_);
lean_closure_set(v___f_5391_, 2, v_head_5369_);
lean_closure_set(v___f_5391_, 3, v_tail_5370_);
lean_closure_set(v___f_5391_, 4, v_val_5371_);
lean_closure_set(v___f_5391_, 5, v___x_5372_);
lean_closure_set(v___f_5391_, 6, v___x_5373_);
lean_closure_set(v___f_5391_, 7, v___x_5374_);
lean_closure_set(v___f_5391_, 8, v___x_5389_);
lean_closure_set(v___f_5391_, 9, v___x_5390_);
lean_closure_set(v___f_5391_, 10, v___x_5377_);
lean_closure_set(v___f_5391_, 11, v___x_5378_);
lean_closure_set(v___f_5391_, 12, v_numParams_5379_);
lean_closure_set(v___f_5391_, 13, v_numFields_5367_);
lean_closure_set(v___f_5391_, 14, v___x_5380_);
lean_closure_set(v___f_5391_, 15, v_t_5381_);
lean_closure_set(v___f_5391_, 16, v___x_5388_);
v___x_5392_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(v_t_5381_, v___x_5388_, v___f_5391_, v_a_5375_, v_a_5375_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_);
return v___x_5392_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_numFields_5393_ = _args[0];
lean_object* v_xs_5394_ = _args[1];
lean_object* v_head_5395_ = _args[2];
lean_object* v_tail_5396_ = _args[3];
lean_object* v_val_5397_ = _args[4];
lean_object* v___x_5398_ = _args[5];
lean_object* v___x_5399_ = _args[6];
lean_object* v___x_5400_ = _args[7];
lean_object* v_a_5401_ = _args[8];
lean_object* v___x_5402_ = _args[9];
lean_object* v___x_5403_ = _args[10];
lean_object* v___x_5404_ = _args[11];
lean_object* v_numParams_5405_ = _args[12];
lean_object* v___x_5406_ = _args[13];
lean_object* v_t_5407_ = _args[14];
lean_object* v_P_5408_ = _args[15];
lean_object* v___y_5409_ = _args[16];
lean_object* v___y_5410_ = _args[17];
lean_object* v___y_5411_ = _args[18];
lean_object* v___y_5412_ = _args[19];
lean_object* v___y_5413_ = _args[20];
_start:
{
uint8_t v_a_18279__boxed_5414_; uint8_t v___x_18280__boxed_5415_; lean_object* v_res_5416_; 
v_a_18279__boxed_5414_ = lean_unbox(v_a_5401_);
v___x_18280__boxed_5415_ = lean_unbox(v___x_5402_);
v_res_5416_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__5(v_numFields_5393_, v_xs_5394_, v_head_5395_, v_tail_5396_, v_val_5397_, v___x_5398_, v___x_5399_, v___x_5400_, v_a_18279__boxed_5414_, v___x_18280__boxed_5415_, v___x_5403_, v___x_5404_, v_numParams_5405_, v___x_5406_, v_t_5407_, v_P_5408_, v___y_5409_, v___y_5410_, v___y_5411_, v___y_5412_);
lean_dec(v___y_5412_);
lean_dec_ref(v___y_5411_);
lean_dec(v___y_5410_);
lean_dec_ref(v___y_5409_);
return v_res_5416_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__6(lean_object* v_numFields_5417_, lean_object* v_head_5418_, lean_object* v_tail_5419_, lean_object* v_val_5420_, lean_object* v___x_5421_, lean_object* v___x_5422_, lean_object* v___x_5423_, uint8_t v_a_5424_, uint8_t v___x_5425_, lean_object* v___x_5426_, lean_object* v___x_5427_, lean_object* v_numParams_5428_, lean_object* v___x_5429_, lean_object* v_head_5430_, lean_object* v_xs_5431_, lean_object* v_t_5432_, lean_object* v___y_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_, lean_object* v___y_5436_){
_start:
{
lean_object* v___x_5438_; lean_object* v___x_5439_; lean_object* v___f_5440_; lean_object* v___x_5441_; lean_object* v___x_5442_; lean_object* v___x_5443_; 
v___x_5438_ = lean_box(v_a_5424_);
v___x_5439_ = lean_box(v___x_5425_);
v___f_5440_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__5___boxed), 21, 15);
lean_closure_set(v___f_5440_, 0, v_numFields_5417_);
lean_closure_set(v___f_5440_, 1, v_xs_5431_);
lean_closure_set(v___f_5440_, 2, v_head_5418_);
lean_closure_set(v___f_5440_, 3, v_tail_5419_);
lean_closure_set(v___f_5440_, 4, v_val_5420_);
lean_closure_set(v___f_5440_, 5, v___x_5421_);
lean_closure_set(v___f_5440_, 6, v___x_5422_);
lean_closure_set(v___f_5440_, 7, v___x_5423_);
lean_closure_set(v___f_5440_, 8, v___x_5438_);
lean_closure_set(v___f_5440_, 9, v___x_5439_);
lean_closure_set(v___f_5440_, 10, v___x_5426_);
lean_closure_set(v___f_5440_, 11, v___x_5427_);
lean_closure_set(v___f_5440_, 12, v_numParams_5428_);
lean_closure_set(v___f_5440_, 13, v___x_5429_);
lean_closure_set(v___f_5440_, 14, v_t_5432_);
v___x_5441_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__1));
v___x_5442_ = l_Lean_Expr_sort___override(v_head_5430_);
v___x_5443_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_5441_, v___x_5442_, v___f_5440_, v___y_5433_, v___y_5434_, v___y_5435_, v___y_5436_);
return v___x_5443_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_numFields_5444_ = _args[0];
lean_object* v_head_5445_ = _args[1];
lean_object* v_tail_5446_ = _args[2];
lean_object* v_val_5447_ = _args[3];
lean_object* v___x_5448_ = _args[4];
lean_object* v___x_5449_ = _args[5];
lean_object* v___x_5450_ = _args[6];
lean_object* v_a_5451_ = _args[7];
lean_object* v___x_5452_ = _args[8];
lean_object* v___x_5453_ = _args[9];
lean_object* v___x_5454_ = _args[10];
lean_object* v_numParams_5455_ = _args[11];
lean_object* v___x_5456_ = _args[12];
lean_object* v_head_5457_ = _args[13];
lean_object* v_xs_5458_ = _args[14];
lean_object* v_t_5459_ = _args[15];
lean_object* v___y_5460_ = _args[16];
lean_object* v___y_5461_ = _args[17];
lean_object* v___y_5462_ = _args[18];
lean_object* v___y_5463_ = _args[19];
lean_object* v___y_5464_ = _args[20];
_start:
{
uint8_t v_a_18340__boxed_5465_; uint8_t v___x_18341__boxed_5466_; lean_object* v_res_5467_; 
v_a_18340__boxed_5465_ = lean_unbox(v_a_5451_);
v___x_18341__boxed_5466_ = lean_unbox(v___x_5452_);
v_res_5467_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__6(v_numFields_5444_, v_head_5445_, v_tail_5446_, v_val_5447_, v___x_5448_, v___x_5449_, v___x_5450_, v_a_18340__boxed_5465_, v___x_18341__boxed_5466_, v___x_5453_, v___x_5454_, v_numParams_5455_, v___x_5456_, v_head_5457_, v_xs_5458_, v_t_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_);
lean_dec(v___y_5463_);
lean_dec_ref(v___y_5462_);
lean_dec(v___y_5461_);
lean_dec_ref(v___y_5460_);
return v_res_5467_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg(lean_object* v_tail_5468_, lean_object* v_val_5469_, lean_object* v___x_5470_, lean_object* v___x_5471_, uint8_t v_a_5472_, lean_object* v___x_5473_, lean_object* v_head_5474_, lean_object* v_as_x27_5475_, lean_object* v_b_5476_, lean_object* v___y_5477_, lean_object* v___y_5478_, lean_object* v___y_5479_, lean_object* v___y_5480_){
_start:
{
if (lean_obj_tag(v_as_x27_5475_) == 0)
{
lean_object* v___x_5482_; 
lean_dec(v_head_5474_);
lean_dec(v___x_5473_);
lean_dec(v___x_5471_);
lean_dec(v___x_5470_);
lean_dec_ref(v_val_5469_);
lean_dec(v_tail_5468_);
v___x_5482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5482_, 0, v_b_5476_);
return v___x_5482_;
}
else
{
lean_object* v_head_5483_; lean_object* v_tail_5484_; lean_object* v___x_5485_; 
v_head_5483_ = lean_ctor_get(v_as_x27_5475_, 0);
v_tail_5484_ = lean_ctor_get(v_as_x27_5475_, 1);
lean_inc(v_head_5483_);
v___x_5485_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0(v_head_5483_, v___y_5477_, v___y_5478_, v___y_5479_, v___y_5480_);
if (lean_obj_tag(v___x_5485_) == 0)
{
lean_object* v_a_5486_; lean_object* v_toConstantVal_5487_; lean_object* v_numParams_5488_; lean_object* v_numFields_5489_; lean_object* v___x_5490_; lean_object* v___x_5491_; uint8_t v___x_5492_; 
v_a_5486_ = lean_ctor_get(v___x_5485_, 0);
lean_inc(v_a_5486_);
lean_dec_ref_known(v___x_5485_, 1);
v_toConstantVal_5487_ = lean_ctor_get(v_a_5486_, 0);
lean_inc_ref(v_toConstantVal_5487_);
v_numParams_5488_ = lean_ctor_get(v_a_5486_, 3);
lean_inc(v_numParams_5488_);
v_numFields_5489_ = lean_ctor_get(v_a_5486_, 4);
lean_inc(v_numFields_5489_);
lean_dec(v_a_5486_);
v___x_5490_ = lean_box(0);
v___x_5491_ = lean_unsigned_to_nat(0u);
v___x_5492_ = lean_nat_dec_lt(v___x_5491_, v_numFields_5489_);
if (v___x_5492_ == 0)
{
lean_dec(v_numFields_5489_);
lean_dec(v_numParams_5488_);
lean_dec_ref(v_toConstantVal_5487_);
v_as_x27_5475_ = v_tail_5484_;
v_b_5476_ = v___x_5490_;
goto _start;
}
else
{
lean_object* v_type_5494_; lean_object* v___x_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; lean_object* v___f_5498_; lean_object* v___x_5499_; lean_object* v___x_5500_; 
v_type_5494_ = lean_ctor_get(v_toConstantVal_5487_, 2);
lean_inc_ref(v_type_5494_);
lean_dec_ref(v_toConstantVal_5487_);
v___x_5495_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__0));
v___x_5496_ = lean_box(v_a_5472_);
v___x_5497_ = lean_box(v___x_5492_);
lean_inc(v_head_5474_);
lean_inc(v_numParams_5488_);
lean_inc(v___x_5473_);
lean_inc(v___x_5471_);
lean_inc(v___x_5470_);
lean_inc_ref(v_val_5469_);
lean_inc(v_tail_5468_);
lean_inc(v_head_5483_);
v___f_5498_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__6___boxed), 21, 14);
lean_closure_set(v___f_5498_, 0, v_numFields_5489_);
lean_closure_set(v___f_5498_, 1, v_head_5483_);
lean_closure_set(v___f_5498_, 2, v_tail_5468_);
lean_closure_set(v___f_5498_, 3, v_val_5469_);
lean_closure_set(v___f_5498_, 4, v___x_5470_);
lean_closure_set(v___f_5498_, 5, v___x_5471_);
lean_closure_set(v___f_5498_, 6, v___x_5491_);
lean_closure_set(v___f_5498_, 7, v___x_5496_);
lean_closure_set(v___f_5498_, 8, v___x_5497_);
lean_closure_set(v___f_5498_, 9, v___x_5495_);
lean_closure_set(v___f_5498_, 10, v___x_5473_);
lean_closure_set(v___f_5498_, 11, v_numParams_5488_);
lean_closure_set(v___f_5498_, 12, v___x_5490_);
lean_closure_set(v___f_5498_, 13, v_head_5474_);
v___x_5499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5499_, 0, v_numParams_5488_);
v___x_5500_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(v_type_5494_, v___x_5499_, v___f_5498_, v_a_5472_, v_a_5472_, v___y_5477_, v___y_5478_, v___y_5479_, v___y_5480_);
if (lean_obj_tag(v___x_5500_) == 0)
{
lean_dec_ref_known(v___x_5500_, 1);
v_as_x27_5475_ = v_tail_5484_;
v_b_5476_ = v___x_5490_;
goto _start;
}
else
{
lean_dec(v_head_5474_);
lean_dec(v___x_5473_);
lean_dec(v___x_5471_);
lean_dec(v___x_5470_);
lean_dec_ref(v_val_5469_);
lean_dec(v_tail_5468_);
return v___x_5500_;
}
}
}
else
{
lean_object* v_a_5502_; lean_object* v___x_5504_; uint8_t v_isShared_5505_; uint8_t v_isSharedCheck_5509_; 
lean_dec(v_head_5474_);
lean_dec(v___x_5473_);
lean_dec(v___x_5471_);
lean_dec(v___x_5470_);
lean_dec_ref(v_val_5469_);
lean_dec(v_tail_5468_);
v_a_5502_ = lean_ctor_get(v___x_5485_, 0);
v_isSharedCheck_5509_ = !lean_is_exclusive(v___x_5485_);
if (v_isSharedCheck_5509_ == 0)
{
v___x_5504_ = v___x_5485_;
v_isShared_5505_ = v_isSharedCheck_5509_;
goto v_resetjp_5503_;
}
else
{
lean_inc(v_a_5502_);
lean_dec(v___x_5485_);
v___x_5504_ = lean_box(0);
v_isShared_5505_ = v_isSharedCheck_5509_;
goto v_resetjp_5503_;
}
v_resetjp_5503_:
{
lean_object* v___x_5507_; 
if (v_isShared_5505_ == 0)
{
v___x_5507_ = v___x_5504_;
goto v_reusejp_5506_;
}
else
{
lean_object* v_reuseFailAlloc_5508_; 
v_reuseFailAlloc_5508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5508_, 0, v_a_5502_);
v___x_5507_ = v_reuseFailAlloc_5508_;
goto v_reusejp_5506_;
}
v_reusejp_5506_:
{
return v___x_5507_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___boxed(lean_object* v_tail_5510_, lean_object* v_val_5511_, lean_object* v___x_5512_, lean_object* v___x_5513_, lean_object* v_a_5514_, lean_object* v___x_5515_, lean_object* v_head_5516_, lean_object* v_as_x27_5517_, lean_object* v_b_5518_, lean_object* v___y_5519_, lean_object* v___y_5520_, lean_object* v___y_5521_, lean_object* v___y_5522_, lean_object* v___y_5523_){
_start:
{
uint8_t v_a_18403__boxed_5524_; lean_object* v_res_5525_; 
v_a_18403__boxed_5524_ = lean_unbox(v_a_5514_);
v_res_5525_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg(v_tail_5510_, v_val_5511_, v___x_5512_, v___x_5513_, v_a_18403__boxed_5524_, v___x_5515_, v_head_5516_, v_as_x27_5517_, v_b_5518_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_);
lean_dec(v___y_5522_);
lean_dec_ref(v___y_5521_);
lean_dec(v___y_5520_);
lean_dec_ref(v___y_5519_);
lean_dec(v_as_x27_5517_);
return v_res_5525_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors___closed__1(void){
_start:
{
lean_object* v___x_5527_; lean_object* v___x_5528_; 
v___x_5527_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors___closed__0));
v___x_5528_ = l_Lean_stringToMessageData(v___x_5527_);
return v___x_5528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors(lean_object* v_declName_5529_, lean_object* v_a_5530_, lean_object* v_a_5531_, lean_object* v_a_5532_, lean_object* v_a_5533_){
_start:
{
lean_object* v___x_5535_; 
lean_inc(v_declName_5529_);
v___x_5535_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(v_declName_5529_, v_a_5530_, v_a_5531_, v_a_5532_, v_a_5533_);
if (lean_obj_tag(v___x_5535_) == 0)
{
lean_object* v_a_5536_; lean_object* v___x_5538_; uint8_t v_isShared_5539_; uint8_t v_isSharedCheck_5625_; 
v_a_5536_ = lean_ctor_get(v___x_5535_, 0);
v_isSharedCheck_5625_ = !lean_is_exclusive(v___x_5535_);
if (v_isSharedCheck_5625_ == 0)
{
v___x_5538_ = v___x_5535_;
v_isShared_5539_ = v_isSharedCheck_5625_;
goto v_resetjp_5537_;
}
else
{
lean_inc(v_a_5536_);
lean_dec(v___x_5535_);
v___x_5538_ = lean_box(0);
v_isShared_5539_ = v_isSharedCheck_5625_;
goto v_resetjp_5537_;
}
v_resetjp_5537_:
{
if (lean_obj_tag(v_a_5536_) == 5)
{
lean_object* v_val_5540_; lean_object* v___x_5541_; uint8_t v___x_5542_; lean_object* v___x_5543_; lean_object* v_a_5544_; lean_object* v___x_5546_; uint8_t v_isShared_5547_; uint8_t v_isSharedCheck_5620_; 
lean_del_object(v___x_5538_);
v_val_5540_ = lean_ctor_get(v_a_5536_, 0);
lean_inc_ref(v_val_5540_);
lean_dec_ref_known(v_a_5536_, 1);
lean_inc(v_declName_5529_);
v___x_5541_ = l_Lean_mkCasesOnName(v_declName_5529_);
v___x_5542_ = 1;
lean_inc(v___x_5541_);
v___x_5543_ = l_Lean_hasConst___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__1___redArg(v___x_5541_, v___x_5542_, v_a_5533_);
v_a_5544_ = lean_ctor_get(v___x_5543_, 0);
v_isSharedCheck_5620_ = !lean_is_exclusive(v___x_5543_);
if (v_isSharedCheck_5620_ == 0)
{
v___x_5546_ = v___x_5543_;
v_isShared_5547_ = v_isSharedCheck_5620_;
goto v_resetjp_5545_;
}
else
{
lean_inc(v_a_5544_);
lean_dec(v___x_5543_);
v___x_5546_ = lean_box(0);
v_isShared_5547_ = v_isSharedCheck_5620_;
goto v_resetjp_5545_;
}
v_resetjp_5545_:
{
uint8_t v___x_5548_; 
v___x_5548_ = lean_unbox(v_a_5544_);
lean_dec(v_a_5544_);
if (v___x_5548_ == 0)
{
lean_object* v___x_5549_; lean_object* v___x_5551_; 
lean_dec(v___x_5541_);
lean_dec_ref(v_val_5540_);
lean_dec(v_declName_5529_);
v___x_5549_ = lean_box(0);
if (v_isShared_5547_ == 0)
{
lean_ctor_set(v___x_5546_, 0, v___x_5549_);
v___x_5551_ = v___x_5546_;
goto v_reusejp_5550_;
}
else
{
lean_object* v_reuseFailAlloc_5552_; 
v_reuseFailAlloc_5552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5552_, 0, v___x_5549_);
v___x_5551_ = v_reuseFailAlloc_5552_;
goto v_reusejp_5550_;
}
v_reusejp_5550_:
{
return v___x_5551_;
}
}
else
{
lean_object* v___x_5553_; 
lean_del_object(v___x_5546_);
v___x_5553_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(v___x_5541_, v_a_5530_, v_a_5531_, v_a_5532_, v_a_5533_);
if (lean_obj_tag(v___x_5553_) == 0)
{
lean_object* v_toConstantVal_5554_; lean_object* v_a_5555_; lean_object* v___x_5557_; uint8_t v_isShared_5558_; uint8_t v_isSharedCheck_5611_; 
v_toConstantVal_5554_ = lean_ctor_get(v_val_5540_, 0);
v_a_5555_ = lean_ctor_get(v___x_5553_, 0);
v_isSharedCheck_5611_ = !lean_is_exclusive(v___x_5553_);
if (v_isSharedCheck_5611_ == 0)
{
v___x_5557_ = v___x_5553_;
v_isShared_5558_ = v_isSharedCheck_5611_;
goto v_resetjp_5556_;
}
else
{
lean_inc(v_a_5555_);
lean_dec(v___x_5553_);
v___x_5557_ = lean_box(0);
v_isShared_5558_ = v_isSharedCheck_5611_;
goto v_resetjp_5556_;
}
v_resetjp_5556_:
{
lean_object* v_ctors_5559_; lean_object* v_levelParams_5560_; lean_object* v_type_5561_; lean_object* v___x_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; uint8_t v___x_5565_; 
v_ctors_5559_ = lean_ctor_get(v_val_5540_, 4);
lean_inc(v_ctors_5559_);
v_levelParams_5560_ = lean_ctor_get(v_toConstantVal_5554_, 1);
v_type_5561_ = lean_ctor_get(v_toConstantVal_5554_, 2);
v___x_5562_ = l_List_lengthTR___redArg(v_levelParams_5560_);
v___x_5563_ = l_Lean_ConstantInfo_levelParams(v_a_5555_);
v___x_5564_ = l_List_lengthTR___redArg(v___x_5563_);
v___x_5565_ = lean_nat_dec_lt(v___x_5562_, v___x_5564_);
lean_dec(v___x_5564_);
lean_dec(v___x_5562_);
if (v___x_5565_ == 0)
{
lean_object* v___x_5566_; lean_object* v___x_5568_; 
lean_dec(v___x_5563_);
lean_dec(v_ctors_5559_);
lean_dec(v_a_5555_);
lean_dec_ref(v_val_5540_);
lean_dec(v_declName_5529_);
v___x_5566_ = lean_box(0);
if (v_isShared_5558_ == 0)
{
lean_ctor_set(v___x_5557_, 0, v___x_5566_);
v___x_5568_ = v___x_5557_;
goto v_reusejp_5567_;
}
else
{
lean_object* v_reuseFailAlloc_5569_; 
v_reuseFailAlloc_5569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5569_, 0, v___x_5566_);
v___x_5568_ = v_reuseFailAlloc_5569_;
goto v_reusejp_5567_;
}
v_reusejp_5567_:
{
return v___x_5568_;
}
}
else
{
lean_object* v___x_5570_; 
lean_del_object(v___x_5557_);
lean_inc_ref(v_type_5561_);
v___x_5570_ = l_Lean_Meta_isPropFormerType(v_type_5561_, v_a_5530_, v_a_5531_, v_a_5532_, v_a_5533_);
if (lean_obj_tag(v___x_5570_) == 0)
{
lean_object* v_a_5571_; lean_object* v___x_5573_; uint8_t v_isShared_5574_; uint8_t v_isSharedCheck_5602_; 
v_a_5571_ = lean_ctor_get(v___x_5570_, 0);
v_isSharedCheck_5602_ = !lean_is_exclusive(v___x_5570_);
if (v_isSharedCheck_5602_ == 0)
{
v___x_5573_ = v___x_5570_;
v_isShared_5574_ = v_isSharedCheck_5602_;
goto v_resetjp_5572_;
}
else
{
lean_inc(v_a_5571_);
lean_dec(v___x_5570_);
v___x_5573_ = lean_box(0);
v_isShared_5574_ = v_isSharedCheck_5602_;
goto v_resetjp_5572_;
}
v_resetjp_5572_:
{
uint8_t v___x_5575_; 
v___x_5575_ = lean_unbox(v_a_5571_);
if (v___x_5575_ == 0)
{
lean_object* v___x_5576_; lean_object* v___x_5577_; 
lean_del_object(v___x_5573_);
v___x_5576_ = lean_box(0);
lean_inc(v___x_5563_);
v___x_5577_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__2(v___x_5563_, v___x_5576_);
if (lean_obj_tag(v___x_5577_) == 1)
{
lean_object* v_head_5578_; lean_object* v_tail_5579_; lean_object* v___x_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; uint8_t v___x_5583_; lean_object* v___x_5584_; 
lean_dec(v_a_5555_);
v_head_5578_ = lean_ctor_get(v___x_5577_, 0);
lean_inc(v_head_5578_);
v_tail_5579_ = lean_ctor_get(v___x_5577_, 1);
lean_inc(v_tail_5579_);
v___x_5580_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__0));
v___x_5581_ = l_Lean_Name_str___override(v_declName_5529_, v___x_5580_);
v___x_5582_ = lean_box(0);
v___x_5583_ = lean_unbox(v_a_5571_);
lean_dec(v_a_5571_);
v___x_5584_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg(v_tail_5579_, v_val_5540_, v___x_5581_, v___x_5577_, v___x_5583_, v___x_5563_, v_head_5578_, v_ctors_5559_, v___x_5582_, v_a_5530_, v_a_5531_, v_a_5532_, v_a_5533_);
lean_dec(v_ctors_5559_);
if (lean_obj_tag(v___x_5584_) == 0)
{
lean_object* v___x_5586_; uint8_t v_isShared_5587_; uint8_t v_isSharedCheck_5591_; 
v_isSharedCheck_5591_ = !lean_is_exclusive(v___x_5584_);
if (v_isSharedCheck_5591_ == 0)
{
lean_object* v_unused_5592_; 
v_unused_5592_ = lean_ctor_get(v___x_5584_, 0);
lean_dec(v_unused_5592_);
v___x_5586_ = v___x_5584_;
v_isShared_5587_ = v_isSharedCheck_5591_;
goto v_resetjp_5585_;
}
else
{
lean_dec(v___x_5584_);
v___x_5586_ = lean_box(0);
v_isShared_5587_ = v_isSharedCheck_5591_;
goto v_resetjp_5585_;
}
v_resetjp_5585_:
{
lean_object* v___x_5589_; 
if (v_isShared_5587_ == 0)
{
lean_ctor_set(v___x_5586_, 0, v___x_5582_);
v___x_5589_ = v___x_5586_;
goto v_reusejp_5588_;
}
else
{
lean_object* v_reuseFailAlloc_5590_; 
v_reuseFailAlloc_5590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5590_, 0, v___x_5582_);
v___x_5589_ = v_reuseFailAlloc_5590_;
goto v_reusejp_5588_;
}
v_reusejp_5588_:
{
return v___x_5589_;
}
}
}
else
{
return v___x_5584_;
}
}
else
{
lean_object* v___x_5593_; lean_object* v___x_5594_; lean_object* v___x_5595_; lean_object* v___x_5596_; lean_object* v___x_5597_; 
lean_dec(v___x_5577_);
lean_dec(v_a_5571_);
lean_dec(v___x_5563_);
lean_dec(v_ctors_5559_);
lean_dec_ref(v_val_5540_);
lean_dec(v_declName_5529_);
v___x_5593_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors___closed__1, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors___closed__1_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors___closed__1);
v___x_5594_ = l_Lean_ConstantInfo_name(v_a_5555_);
lean_dec(v_a_5555_);
v___x_5595_ = l_Lean_MessageData_ofName(v___x_5594_);
v___x_5596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5596_, 0, v___x_5593_);
lean_ctor_set(v___x_5596_, 1, v___x_5595_);
v___x_5597_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0___redArg(v___x_5596_, v_a_5530_, v_a_5531_, v_a_5532_, v_a_5533_);
return v___x_5597_;
}
}
else
{
lean_object* v___x_5598_; lean_object* v___x_5600_; 
lean_dec(v_a_5571_);
lean_dec(v___x_5563_);
lean_dec(v_ctors_5559_);
lean_dec(v_a_5555_);
lean_dec_ref(v_val_5540_);
lean_dec(v_declName_5529_);
v___x_5598_ = lean_box(0);
if (v_isShared_5574_ == 0)
{
lean_ctor_set(v___x_5573_, 0, v___x_5598_);
v___x_5600_ = v___x_5573_;
goto v_reusejp_5599_;
}
else
{
lean_object* v_reuseFailAlloc_5601_; 
v_reuseFailAlloc_5601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5601_, 0, v___x_5598_);
v___x_5600_ = v_reuseFailAlloc_5601_;
goto v_reusejp_5599_;
}
v_reusejp_5599_:
{
return v___x_5600_;
}
}
}
}
else
{
lean_object* v_a_5603_; lean_object* v___x_5605_; uint8_t v_isShared_5606_; uint8_t v_isSharedCheck_5610_; 
lean_dec(v___x_5563_);
lean_dec(v_ctors_5559_);
lean_dec(v_a_5555_);
lean_dec_ref(v_val_5540_);
lean_dec(v_declName_5529_);
v_a_5603_ = lean_ctor_get(v___x_5570_, 0);
v_isSharedCheck_5610_ = !lean_is_exclusive(v___x_5570_);
if (v_isSharedCheck_5610_ == 0)
{
v___x_5605_ = v___x_5570_;
v_isShared_5606_ = v_isSharedCheck_5610_;
goto v_resetjp_5604_;
}
else
{
lean_inc(v_a_5603_);
lean_dec(v___x_5570_);
v___x_5605_ = lean_box(0);
v_isShared_5606_ = v_isSharedCheck_5610_;
goto v_resetjp_5604_;
}
v_resetjp_5604_:
{
lean_object* v___x_5608_; 
if (v_isShared_5606_ == 0)
{
v___x_5608_ = v___x_5605_;
goto v_reusejp_5607_;
}
else
{
lean_object* v_reuseFailAlloc_5609_; 
v_reuseFailAlloc_5609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5609_, 0, v_a_5603_);
v___x_5608_ = v_reuseFailAlloc_5609_;
goto v_reusejp_5607_;
}
v_reusejp_5607_:
{
return v___x_5608_;
}
}
}
}
}
}
else
{
lean_object* v_a_5612_; lean_object* v___x_5614_; uint8_t v_isShared_5615_; uint8_t v_isSharedCheck_5619_; 
lean_dec_ref(v_val_5540_);
lean_dec(v_declName_5529_);
v_a_5612_ = lean_ctor_get(v___x_5553_, 0);
v_isSharedCheck_5619_ = !lean_is_exclusive(v___x_5553_);
if (v_isSharedCheck_5619_ == 0)
{
v___x_5614_ = v___x_5553_;
v_isShared_5615_ = v_isSharedCheck_5619_;
goto v_resetjp_5613_;
}
else
{
lean_inc(v_a_5612_);
lean_dec(v___x_5553_);
v___x_5614_ = lean_box(0);
v_isShared_5615_ = v_isSharedCheck_5619_;
goto v_resetjp_5613_;
}
v_resetjp_5613_:
{
lean_object* v___x_5617_; 
if (v_isShared_5615_ == 0)
{
v___x_5617_ = v___x_5614_;
goto v_reusejp_5616_;
}
else
{
lean_object* v_reuseFailAlloc_5618_; 
v_reuseFailAlloc_5618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5618_, 0, v_a_5612_);
v___x_5617_ = v_reuseFailAlloc_5618_;
goto v_reusejp_5616_;
}
v_reusejp_5616_:
{
return v___x_5617_;
}
}
}
}
}
}
else
{
lean_object* v___x_5621_; lean_object* v___x_5623_; 
lean_dec(v_a_5536_);
lean_dec(v_declName_5529_);
v___x_5621_ = lean_box(0);
if (v_isShared_5539_ == 0)
{
lean_ctor_set(v___x_5538_, 0, v___x_5621_);
v___x_5623_ = v___x_5538_;
goto v_reusejp_5622_;
}
else
{
lean_object* v_reuseFailAlloc_5624_; 
v_reuseFailAlloc_5624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5624_, 0, v___x_5621_);
v___x_5623_ = v_reuseFailAlloc_5624_;
goto v_reusejp_5622_;
}
v_reusejp_5622_:
{
return v___x_5623_;
}
}
}
}
else
{
lean_object* v_a_5626_; lean_object* v___x_5628_; uint8_t v_isShared_5629_; uint8_t v_isSharedCheck_5633_; 
lean_dec(v_declName_5529_);
v_a_5626_ = lean_ctor_get(v___x_5535_, 0);
v_isSharedCheck_5633_ = !lean_is_exclusive(v___x_5535_);
if (v_isSharedCheck_5633_ == 0)
{
v___x_5628_ = v___x_5535_;
v_isShared_5629_ = v_isSharedCheck_5633_;
goto v_resetjp_5627_;
}
else
{
lean_inc(v_a_5626_);
lean_dec(v___x_5535_);
v___x_5628_ = lean_box(0);
v_isShared_5629_ = v_isSharedCheck_5633_;
goto v_resetjp_5627_;
}
v_resetjp_5627_:
{
lean_object* v___x_5631_; 
if (v_isShared_5629_ == 0)
{
v___x_5631_ = v___x_5628_;
goto v_reusejp_5630_;
}
else
{
lean_object* v_reuseFailAlloc_5632_; 
v_reuseFailAlloc_5632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5632_, 0, v_a_5626_);
v___x_5631_ = v_reuseFailAlloc_5632_;
goto v_reusejp_5630_;
}
v_reusejp_5630_:
{
return v___x_5631_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors___boxed(lean_object* v_declName_5634_, lean_object* v_a_5635_, lean_object* v_a_5636_, lean_object* v_a_5637_, lean_object* v_a_5638_, lean_object* v_a_5639_){
_start:
{
lean_object* v_res_5640_; 
v_res_5640_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors(v_declName_5634_, v_a_5635_, v_a_5636_, v_a_5637_, v_a_5638_);
lean_dec(v_a_5638_);
lean_dec_ref(v_a_5637_);
lean_dec(v_a_5636_);
lean_dec_ref(v_a_5635_);
return v_res_5640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0(lean_object* v_range_5641_, lean_object* v_b_5642_, lean_object* v_i_5643_, lean_object* v_hs_5644_, lean_object* v_hl_5645_, lean_object* v___y_5646_, lean_object* v___y_5647_, lean_object* v___y_5648_, lean_object* v___y_5649_){
_start:
{
lean_object* v___x_5651_; 
v___x_5651_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg(v_range_5641_, v_b_5642_, v_i_5643_, v___y_5646_, v___y_5647_, v___y_5648_, v___y_5649_);
return v___x_5651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___boxed(lean_object* v_range_5652_, lean_object* v_b_5653_, lean_object* v_i_5654_, lean_object* v_hs_5655_, lean_object* v_hl_5656_, lean_object* v___y_5657_, lean_object* v___y_5658_, lean_object* v___y_5659_, lean_object* v___y_5660_, lean_object* v___y_5661_){
_start:
{
lean_object* v_res_5662_; 
v_res_5662_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0(v_range_5652_, v_b_5653_, v_i_5654_, v_hs_5655_, v_hl_5656_, v___y_5657_, v___y_5658_, v___y_5659_, v___y_5660_);
lean_dec(v___y_5660_);
lean_dec_ref(v___y_5659_);
lean_dec(v___y_5658_);
lean_dec_ref(v___y_5657_);
lean_dec_ref(v_range_5652_);
return v_res_5662_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2(lean_object* v_tail_5663_, lean_object* v_val_5664_, lean_object* v___x_5665_, lean_object* v___x_5666_, uint8_t v_a_5667_, lean_object* v___x_5668_, lean_object* v_head_5669_, lean_object* v_as_5670_, lean_object* v_as_x27_5671_, lean_object* v_b_5672_, lean_object* v_a_5673_, lean_object* v___y_5674_, lean_object* v___y_5675_, lean_object* v___y_5676_, lean_object* v___y_5677_){
_start:
{
lean_object* v___x_5679_; 
v___x_5679_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg(v_tail_5663_, v_val_5664_, v___x_5665_, v___x_5666_, v_a_5667_, v___x_5668_, v_head_5669_, v_as_x27_5671_, v_b_5672_, v___y_5674_, v___y_5675_, v___y_5676_, v___y_5677_);
return v___x_5679_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___boxed(lean_object* v_tail_5680_, lean_object* v_val_5681_, lean_object* v___x_5682_, lean_object* v___x_5683_, lean_object* v_a_5684_, lean_object* v___x_5685_, lean_object* v_head_5686_, lean_object* v_as_5687_, lean_object* v_as_x27_5688_, lean_object* v_b_5689_, lean_object* v_a_5690_, lean_object* v___y_5691_, lean_object* v___y_5692_, lean_object* v___y_5693_, lean_object* v___y_5694_, lean_object* v___y_5695_){
_start:
{
uint8_t v_a_18712__boxed_5696_; lean_object* v_res_5697_; 
v_a_18712__boxed_5696_ = lean_unbox(v_a_5684_);
v_res_5697_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2(v_tail_5680_, v_val_5681_, v___x_5682_, v___x_5683_, v_a_18712__boxed_5696_, v___x_5685_, v_head_5686_, v_as_5687_, v_as_x27_5688_, v_b_5689_, v_a_5690_, v___y_5691_, v___y_5692_, v___y_5693_, v___y_5694_);
lean_dec(v___y_5694_);
lean_dec_ref(v___y_5693_);
lean_dec(v___y_5692_);
lean_dec_ref(v___y_5691_);
lean_dec(v_as_x27_5688_);
lean_dec(v_as_5687_);
return v_res_5697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCore(lean_object* v_declName_5698_, lean_object* v_a_5699_, lean_object* v_a_5700_, lean_object* v_a_5701_, lean_object* v_a_5702_){
_start:
{
lean_object* v___x_5704_; 
lean_inc(v_declName_5698_);
v___x_5704_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(v_declName_5698_, v_a_5699_, v_a_5700_, v_a_5701_, v_a_5702_);
if (lean_obj_tag(v___x_5704_) == 0)
{
lean_object* v_a_5705_; lean_object* v___x_5707_; uint8_t v_isShared_5708_; uint8_t v_isSharedCheck_5774_; 
v_a_5705_ = lean_ctor_get(v___x_5704_, 0);
v_isSharedCheck_5774_ = !lean_is_exclusive(v___x_5704_);
if (v_isSharedCheck_5774_ == 0)
{
v___x_5707_ = v___x_5704_;
v_isShared_5708_ = v_isSharedCheck_5774_;
goto v_resetjp_5706_;
}
else
{
lean_inc(v_a_5705_);
lean_dec(v___x_5704_);
v___x_5707_ = lean_box(0);
v_isShared_5708_ = v_isSharedCheck_5774_;
goto v_resetjp_5706_;
}
v_resetjp_5706_:
{
if (lean_obj_tag(v_a_5705_) == 5)
{
lean_object* v_val_5709_; lean_object* v___x_5710_; uint8_t v___x_5711_; lean_object* v___x_5712_; lean_object* v_a_5713_; lean_object* v___x_5715_; uint8_t v_isShared_5716_; uint8_t v_isSharedCheck_5769_; 
lean_del_object(v___x_5707_);
v_val_5709_ = lean_ctor_get(v_a_5705_, 0);
lean_inc_ref(v_val_5709_);
lean_dec_ref_known(v_a_5705_, 1);
lean_inc(v_declName_5698_);
v___x_5710_ = l_Lean_mkCasesOnName(v_declName_5698_);
v___x_5711_ = 1;
lean_inc(v___x_5710_);
v___x_5712_ = l_Lean_hasConst___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__1___redArg(v___x_5710_, v___x_5711_, v_a_5702_);
v_a_5713_ = lean_ctor_get(v___x_5712_, 0);
v_isSharedCheck_5769_ = !lean_is_exclusive(v___x_5712_);
if (v_isSharedCheck_5769_ == 0)
{
v___x_5715_ = v___x_5712_;
v_isShared_5716_ = v_isSharedCheck_5769_;
goto v_resetjp_5714_;
}
else
{
lean_inc(v_a_5713_);
lean_dec(v___x_5712_);
v___x_5715_ = lean_box(0);
v_isShared_5716_ = v_isSharedCheck_5769_;
goto v_resetjp_5714_;
}
v_resetjp_5714_:
{
uint8_t v___x_5717_; 
v___x_5717_ = lean_unbox(v_a_5713_);
lean_dec(v_a_5713_);
if (v___x_5717_ == 0)
{
lean_object* v___x_5718_; lean_object* v___x_5720_; 
lean_dec(v___x_5710_);
lean_dec_ref(v_val_5709_);
lean_dec(v_declName_5698_);
v___x_5718_ = lean_box(0);
if (v_isShared_5716_ == 0)
{
lean_ctor_set(v___x_5715_, 0, v___x_5718_);
v___x_5720_ = v___x_5715_;
goto v_reusejp_5719_;
}
else
{
lean_object* v_reuseFailAlloc_5721_; 
v_reuseFailAlloc_5721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5721_, 0, v___x_5718_);
v___x_5720_ = v_reuseFailAlloc_5721_;
goto v_reusejp_5719_;
}
v_reusejp_5719_:
{
return v___x_5720_;
}
}
else
{
lean_object* v___x_5722_; 
lean_del_object(v___x_5715_);
v___x_5722_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(v___x_5710_, v_a_5699_, v_a_5700_, v_a_5701_, v_a_5702_);
if (lean_obj_tag(v___x_5722_) == 0)
{
lean_object* v_toConstantVal_5723_; lean_object* v_a_5724_; lean_object* v___x_5726_; uint8_t v_isShared_5727_; uint8_t v_isSharedCheck_5760_; 
v_toConstantVal_5723_ = lean_ctor_get(v_val_5709_, 0);
lean_inc_ref(v_toConstantVal_5723_);
lean_dec_ref(v_val_5709_);
v_a_5724_ = lean_ctor_get(v___x_5722_, 0);
v_isSharedCheck_5760_ = !lean_is_exclusive(v___x_5722_);
if (v_isSharedCheck_5760_ == 0)
{
v___x_5726_ = v___x_5722_;
v_isShared_5727_ = v_isSharedCheck_5760_;
goto v_resetjp_5725_;
}
else
{
lean_inc(v_a_5724_);
lean_dec(v___x_5722_);
v___x_5726_ = lean_box(0);
v_isShared_5727_ = v_isSharedCheck_5760_;
goto v_resetjp_5725_;
}
v_resetjp_5725_:
{
lean_object* v_levelParams_5728_; lean_object* v_type_5729_; lean_object* v___x_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; uint8_t v___x_5733_; 
v_levelParams_5728_ = lean_ctor_get(v_toConstantVal_5723_, 1);
lean_inc(v_levelParams_5728_);
v_type_5729_ = lean_ctor_get(v_toConstantVal_5723_, 2);
lean_inc_ref(v_type_5729_);
lean_dec_ref(v_toConstantVal_5723_);
v___x_5730_ = l_List_lengthTR___redArg(v_levelParams_5728_);
lean_dec(v_levelParams_5728_);
v___x_5731_ = l_Lean_ConstantInfo_levelParams(v_a_5724_);
lean_dec(v_a_5724_);
v___x_5732_ = l_List_lengthTR___redArg(v___x_5731_);
lean_dec(v___x_5731_);
v___x_5733_ = lean_nat_dec_lt(v___x_5730_, v___x_5732_);
lean_dec(v___x_5732_);
lean_dec(v___x_5730_);
if (v___x_5733_ == 0)
{
lean_object* v___x_5734_; lean_object* v___x_5736_; 
lean_dec_ref(v_type_5729_);
lean_dec(v_declName_5698_);
v___x_5734_ = lean_box(0);
if (v_isShared_5727_ == 0)
{
lean_ctor_set(v___x_5726_, 0, v___x_5734_);
v___x_5736_ = v___x_5726_;
goto v_reusejp_5735_;
}
else
{
lean_object* v_reuseFailAlloc_5737_; 
v_reuseFailAlloc_5737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5737_, 0, v___x_5734_);
v___x_5736_ = v_reuseFailAlloc_5737_;
goto v_reusejp_5735_;
}
v_reusejp_5735_:
{
return v___x_5736_;
}
}
else
{
lean_object* v___x_5738_; 
lean_del_object(v___x_5726_);
v___x_5738_ = l_Lean_Meta_isPropFormerType(v_type_5729_, v_a_5699_, v_a_5700_, v_a_5701_, v_a_5702_);
if (lean_obj_tag(v___x_5738_) == 0)
{
lean_object* v_a_5739_; lean_object* v___x_5741_; uint8_t v_isShared_5742_; uint8_t v_isSharedCheck_5751_; 
v_a_5739_ = lean_ctor_get(v___x_5738_, 0);
v_isSharedCheck_5751_ = !lean_is_exclusive(v___x_5738_);
if (v_isSharedCheck_5751_ == 0)
{
v___x_5741_ = v___x_5738_;
v_isShared_5742_ = v_isSharedCheck_5751_;
goto v_resetjp_5740_;
}
else
{
lean_inc(v_a_5739_);
lean_dec(v___x_5738_);
v___x_5741_ = lean_box(0);
v_isShared_5742_ = v_isSharedCheck_5751_;
goto v_resetjp_5740_;
}
v_resetjp_5740_:
{
uint8_t v___x_5743_; 
v___x_5743_ = lean_unbox(v_a_5739_);
lean_dec(v_a_5739_);
if (v___x_5743_ == 0)
{
lean_object* v___x_5744_; 
lean_del_object(v___x_5741_);
lean_inc(v_declName_5698_);
v___x_5744_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType(v_declName_5698_, v_a_5699_, v_a_5700_, v_a_5701_, v_a_5702_);
if (lean_obj_tag(v___x_5744_) == 0)
{
lean_object* v___x_5745_; 
lean_dec_ref_known(v___x_5744_, 1);
lean_inc(v_declName_5698_);
v___x_5745_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp(v_declName_5698_, v_a_5699_, v_a_5700_, v_a_5701_, v_a_5702_);
if (lean_obj_tag(v___x_5745_) == 0)
{
lean_object* v___x_5746_; 
lean_dec_ref_known(v___x_5745_, 1);
v___x_5746_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors(v_declName_5698_, v_a_5699_, v_a_5700_, v_a_5701_, v_a_5702_);
return v___x_5746_;
}
else
{
lean_dec(v_declName_5698_);
return v___x_5745_;
}
}
else
{
lean_dec(v_declName_5698_);
return v___x_5744_;
}
}
else
{
lean_object* v___x_5747_; lean_object* v___x_5749_; 
lean_dec(v_declName_5698_);
v___x_5747_ = lean_box(0);
if (v_isShared_5742_ == 0)
{
lean_ctor_set(v___x_5741_, 0, v___x_5747_);
v___x_5749_ = v___x_5741_;
goto v_reusejp_5748_;
}
else
{
lean_object* v_reuseFailAlloc_5750_; 
v_reuseFailAlloc_5750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5750_, 0, v___x_5747_);
v___x_5749_ = v_reuseFailAlloc_5750_;
goto v_reusejp_5748_;
}
v_reusejp_5748_:
{
return v___x_5749_;
}
}
}
}
else
{
lean_object* v_a_5752_; lean_object* v___x_5754_; uint8_t v_isShared_5755_; uint8_t v_isSharedCheck_5759_; 
lean_dec(v_declName_5698_);
v_a_5752_ = lean_ctor_get(v___x_5738_, 0);
v_isSharedCheck_5759_ = !lean_is_exclusive(v___x_5738_);
if (v_isSharedCheck_5759_ == 0)
{
v___x_5754_ = v___x_5738_;
v_isShared_5755_ = v_isSharedCheck_5759_;
goto v_resetjp_5753_;
}
else
{
lean_inc(v_a_5752_);
lean_dec(v___x_5738_);
v___x_5754_ = lean_box(0);
v_isShared_5755_ = v_isSharedCheck_5759_;
goto v_resetjp_5753_;
}
v_resetjp_5753_:
{
lean_object* v___x_5757_; 
if (v_isShared_5755_ == 0)
{
v___x_5757_ = v___x_5754_;
goto v_reusejp_5756_;
}
else
{
lean_object* v_reuseFailAlloc_5758_; 
v_reuseFailAlloc_5758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5758_, 0, v_a_5752_);
v___x_5757_ = v_reuseFailAlloc_5758_;
goto v_reusejp_5756_;
}
v_reusejp_5756_:
{
return v___x_5757_;
}
}
}
}
}
}
else
{
lean_object* v_a_5761_; lean_object* v___x_5763_; uint8_t v_isShared_5764_; uint8_t v_isSharedCheck_5768_; 
lean_dec_ref(v_val_5709_);
lean_dec(v_declName_5698_);
v_a_5761_ = lean_ctor_get(v___x_5722_, 0);
v_isSharedCheck_5768_ = !lean_is_exclusive(v___x_5722_);
if (v_isSharedCheck_5768_ == 0)
{
v___x_5763_ = v___x_5722_;
v_isShared_5764_ = v_isSharedCheck_5768_;
goto v_resetjp_5762_;
}
else
{
lean_inc(v_a_5761_);
lean_dec(v___x_5722_);
v___x_5763_ = lean_box(0);
v_isShared_5764_ = v_isSharedCheck_5768_;
goto v_resetjp_5762_;
}
v_resetjp_5762_:
{
lean_object* v___x_5766_; 
if (v_isShared_5764_ == 0)
{
v___x_5766_ = v___x_5763_;
goto v_reusejp_5765_;
}
else
{
lean_object* v_reuseFailAlloc_5767_; 
v_reuseFailAlloc_5767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5767_, 0, v_a_5761_);
v___x_5766_ = v_reuseFailAlloc_5767_;
goto v_reusejp_5765_;
}
v_reusejp_5765_:
{
return v___x_5766_;
}
}
}
}
}
}
else
{
lean_object* v___x_5770_; lean_object* v___x_5772_; 
lean_dec(v_a_5705_);
lean_dec(v_declName_5698_);
v___x_5770_ = lean_box(0);
if (v_isShared_5708_ == 0)
{
lean_ctor_set(v___x_5707_, 0, v___x_5770_);
v___x_5772_ = v___x_5707_;
goto v_reusejp_5771_;
}
else
{
lean_object* v_reuseFailAlloc_5773_; 
v_reuseFailAlloc_5773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5773_, 0, v___x_5770_);
v___x_5772_ = v_reuseFailAlloc_5773_;
goto v_reusejp_5771_;
}
v_reusejp_5771_:
{
return v___x_5772_;
}
}
}
}
else
{
lean_object* v_a_5775_; lean_object* v___x_5777_; uint8_t v_isShared_5778_; uint8_t v_isSharedCheck_5782_; 
lean_dec(v_declName_5698_);
v_a_5775_ = lean_ctor_get(v___x_5704_, 0);
v_isSharedCheck_5782_ = !lean_is_exclusive(v___x_5704_);
if (v_isSharedCheck_5782_ == 0)
{
v___x_5777_ = v___x_5704_;
v_isShared_5778_ = v_isSharedCheck_5782_;
goto v_resetjp_5776_;
}
else
{
lean_inc(v_a_5775_);
lean_dec(v___x_5704_);
v___x_5777_ = lean_box(0);
v_isShared_5778_ = v_isSharedCheck_5782_;
goto v_resetjp_5776_;
}
v_resetjp_5776_:
{
lean_object* v___x_5780_; 
if (v_isShared_5778_ == 0)
{
v___x_5780_ = v___x_5777_;
goto v_reusejp_5779_;
}
else
{
lean_object* v_reuseFailAlloc_5781_; 
v_reuseFailAlloc_5781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5781_, 0, v_a_5775_);
v___x_5780_ = v_reuseFailAlloc_5781_;
goto v_reusejp_5779_;
}
v_reusejp_5779_:
{
return v___x_5780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCore___boxed(lean_object* v_declName_5783_, lean_object* v_a_5784_, lean_object* v_a_5785_, lean_object* v_a_5786_, lean_object* v_a_5787_, lean_object* v_a_5788_){
_start:
{
lean_object* v_res_5789_; 
v_res_5789_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCore(v_declName_5783_, v_a_5784_, v_a_5785_, v_a_5786_, v_a_5787_);
lean_dec(v_a_5787_);
lean_dec_ref(v_a_5786_);
lean_dec(v_a_5785_);
lean_dec_ref(v_a_5784_);
return v_res_5789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__0(lean_object* v_P_5793_, lean_object* v_x_5794_, lean_object* v___x_5795_, lean_object* v_enumName_5796_, lean_object* v_a_5797_, lean_object* v_levelParams_5798_, lean_object* v_val_5799_, lean_object* v___x_5800_, lean_object* v_y_5801_, lean_object* v___y_5802_, lean_object* v___y_5803_, lean_object* v___y_5804_, lean_object* v___y_5805_){
_start:
{
lean_object* v___x_5807_; lean_object* v___x_5808_; lean_object* v___x_5809_; lean_object* v___x_5810_; lean_object* v___x_5811_; uint8_t v___x_5812_; uint8_t v___x_5813_; uint8_t v___x_5814_; lean_object* v___x_5815_; 
v___x_5807_ = lean_unsigned_to_nat(3u);
v___x_5808_ = lean_mk_empty_array_with_capacity(v___x_5807_);
lean_inc_ref(v_P_5793_);
v___x_5809_ = lean_array_push(v___x_5808_, v_P_5793_);
lean_inc_ref(v_x_5794_);
v___x_5810_ = lean_array_push(v___x_5809_, v_x_5794_);
lean_inc_ref(v_y_5801_);
v___x_5811_ = lean_array_push(v___x_5810_, v_y_5801_);
v___x_5812_ = 0;
v___x_5813_ = 1;
v___x_5814_ = 1;
v___x_5815_ = l_Lean_Meta_mkForallFVars(v___x_5811_, v___x_5795_, v___x_5812_, v___x_5813_, v___x_5813_, v___x_5814_, v___y_5802_, v___y_5803_, v___y_5804_, v___y_5805_);
if (lean_obj_tag(v___x_5815_) == 0)
{
lean_object* v_a_5816_; lean_object* v_declValue_5818_; lean_object* v___y_5819_; lean_object* v___y_5820_; lean_object* v___y_5821_; lean_object* v___y_5822_; lean_object* v___x_5835_; lean_object* v___x_5836_; uint8_t v___x_5837_; 
v_a_5816_ = lean_ctor_get(v___x_5815_, 0);
lean_inc(v_a_5816_);
lean_dec_ref_known(v___x_5815_, 1);
v___x_5835_ = l_Lean_InductiveVal_numCtors(v_val_5799_);
v___x_5836_ = lean_unsigned_to_nat(1u);
v___x_5837_ = lean_nat_dec_eq(v___x_5835_, v___x_5836_);
lean_dec(v___x_5835_);
if (v___x_5837_ == 0)
{
lean_object* v___x_5838_; lean_object* v___x_5839_; lean_object* v___x_5840_; lean_object* v___x_5841_; lean_object* v___x_5842_; lean_object* v___x_5843_; lean_object* v___x_5844_; lean_object* v___x_5845_; lean_object* v___x_5846_; lean_object* v___x_5847_; 
lean_inc(v_enumName_5796_);
v___x_5838_ = l_Lean_mkCtorIdxName(v_enumName_5796_);
v___x_5839_ = l_Lean_mkConst(v___x_5838_, v___x_5800_);
v___x_5840_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__0___closed__1));
v___x_5841_ = lean_unsigned_to_nat(4u);
v___x_5842_ = lean_mk_empty_array_with_capacity(v___x_5841_);
v___x_5843_ = lean_array_push(v___x_5842_, v___x_5839_);
v___x_5844_ = lean_array_push(v___x_5843_, v_P_5793_);
v___x_5845_ = lean_array_push(v___x_5844_, v_x_5794_);
v___x_5846_ = lean_array_push(v___x_5845_, v_y_5801_);
v___x_5847_ = l_Lean_Meta_mkAppM(v___x_5840_, v___x_5846_, v___y_5802_, v___y_5803_, v___y_5804_, v___y_5805_);
if (lean_obj_tag(v___x_5847_) == 0)
{
lean_object* v_a_5848_; lean_object* v___x_5849_; 
v_a_5848_ = lean_ctor_get(v___x_5847_, 0);
lean_inc(v_a_5848_);
lean_dec_ref_known(v___x_5847_, 1);
v___x_5849_ = l_Lean_Meta_mkLambdaFVars(v___x_5811_, v_a_5848_, v___x_5812_, v___x_5813_, v___x_5812_, v___x_5813_, v___x_5814_, v___y_5802_, v___y_5803_, v___y_5804_, v___y_5805_);
lean_dec_ref(v___x_5811_);
if (lean_obj_tag(v___x_5849_) == 0)
{
lean_object* v_a_5850_; 
v_a_5850_ = lean_ctor_get(v___x_5849_, 0);
lean_inc(v_a_5850_);
lean_dec_ref_known(v___x_5849_, 1);
v_declValue_5818_ = v_a_5850_;
v___y_5819_ = v___y_5802_;
v___y_5820_ = v___y_5803_;
v___y_5821_ = v___y_5804_;
v___y_5822_ = v___y_5805_;
goto v___jp_5817_;
}
else
{
lean_object* v_a_5851_; lean_object* v___x_5853_; uint8_t v_isShared_5854_; uint8_t v_isSharedCheck_5858_; 
lean_dec(v_a_5816_);
lean_dec(v_levelParams_5798_);
lean_dec(v_a_5797_);
lean_dec(v_enumName_5796_);
v_a_5851_ = lean_ctor_get(v___x_5849_, 0);
v_isSharedCheck_5858_ = !lean_is_exclusive(v___x_5849_);
if (v_isSharedCheck_5858_ == 0)
{
v___x_5853_ = v___x_5849_;
v_isShared_5854_ = v_isSharedCheck_5858_;
goto v_resetjp_5852_;
}
else
{
lean_inc(v_a_5851_);
lean_dec(v___x_5849_);
v___x_5853_ = lean_box(0);
v_isShared_5854_ = v_isSharedCheck_5858_;
goto v_resetjp_5852_;
}
v_resetjp_5852_:
{
lean_object* v___x_5856_; 
if (v_isShared_5854_ == 0)
{
v___x_5856_ = v___x_5853_;
goto v_reusejp_5855_;
}
else
{
lean_object* v_reuseFailAlloc_5857_; 
v_reuseFailAlloc_5857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5857_, 0, v_a_5851_);
v___x_5856_ = v_reuseFailAlloc_5857_;
goto v_reusejp_5855_;
}
v_reusejp_5855_:
{
return v___x_5856_;
}
}
}
}
else
{
lean_object* v_a_5859_; lean_object* v___x_5861_; uint8_t v_isShared_5862_; uint8_t v_isSharedCheck_5866_; 
lean_dec(v_a_5816_);
lean_dec_ref(v___x_5811_);
lean_dec(v_levelParams_5798_);
lean_dec(v_a_5797_);
lean_dec(v_enumName_5796_);
v_a_5859_ = lean_ctor_get(v___x_5847_, 0);
v_isSharedCheck_5866_ = !lean_is_exclusive(v___x_5847_);
if (v_isSharedCheck_5866_ == 0)
{
v___x_5861_ = v___x_5847_;
v_isShared_5862_ = v_isSharedCheck_5866_;
goto v_resetjp_5860_;
}
else
{
lean_inc(v_a_5859_);
lean_dec(v___x_5847_);
v___x_5861_ = lean_box(0);
v_isShared_5862_ = v_isSharedCheck_5866_;
goto v_resetjp_5860_;
}
v_resetjp_5860_:
{
lean_object* v___x_5864_; 
if (v_isShared_5862_ == 0)
{
v___x_5864_ = v___x_5861_;
goto v_reusejp_5863_;
}
else
{
lean_object* v_reuseFailAlloc_5865_; 
v_reuseFailAlloc_5865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5865_, 0, v_a_5859_);
v___x_5864_ = v_reuseFailAlloc_5865_;
goto v_reusejp_5863_;
}
v_reusejp_5863_:
{
return v___x_5864_;
}
}
}
}
else
{
lean_object* v___x_5867_; 
lean_dec_ref(v_y_5801_);
lean_dec(v___x_5800_);
lean_dec_ref(v_x_5794_);
lean_inc_ref(v_P_5793_);
v___x_5867_ = l_Lean_mkArrow(v_P_5793_, v_P_5793_, v___y_5804_, v___y_5805_);
if (lean_obj_tag(v___x_5867_) == 0)
{
lean_object* v_a_5868_; lean_object* v___x_5869_; 
v_a_5868_ = lean_ctor_get(v___x_5867_, 0);
lean_inc(v_a_5868_);
lean_dec_ref_known(v___x_5867_, 1);
v___x_5869_ = l_Lean_Meta_mkLambdaFVars(v___x_5811_, v_a_5868_, v___x_5812_, v___x_5813_, v___x_5812_, v___x_5813_, v___x_5814_, v___y_5802_, v___y_5803_, v___y_5804_, v___y_5805_);
lean_dec_ref(v___x_5811_);
if (lean_obj_tag(v___x_5869_) == 0)
{
lean_object* v_a_5870_; 
v_a_5870_ = lean_ctor_get(v___x_5869_, 0);
lean_inc(v_a_5870_);
lean_dec_ref_known(v___x_5869_, 1);
v_declValue_5818_ = v_a_5870_;
v___y_5819_ = v___y_5802_;
v___y_5820_ = v___y_5803_;
v___y_5821_ = v___y_5804_;
v___y_5822_ = v___y_5805_;
goto v___jp_5817_;
}
else
{
lean_object* v_a_5871_; lean_object* v___x_5873_; uint8_t v_isShared_5874_; uint8_t v_isSharedCheck_5878_; 
lean_dec(v_a_5816_);
lean_dec(v_levelParams_5798_);
lean_dec(v_a_5797_);
lean_dec(v_enumName_5796_);
v_a_5871_ = lean_ctor_get(v___x_5869_, 0);
v_isSharedCheck_5878_ = !lean_is_exclusive(v___x_5869_);
if (v_isSharedCheck_5878_ == 0)
{
v___x_5873_ = v___x_5869_;
v_isShared_5874_ = v_isSharedCheck_5878_;
goto v_resetjp_5872_;
}
else
{
lean_inc(v_a_5871_);
lean_dec(v___x_5869_);
v___x_5873_ = lean_box(0);
v_isShared_5874_ = v_isSharedCheck_5878_;
goto v_resetjp_5872_;
}
v_resetjp_5872_:
{
lean_object* v___x_5876_; 
if (v_isShared_5874_ == 0)
{
v___x_5876_ = v___x_5873_;
goto v_reusejp_5875_;
}
else
{
lean_object* v_reuseFailAlloc_5877_; 
v_reuseFailAlloc_5877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5877_, 0, v_a_5871_);
v___x_5876_ = v_reuseFailAlloc_5877_;
goto v_reusejp_5875_;
}
v_reusejp_5875_:
{
return v___x_5876_;
}
}
}
}
else
{
lean_object* v_a_5879_; lean_object* v___x_5881_; uint8_t v_isShared_5882_; uint8_t v_isSharedCheck_5886_; 
lean_dec(v_a_5816_);
lean_dec_ref(v___x_5811_);
lean_dec(v_levelParams_5798_);
lean_dec(v_a_5797_);
lean_dec(v_enumName_5796_);
v_a_5879_ = lean_ctor_get(v___x_5867_, 0);
v_isSharedCheck_5886_ = !lean_is_exclusive(v___x_5867_);
if (v_isSharedCheck_5886_ == 0)
{
v___x_5881_ = v___x_5867_;
v_isShared_5882_ = v_isSharedCheck_5886_;
goto v_resetjp_5880_;
}
else
{
lean_inc(v_a_5879_);
lean_dec(v___x_5867_);
v___x_5881_ = lean_box(0);
v_isShared_5882_ = v_isSharedCheck_5886_;
goto v_resetjp_5880_;
}
v_resetjp_5880_:
{
lean_object* v___x_5884_; 
if (v_isShared_5882_ == 0)
{
v___x_5884_ = v___x_5881_;
goto v_reusejp_5883_;
}
else
{
lean_object* v_reuseFailAlloc_5885_; 
v_reuseFailAlloc_5885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5885_, 0, v_a_5879_);
v___x_5884_ = v_reuseFailAlloc_5885_;
goto v_reusejp_5883_;
}
v_reusejp_5883_:
{
return v___x_5884_;
}
}
}
}
v___jp_5817_:
{
lean_object* v___x_5823_; lean_object* v___x_5824_; lean_object* v___x_5825_; lean_object* v___x_5826_; lean_object* v___x_5827_; uint8_t v___x_5828_; lean_object* v___x_5829_; lean_object* v___x_5830_; lean_object* v___x_5831_; lean_object* v___x_5832_; lean_object* v___x_5833_; 
v___x_5823_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionTypeName___closed__0));
v___x_5824_ = l_Lean_Name_str___override(v_enumName_5796_, v___x_5823_);
v___x_5825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5825_, 0, v_a_5797_);
lean_ctor_set(v___x_5825_, 1, v_levelParams_5798_);
lean_inc_n(v___x_5824_, 2);
v___x_5826_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5826_, 0, v___x_5824_);
lean_ctor_set(v___x_5826_, 1, v___x_5825_);
lean_ctor_set(v___x_5826_, 2, v_a_5816_);
v___x_5827_ = lean_box(1);
v___x_5828_ = 1;
v___x_5829_ = lean_box(0);
v___x_5830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5830_, 0, v___x_5824_);
lean_ctor_set(v___x_5830_, 1, v___x_5829_);
v___x_5831_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_5831_, 0, v___x_5826_);
lean_ctor_set(v___x_5831_, 1, v_declValue_5818_);
lean_ctor_set(v___x_5831_, 2, v___x_5827_);
lean_ctor_set(v___x_5831_, 3, v___x_5830_);
lean_ctor_set_uint8(v___x_5831_, sizeof(void*)*4, v___x_5828_);
v___x_5832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5832_, 0, v___x_5831_);
v___x_5833_ = l_Lean_addDecl(v___x_5832_, v___x_5812_, v___y_5821_, v___y_5822_);
if (lean_obj_tag(v___x_5833_) == 0)
{
lean_object* v___x_5834_; 
lean_dec_ref_known(v___x_5833_, 1);
v___x_5834_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7(v___x_5824_, v___y_5819_, v___y_5820_, v___y_5821_, v___y_5822_);
return v___x_5834_;
}
else
{
lean_dec(v___x_5824_);
return v___x_5833_;
}
}
}
else
{
lean_object* v_a_5887_; lean_object* v___x_5889_; uint8_t v_isShared_5890_; uint8_t v_isSharedCheck_5894_; 
lean_dec_ref(v___x_5811_);
lean_dec_ref(v_y_5801_);
lean_dec(v___x_5800_);
lean_dec(v_levelParams_5798_);
lean_dec(v_a_5797_);
lean_dec(v_enumName_5796_);
lean_dec_ref(v_x_5794_);
lean_dec_ref(v_P_5793_);
v_a_5887_ = lean_ctor_get(v___x_5815_, 0);
v_isSharedCheck_5894_ = !lean_is_exclusive(v___x_5815_);
if (v_isSharedCheck_5894_ == 0)
{
v___x_5889_ = v___x_5815_;
v_isShared_5890_ = v_isSharedCheck_5894_;
goto v_resetjp_5888_;
}
else
{
lean_inc(v_a_5887_);
lean_dec(v___x_5815_);
v___x_5889_ = lean_box(0);
v_isShared_5890_ = v_isSharedCheck_5894_;
goto v_resetjp_5888_;
}
v_resetjp_5888_:
{
lean_object* v___x_5892_; 
if (v_isShared_5890_ == 0)
{
v___x_5892_ = v___x_5889_;
goto v_reusejp_5891_;
}
else
{
lean_object* v_reuseFailAlloc_5893_; 
v_reuseFailAlloc_5893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5893_, 0, v_a_5887_);
v___x_5892_ = v_reuseFailAlloc_5893_;
goto v_reusejp_5891_;
}
v_reusejp_5891_:
{
return v___x_5892_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__0___boxed(lean_object* v_P_5895_, lean_object* v_x_5896_, lean_object* v___x_5897_, lean_object* v_enumName_5898_, lean_object* v_a_5899_, lean_object* v_levelParams_5900_, lean_object* v_val_5901_, lean_object* v___x_5902_, lean_object* v_y_5903_, lean_object* v___y_5904_, lean_object* v___y_5905_, lean_object* v___y_5906_, lean_object* v___y_5907_, lean_object* v___y_5908_){
_start:
{
lean_object* v_res_5909_; 
v_res_5909_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__0(v_P_5895_, v_x_5896_, v___x_5897_, v_enumName_5898_, v_a_5899_, v_levelParams_5900_, v_val_5901_, v___x_5902_, v_y_5903_, v___y_5904_, v___y_5905_, v___y_5906_, v___y_5907_);
lean_dec(v___y_5907_);
lean_dec_ref(v___y_5906_);
lean_dec(v___y_5905_);
lean_dec_ref(v___y_5904_);
lean_dec_ref(v_val_5901_);
return v_res_5909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__1(lean_object* v_P_5913_, lean_object* v___x_5914_, lean_object* v_enumName_5915_, lean_object* v_a_5916_, lean_object* v_levelParams_5917_, lean_object* v_val_5918_, lean_object* v___x_5919_, lean_object* v___x_5920_, lean_object* v_x_5921_, lean_object* v___y_5922_, lean_object* v___y_5923_, lean_object* v___y_5924_, lean_object* v___y_5925_){
_start:
{
lean_object* v___f_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; 
v___f_5927_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__0___boxed), 14, 8);
lean_closure_set(v___f_5927_, 0, v_P_5913_);
lean_closure_set(v___f_5927_, 1, v_x_5921_);
lean_closure_set(v___f_5927_, 2, v___x_5914_);
lean_closure_set(v___f_5927_, 3, v_enumName_5915_);
lean_closure_set(v___f_5927_, 4, v_a_5916_);
lean_closure_set(v___f_5927_, 5, v_levelParams_5917_);
lean_closure_set(v___f_5927_, 6, v_val_5918_);
lean_closure_set(v___f_5927_, 7, v___x_5919_);
v___x_5928_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__1___closed__1));
v___x_5929_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_5928_, v___x_5920_, v___f_5927_, v___y_5922_, v___y_5923_, v___y_5924_, v___y_5925_);
return v___x_5929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__1___boxed(lean_object* v_P_5930_, lean_object* v___x_5931_, lean_object* v_enumName_5932_, lean_object* v_a_5933_, lean_object* v_levelParams_5934_, lean_object* v_val_5935_, lean_object* v___x_5936_, lean_object* v___x_5937_, lean_object* v_x_5938_, lean_object* v___y_5939_, lean_object* v___y_5940_, lean_object* v___y_5941_, lean_object* v___y_5942_, lean_object* v___y_5943_){
_start:
{
lean_object* v_res_5944_; 
v_res_5944_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__1(v_P_5930_, v___x_5931_, v_enumName_5932_, v_a_5933_, v_levelParams_5934_, v_val_5935_, v___x_5936_, v___x_5937_, v_x_5938_, v___y_5939_, v___y_5940_, v___y_5941_, v___y_5942_);
lean_dec(v___y_5942_);
lean_dec_ref(v___y_5941_);
lean_dec(v___y_5940_);
lean_dec_ref(v___y_5939_);
return v_res_5944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__2(lean_object* v___x_5948_, lean_object* v_enumName_5949_, lean_object* v_a_5950_, lean_object* v_levelParams_5951_, lean_object* v_val_5952_, lean_object* v___x_5953_, lean_object* v___x_5954_, lean_object* v_P_5955_, lean_object* v___y_5956_, lean_object* v___y_5957_, lean_object* v___y_5958_, lean_object* v___y_5959_){
_start:
{
lean_object* v___f_5961_; lean_object* v___x_5962_; lean_object* v___x_5963_; 
lean_inc_ref(v___x_5954_);
v___f_5961_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__1___boxed), 14, 8);
lean_closure_set(v___f_5961_, 0, v_P_5955_);
lean_closure_set(v___f_5961_, 1, v___x_5948_);
lean_closure_set(v___f_5961_, 2, v_enumName_5949_);
lean_closure_set(v___f_5961_, 3, v_a_5950_);
lean_closure_set(v___f_5961_, 4, v_levelParams_5951_);
lean_closure_set(v___f_5961_, 5, v_val_5952_);
lean_closure_set(v___f_5961_, 6, v___x_5953_);
lean_closure_set(v___f_5961_, 7, v___x_5954_);
v___x_5962_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__2___closed__1));
v___x_5963_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_5962_, v___x_5954_, v___f_5961_, v___y_5956_, v___y_5957_, v___y_5958_, v___y_5959_);
return v___x_5963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__2___boxed(lean_object* v___x_5964_, lean_object* v_enumName_5965_, lean_object* v_a_5966_, lean_object* v_levelParams_5967_, lean_object* v_val_5968_, lean_object* v___x_5969_, lean_object* v___x_5970_, lean_object* v_P_5971_, lean_object* v___y_5972_, lean_object* v___y_5973_, lean_object* v___y_5974_, lean_object* v___y_5975_, lean_object* v___y_5976_){
_start:
{
lean_object* v_res_5977_; 
v_res_5977_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__2(v___x_5964_, v_enumName_5965_, v_a_5966_, v_levelParams_5967_, v_val_5968_, v___x_5969_, v___x_5970_, v_P_5971_, v___y_5972_, v___y_5973_, v___y_5974_, v___y_5975_);
lean_dec(v___y_5975_);
lean_dec_ref(v___y_5974_);
lean_dec(v___y_5973_);
lean_dec_ref(v___y_5972_);
return v_res_5977_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___closed__3(void){
_start:
{
lean_object* v___x_5982_; lean_object* v___x_5983_; lean_object* v___x_5984_; lean_object* v___x_5985_; lean_object* v___x_5986_; lean_object* v___x_5987_; 
v___x_5982_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__6));
v___x_5983_ = lean_unsigned_to_nat(63u);
v___x_5984_ = lean_unsigned_to_nat(378u);
v___x_5985_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___closed__2));
v___x_5986_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__2));
v___x_5987_ = l_mkPanicMessageWithDecl(v___x_5986_, v___x_5985_, v___x_5984_, v___x_5983_, v___x_5982_);
return v___x_5987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType(lean_object* v_enumName_5988_, lean_object* v_a_5989_, lean_object* v_a_5990_, lean_object* v_a_5991_, lean_object* v_a_5992_){
_start:
{
lean_object* v___x_5994_; 
lean_inc(v_enumName_5988_);
v___x_5994_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(v_enumName_5988_, v_a_5989_, v_a_5990_, v_a_5991_, v_a_5992_);
if (lean_obj_tag(v___x_5994_) == 0)
{
lean_object* v_a_5995_; 
v_a_5995_ = lean_ctor_get(v___x_5994_, 0);
lean_inc(v_a_5995_);
lean_dec_ref_known(v___x_5994_, 1);
if (lean_obj_tag(v_a_5995_) == 5)
{
lean_object* v_val_5996_; lean_object* v___x_5997_; lean_object* v___x_5998_; 
v_val_5996_ = lean_ctor_get(v_a_5995_, 0);
lean_inc_ref(v_val_5996_);
lean_dec_ref_known(v_a_5995_, 1);
v___x_5997_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___closed__1));
v___x_5998_ = l_Lean_Core_mkFreshUserName(v___x_5997_, v_a_5991_, v_a_5992_);
if (lean_obj_tag(v___x_5998_) == 0)
{
lean_object* v_toConstantVal_5999_; lean_object* v_a_6000_; lean_object* v_levelParams_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___f_6007_; lean_object* v___x_6008_; lean_object* v___x_6009_; 
v_toConstantVal_5999_ = lean_ctor_get(v_val_5996_, 0);
v_a_6000_ = lean_ctor_get(v___x_5998_, 0);
lean_inc_n(v_a_6000_, 2);
lean_dec_ref_known(v___x_5998_, 1);
v_levelParams_6001_ = lean_ctor_get(v_toConstantVal_5999_, 1);
lean_inc_n(v_levelParams_6001_, 2);
v___x_6002_ = lean_box(0);
v___x_6003_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__2(v_levelParams_6001_, v___x_6002_);
lean_inc(v___x_6003_);
lean_inc(v_enumName_5988_);
v___x_6004_ = l_Lean_mkConst(v_enumName_5988_, v___x_6003_);
v___x_6005_ = l_Lean_mkLevelParam(v_a_6000_);
v___x_6006_ = l_Lean_mkSort(v___x_6005_);
lean_inc_ref(v___x_6006_);
v___f_6007_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__2___boxed), 13, 7);
lean_closure_set(v___f_6007_, 0, v___x_6006_);
lean_closure_set(v___f_6007_, 1, v_enumName_5988_);
lean_closure_set(v___f_6007_, 2, v_a_6000_);
lean_closure_set(v___f_6007_, 3, v_levelParams_6001_);
lean_closure_set(v___f_6007_, 4, v_val_5996_);
lean_closure_set(v___f_6007_, 5, v___x_6003_);
lean_closure_set(v___f_6007_, 6, v___x_6004_);
v___x_6008_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__1));
v___x_6009_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_6008_, v___x_6006_, v___f_6007_, v_a_5989_, v_a_5990_, v_a_5991_, v_a_5992_);
return v___x_6009_;
}
else
{
lean_object* v_a_6010_; lean_object* v___x_6012_; uint8_t v_isShared_6013_; uint8_t v_isSharedCheck_6017_; 
lean_dec_ref(v_val_5996_);
lean_dec(v_enumName_5988_);
v_a_6010_ = lean_ctor_get(v___x_5998_, 0);
v_isSharedCheck_6017_ = !lean_is_exclusive(v___x_5998_);
if (v_isSharedCheck_6017_ == 0)
{
v___x_6012_ = v___x_5998_;
v_isShared_6013_ = v_isSharedCheck_6017_;
goto v_resetjp_6011_;
}
else
{
lean_inc(v_a_6010_);
lean_dec(v___x_5998_);
v___x_6012_ = lean_box(0);
v_isShared_6013_ = v_isSharedCheck_6017_;
goto v_resetjp_6011_;
}
v_resetjp_6011_:
{
lean_object* v___x_6015_; 
if (v_isShared_6013_ == 0)
{
v___x_6015_ = v___x_6012_;
goto v_reusejp_6014_;
}
else
{
lean_object* v_reuseFailAlloc_6016_; 
v_reuseFailAlloc_6016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6016_, 0, v_a_6010_);
v___x_6015_ = v_reuseFailAlloc_6016_;
goto v_reusejp_6014_;
}
v_reusejp_6014_:
{
return v___x_6015_;
}
}
}
}
else
{
lean_object* v___x_6018_; lean_object* v___x_6019_; 
lean_dec(v_a_5995_);
lean_dec(v_enumName_5988_);
v___x_6018_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___closed__3, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___closed__3_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___closed__3);
v___x_6019_ = l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8(v___x_6018_, v_a_5989_, v_a_5990_, v_a_5991_, v_a_5992_);
return v___x_6019_;
}
}
else
{
lean_object* v_a_6020_; lean_object* v___x_6022_; uint8_t v_isShared_6023_; uint8_t v_isSharedCheck_6027_; 
lean_dec(v_enumName_5988_);
v_a_6020_ = lean_ctor_get(v___x_5994_, 0);
v_isSharedCheck_6027_ = !lean_is_exclusive(v___x_5994_);
if (v_isSharedCheck_6027_ == 0)
{
v___x_6022_ = v___x_5994_;
v_isShared_6023_ = v_isSharedCheck_6027_;
goto v_resetjp_6021_;
}
else
{
lean_inc(v_a_6020_);
lean_dec(v___x_5994_);
v___x_6022_ = lean_box(0);
v_isShared_6023_ = v_isSharedCheck_6027_;
goto v_resetjp_6021_;
}
v_resetjp_6021_:
{
lean_object* v___x_6025_; 
if (v_isShared_6023_ == 0)
{
v___x_6025_ = v___x_6022_;
goto v_reusejp_6024_;
}
else
{
lean_object* v_reuseFailAlloc_6026_; 
v_reuseFailAlloc_6026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6026_, 0, v_a_6020_);
v___x_6025_ = v_reuseFailAlloc_6026_;
goto v_reusejp_6024_;
}
v_reusejp_6024_:
{
return v___x_6025_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___boxed(lean_object* v_enumName_6028_, lean_object* v_a_6029_, lean_object* v_a_6030_, lean_object* v_a_6031_, lean_object* v_a_6032_, lean_object* v_a_6033_){
_start:
{
lean_object* v_res_6034_; 
v_res_6034_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType(v_enumName_6028_, v_a_6029_, v_a_6030_, v_a_6031_, v_a_6032_);
lean_dec(v_a_6032_);
lean_dec_ref(v_a_6031_);
lean_dec(v_a_6030_);
lean_dec_ref(v_a_6029_);
return v_res_6034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__0(uint8_t v___x_6035_, uint8_t v___x_6036_, uint8_t v___x_6037_, lean_object* v_p_6038_, lean_object* v___y_6039_, lean_object* v___y_6040_, lean_object* v___y_6041_, lean_object* v___y_6042_){
_start:
{
lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; 
v___x_6044_ = lean_unsigned_to_nat(1u);
v___x_6045_ = lean_mk_empty_array_with_capacity(v___x_6044_);
lean_inc_ref(v_p_6038_);
v___x_6046_ = lean_array_push(v___x_6045_, v_p_6038_);
v___x_6047_ = l_Lean_Meta_mkLambdaFVars(v___x_6046_, v_p_6038_, v___x_6035_, v___x_6036_, v___x_6035_, v___x_6036_, v___x_6037_, v___y_6039_, v___y_6040_, v___y_6041_, v___y_6042_);
lean_dec_ref(v___x_6046_);
return v___x_6047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__0___boxed(lean_object* v___x_6048_, lean_object* v___x_6049_, lean_object* v___x_6050_, lean_object* v_p_6051_, lean_object* v___y_6052_, lean_object* v___y_6053_, lean_object* v___y_6054_, lean_object* v___y_6055_, lean_object* v___y_6056_){
_start:
{
uint8_t v___x_4222__boxed_6057_; uint8_t v___x_4223__boxed_6058_; uint8_t v___x_4224__boxed_6059_; lean_object* v_res_6060_; 
v___x_4222__boxed_6057_ = lean_unbox(v___x_6048_);
v___x_4223__boxed_6058_ = lean_unbox(v___x_6049_);
v___x_4224__boxed_6059_ = lean_unbox(v___x_6050_);
v_res_6060_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__0(v___x_4222__boxed_6057_, v___x_4223__boxed_6058_, v___x_4224__boxed_6059_, v_p_6051_, v___y_6052_, v___y_6053_, v___y_6054_, v___y_6055_);
lean_dec(v___y_6055_);
lean_dec_ref(v___y_6054_);
lean_dec(v___y_6053_);
lean_dec_ref(v___y_6052_);
return v_res_6060_;
}
}
static lean_object* _init_l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__3(void){
_start:
{
lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; 
v___x_6068_ = lean_box(0);
v___x_6069_ = lean_unsigned_to_nat(6u);
v___x_6070_ = lean_mk_empty_array_with_capacity(v___x_6069_);
v___x_6071_ = lean_array_push(v___x_6070_, v___x_6068_);
return v___x_6071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1(lean_object* v_P_6075_, lean_object* v_x_6076_, lean_object* v_b_6077_, lean_object* v___x_6078_, uint8_t v___x_6079_, lean_object* v_enumName_6080_, lean_object* v_a_6081_, lean_object* v___x_6082_, lean_object* v_val_6083_, lean_object* v___x_6084_, lean_object* v_h_6085_, lean_object* v___y_6086_, lean_object* v___y_6087_, lean_object* v___y_6088_, lean_object* v___y_6089_){
_start:
{
lean_object* v___x_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; lean_object* v___x_6097_; uint8_t v___x_6098_; uint8_t v___x_6099_; lean_object* v___x_6100_; 
v___x_6091_ = lean_unsigned_to_nat(4u);
v___x_6092_ = lean_mk_empty_array_with_capacity(v___x_6091_);
lean_inc_ref_n(v_P_6075_, 2);
v___x_6093_ = lean_array_push(v___x_6092_, v_P_6075_);
lean_inc_ref_n(v_x_6076_, 2);
v___x_6094_ = lean_array_push(v___x_6093_, v_x_6076_);
lean_inc_ref_n(v_b_6077_, 2);
v___x_6095_ = lean_array_push(v___x_6094_, v_b_6077_);
lean_inc_ref(v_h_6085_);
v___x_6096_ = lean_array_push(v___x_6095_, v_h_6085_);
v___x_6097_ = l_Lean_mkApp3(v___x_6078_, v_P_6075_, v_x_6076_, v_b_6077_);
v___x_6098_ = 0;
v___x_6099_ = 1;
v___x_6100_ = l_Lean_Meta_mkForallFVars(v___x_6096_, v___x_6097_, v___x_6098_, v___x_6099_, v___x_6099_, v___x_6079_, v___y_6086_, v___y_6087_, v___y_6088_, v___y_6089_);
if (lean_obj_tag(v___x_6100_) == 0)
{
lean_object* v_a_6101_; lean_object* v_____do__lift_6103_; lean_object* v___y_6104_; lean_object* v___y_6105_; lean_object* v___y_6106_; lean_object* v___y_6107_; lean_object* v___x_6175_; lean_object* v___x_6176_; uint8_t v___x_6177_; 
v_a_6101_ = lean_ctor_get(v___x_6100_, 0);
lean_inc(v_a_6101_);
lean_dec_ref_known(v___x_6100_, 1);
v___x_6175_ = l_Lean_InductiveVal_numCtors(v_val_6083_);
v___x_6176_ = lean_unsigned_to_nat(1u);
v___x_6177_ = lean_nat_dec_eq(v___x_6175_, v___x_6176_);
lean_dec(v___x_6175_);
if (v___x_6177_ == 0)
{
lean_object* v___x_6178_; lean_object* v___x_6179_; lean_object* v___x_6180_; lean_object* v___x_6181_; lean_object* v___x_6182_; lean_object* v___x_6183_; lean_object* v___x_6184_; lean_object* v___x_6185_; lean_object* v___x_6186_; lean_object* v___x_6187_; lean_object* v___x_6188_; lean_object* v___x_6189_; lean_object* v___x_6190_; 
v___x_6178_ = ((lean_object*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__2));
v___x_6179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6179_, 0, v___x_6084_);
v___x_6180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6180_, 0, v_P_6075_);
v___x_6181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6181_, 0, v_x_6076_);
v___x_6182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6182_, 0, v_b_6077_);
v___x_6183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6183_, 0, v_h_6085_);
v___x_6184_ = lean_obj_once(&l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__3, &l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__3_once, _init_l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__3);
v___x_6185_ = lean_array_push(v___x_6184_, v___x_6179_);
v___x_6186_ = lean_array_push(v___x_6185_, v___x_6180_);
v___x_6187_ = lean_array_push(v___x_6186_, v___x_6181_);
v___x_6188_ = lean_array_push(v___x_6187_, v___x_6182_);
v___x_6189_ = lean_array_push(v___x_6188_, v___x_6183_);
v___x_6190_ = l_Lean_Meta_mkAppOptM(v___x_6178_, v___x_6189_, v___y_6086_, v___y_6087_, v___y_6088_, v___y_6089_);
if (lean_obj_tag(v___x_6190_) == 0)
{
lean_object* v_a_6191_; 
v_a_6191_ = lean_ctor_get(v___x_6190_, 0);
lean_inc(v_a_6191_);
lean_dec_ref_known(v___x_6190_, 1);
v_____do__lift_6103_ = v_a_6191_;
v___y_6104_ = v___y_6086_;
v___y_6105_ = v___y_6087_;
v___y_6106_ = v___y_6088_;
v___y_6107_ = v___y_6089_;
goto v___jp_6102_;
}
else
{
lean_object* v_a_6192_; lean_object* v___x_6194_; uint8_t v_isShared_6195_; uint8_t v_isSharedCheck_6199_; 
lean_dec(v_a_6101_);
lean_dec_ref(v___x_6096_);
lean_dec(v___x_6082_);
lean_dec(v_a_6081_);
lean_dec(v_enumName_6080_);
v_a_6192_ = lean_ctor_get(v___x_6190_, 0);
v_isSharedCheck_6199_ = !lean_is_exclusive(v___x_6190_);
if (v_isSharedCheck_6199_ == 0)
{
v___x_6194_ = v___x_6190_;
v_isShared_6195_ = v_isSharedCheck_6199_;
goto v_resetjp_6193_;
}
else
{
lean_inc(v_a_6192_);
lean_dec(v___x_6190_);
v___x_6194_ = lean_box(0);
v_isShared_6195_ = v_isSharedCheck_6199_;
goto v_resetjp_6193_;
}
v_resetjp_6193_:
{
lean_object* v___x_6197_; 
if (v_isShared_6195_ == 0)
{
v___x_6197_ = v___x_6194_;
goto v_reusejp_6196_;
}
else
{
lean_object* v_reuseFailAlloc_6198_; 
v_reuseFailAlloc_6198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6198_, 0, v_a_6192_);
v___x_6197_ = v_reuseFailAlloc_6198_;
goto v_reusejp_6196_;
}
v_reusejp_6196_:
{
return v___x_6197_;
}
}
}
}
else
{
lean_object* v___x_6200_; lean_object* v___x_6201_; lean_object* v___x_6202_; lean_object* v___f_6203_; lean_object* v___x_6204_; lean_object* v___x_6205_; 
lean_dec_ref(v_h_6085_);
lean_dec_ref(v___x_6084_);
lean_dec_ref(v_b_6077_);
lean_dec_ref(v_x_6076_);
v___x_6200_ = lean_box(v___x_6098_);
v___x_6201_ = lean_box(v___x_6099_);
v___x_6202_ = lean_box(v___x_6079_);
v___f_6203_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__0___boxed), 9, 3);
lean_closure_set(v___f_6203_, 0, v___x_6200_);
lean_closure_set(v___f_6203_, 1, v___x_6201_);
lean_closure_set(v___f_6203_, 2, v___x_6202_);
v___x_6204_ = ((lean_object*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__5));
v___x_6205_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_6204_, v_P_6075_, v___f_6203_, v___y_6086_, v___y_6087_, v___y_6088_, v___y_6089_);
if (lean_obj_tag(v___x_6205_) == 0)
{
lean_object* v_a_6206_; 
v_a_6206_ = lean_ctor_get(v___x_6205_, 0);
lean_inc(v_a_6206_);
lean_dec_ref_known(v___x_6205_, 1);
v_____do__lift_6103_ = v_a_6206_;
v___y_6104_ = v___y_6086_;
v___y_6105_ = v___y_6087_;
v___y_6106_ = v___y_6088_;
v___y_6107_ = v___y_6089_;
goto v___jp_6102_;
}
else
{
lean_object* v_a_6207_; lean_object* v___x_6209_; uint8_t v_isShared_6210_; uint8_t v_isSharedCheck_6214_; 
lean_dec(v_a_6101_);
lean_dec_ref(v___x_6096_);
lean_dec(v___x_6082_);
lean_dec(v_a_6081_);
lean_dec(v_enumName_6080_);
v_a_6207_ = lean_ctor_get(v___x_6205_, 0);
v_isSharedCheck_6214_ = !lean_is_exclusive(v___x_6205_);
if (v_isSharedCheck_6214_ == 0)
{
v___x_6209_ = v___x_6205_;
v_isShared_6210_ = v_isSharedCheck_6214_;
goto v_resetjp_6208_;
}
else
{
lean_inc(v_a_6207_);
lean_dec(v___x_6205_);
v___x_6209_ = lean_box(0);
v_isShared_6210_ = v_isSharedCheck_6214_;
goto v_resetjp_6208_;
}
v_resetjp_6208_:
{
lean_object* v___x_6212_; 
if (v_isShared_6210_ == 0)
{
v___x_6212_ = v___x_6209_;
goto v_reusejp_6211_;
}
else
{
lean_object* v_reuseFailAlloc_6213_; 
v_reuseFailAlloc_6213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6213_, 0, v_a_6207_);
v___x_6212_ = v_reuseFailAlloc_6213_;
goto v_reusejp_6211_;
}
v_reusejp_6211_:
{
return v___x_6212_;
}
}
}
}
v___jp_6102_:
{
lean_object* v___x_6108_; 
v___x_6108_ = l_Lean_Meta_mkLambdaFVars(v___x_6096_, v_____do__lift_6103_, v___x_6098_, v___x_6099_, v___x_6098_, v___x_6099_, v___x_6079_, v___y_6104_, v___y_6105_, v___y_6106_, v___y_6107_);
lean_dec_ref(v___x_6096_);
if (lean_obj_tag(v___x_6108_) == 0)
{
lean_object* v_a_6109_; lean_object* v___x_6110_; lean_object* v___x_6111_; lean_object* v___x_6112_; lean_object* v___x_6113_; lean_object* v___x_6114_; uint8_t v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6119_; lean_object* v___x_6120_; 
v_a_6109_ = lean_ctor_get(v___x_6108_, 0);
lean_inc(v_a_6109_);
lean_dec_ref_known(v___x_6108_, 1);
v___x_6110_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__0));
v___x_6111_ = l_Lean_Name_str___override(v_enumName_6080_, v___x_6110_);
v___x_6112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6112_, 0, v_a_6081_);
lean_ctor_set(v___x_6112_, 1, v___x_6082_);
lean_inc_n(v___x_6111_, 2);
v___x_6113_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6113_, 0, v___x_6111_);
lean_ctor_set(v___x_6113_, 1, v___x_6112_);
lean_ctor_set(v___x_6113_, 2, v_a_6101_);
v___x_6114_ = lean_box(1);
v___x_6115_ = 1;
v___x_6116_ = lean_box(0);
v___x_6117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6117_, 0, v___x_6111_);
lean_ctor_set(v___x_6117_, 1, v___x_6116_);
v___x_6118_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_6118_, 0, v___x_6113_);
lean_ctor_set(v___x_6118_, 1, v_a_6109_);
lean_ctor_set(v___x_6118_, 2, v___x_6114_);
lean_ctor_set(v___x_6118_, 3, v___x_6117_);
lean_ctor_set_uint8(v___x_6118_, sizeof(void*)*4, v___x_6115_);
v___x_6119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6119_, 0, v___x_6118_);
v___x_6120_ = l_Lean_addDecl(v___x_6119_, v___x_6098_, v___y_6106_, v___y_6107_);
if (lean_obj_tag(v___x_6120_) == 0)
{
lean_object* v___x_6121_; lean_object* v___x_6123_; uint8_t v_isShared_6124_; uint8_t v_isSharedCheck_6165_; 
lean_dec_ref_known(v___x_6120_, 1);
lean_inc(v___x_6111_);
v___x_6121_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7(v___x_6111_, v___y_6104_, v___y_6105_, v___y_6106_, v___y_6107_);
v_isSharedCheck_6165_ = !lean_is_exclusive(v___x_6121_);
if (v_isSharedCheck_6165_ == 0)
{
lean_object* v_unused_6166_; 
v_unused_6166_ = lean_ctor_get(v___x_6121_, 0);
lean_dec(v_unused_6166_);
v___x_6123_ = v___x_6121_;
v_isShared_6124_ = v_isSharedCheck_6165_;
goto v_resetjp_6122_;
}
else
{
lean_dec(v___x_6121_);
v___x_6123_ = lean_box(0);
v_isShared_6124_ = v_isSharedCheck_6165_;
goto v_resetjp_6122_;
}
v_resetjp_6122_:
{
lean_object* v___x_6125_; lean_object* v_env_6126_; lean_object* v_nextMacroScope_6127_; lean_object* v_ngen_6128_; lean_object* v_auxDeclNGen_6129_; lean_object* v_traceState_6130_; lean_object* v_messages_6131_; lean_object* v_infoState_6132_; lean_object* v_snapshotTasks_6133_; lean_object* v___x_6135_; uint8_t v_isShared_6136_; uint8_t v_isSharedCheck_6163_; 
v___x_6125_ = lean_st_ref_take(v___y_6107_);
v_env_6126_ = lean_ctor_get(v___x_6125_, 0);
v_nextMacroScope_6127_ = lean_ctor_get(v___x_6125_, 1);
v_ngen_6128_ = lean_ctor_get(v___x_6125_, 2);
v_auxDeclNGen_6129_ = lean_ctor_get(v___x_6125_, 3);
v_traceState_6130_ = lean_ctor_get(v___x_6125_, 4);
v_messages_6131_ = lean_ctor_get(v___x_6125_, 6);
v_infoState_6132_ = lean_ctor_get(v___x_6125_, 7);
v_snapshotTasks_6133_ = lean_ctor_get(v___x_6125_, 8);
v_isSharedCheck_6163_ = !lean_is_exclusive(v___x_6125_);
if (v_isSharedCheck_6163_ == 0)
{
lean_object* v_unused_6164_; 
v_unused_6164_ = lean_ctor_get(v___x_6125_, 5);
lean_dec(v_unused_6164_);
v___x_6135_ = v___x_6125_;
v_isShared_6136_ = v_isSharedCheck_6163_;
goto v_resetjp_6134_;
}
else
{
lean_inc(v_snapshotTasks_6133_);
lean_inc(v_infoState_6132_);
lean_inc(v_messages_6131_);
lean_inc(v_traceState_6130_);
lean_inc(v_auxDeclNGen_6129_);
lean_inc(v_ngen_6128_);
lean_inc(v_nextMacroScope_6127_);
lean_inc(v_env_6126_);
lean_dec(v___x_6125_);
v___x_6135_ = lean_box(0);
v_isShared_6136_ = v_isSharedCheck_6163_;
goto v_resetjp_6134_;
}
v_resetjp_6134_:
{
lean_object* v___x_6137_; lean_object* v___x_6138_; lean_object* v___x_6139_; lean_object* v___x_6141_; 
v___x_6137_ = ((lean_object*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__0));
v___x_6138_ = l_Lean_markNoConfusion(v_env_6126_, v___x_6111_, v___x_6137_);
v___x_6139_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2);
if (v_isShared_6136_ == 0)
{
lean_ctor_set(v___x_6135_, 5, v___x_6139_);
lean_ctor_set(v___x_6135_, 0, v___x_6138_);
v___x_6141_ = v___x_6135_;
goto v_reusejp_6140_;
}
else
{
lean_object* v_reuseFailAlloc_6162_; 
v_reuseFailAlloc_6162_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6162_, 0, v___x_6138_);
lean_ctor_set(v_reuseFailAlloc_6162_, 1, v_nextMacroScope_6127_);
lean_ctor_set(v_reuseFailAlloc_6162_, 2, v_ngen_6128_);
lean_ctor_set(v_reuseFailAlloc_6162_, 3, v_auxDeclNGen_6129_);
lean_ctor_set(v_reuseFailAlloc_6162_, 4, v_traceState_6130_);
lean_ctor_set(v_reuseFailAlloc_6162_, 5, v___x_6139_);
lean_ctor_set(v_reuseFailAlloc_6162_, 6, v_messages_6131_);
lean_ctor_set(v_reuseFailAlloc_6162_, 7, v_infoState_6132_);
lean_ctor_set(v_reuseFailAlloc_6162_, 8, v_snapshotTasks_6133_);
v___x_6141_ = v_reuseFailAlloc_6162_;
goto v_reusejp_6140_;
}
v_reusejp_6140_:
{
lean_object* v___x_6142_; lean_object* v___x_6143_; lean_object* v_mctx_6144_; lean_object* v_zetaDeltaFVarIds_6145_; lean_object* v_postponed_6146_; lean_object* v_diag_6147_; lean_object* v___x_6149_; uint8_t v_isShared_6150_; uint8_t v_isSharedCheck_6160_; 
v___x_6142_ = lean_st_ref_put(v___y_6107_, v___x_6141_);
v___x_6143_ = lean_st_ref_take(v___y_6105_);
v_mctx_6144_ = lean_ctor_get(v___x_6143_, 0);
v_zetaDeltaFVarIds_6145_ = lean_ctor_get(v___x_6143_, 2);
v_postponed_6146_ = lean_ctor_get(v___x_6143_, 3);
v_diag_6147_ = lean_ctor_get(v___x_6143_, 4);
v_isSharedCheck_6160_ = !lean_is_exclusive(v___x_6143_);
if (v_isSharedCheck_6160_ == 0)
{
lean_object* v_unused_6161_; 
v_unused_6161_ = lean_ctor_get(v___x_6143_, 1);
lean_dec(v_unused_6161_);
v___x_6149_ = v___x_6143_;
v_isShared_6150_ = v_isSharedCheck_6160_;
goto v_resetjp_6148_;
}
else
{
lean_inc(v_diag_6147_);
lean_inc(v_postponed_6146_);
lean_inc(v_zetaDeltaFVarIds_6145_);
lean_inc(v_mctx_6144_);
lean_dec(v___x_6143_);
v___x_6149_ = lean_box(0);
v_isShared_6150_ = v_isSharedCheck_6160_;
goto v_resetjp_6148_;
}
v_resetjp_6148_:
{
lean_object* v___x_6151_; lean_object* v___x_6153_; 
v___x_6151_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3);
if (v_isShared_6150_ == 0)
{
lean_ctor_set(v___x_6149_, 1, v___x_6151_);
v___x_6153_ = v___x_6149_;
goto v_reusejp_6152_;
}
else
{
lean_object* v_reuseFailAlloc_6159_; 
v_reuseFailAlloc_6159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6159_, 0, v_mctx_6144_);
lean_ctor_set(v_reuseFailAlloc_6159_, 1, v___x_6151_);
lean_ctor_set(v_reuseFailAlloc_6159_, 2, v_zetaDeltaFVarIds_6145_);
lean_ctor_set(v_reuseFailAlloc_6159_, 3, v_postponed_6146_);
lean_ctor_set(v_reuseFailAlloc_6159_, 4, v_diag_6147_);
v___x_6153_ = v_reuseFailAlloc_6159_;
goto v_reusejp_6152_;
}
v_reusejp_6152_:
{
lean_object* v___x_6154_; lean_object* v___x_6155_; lean_object* v___x_6157_; 
v___x_6154_ = lean_st_ref_put(v___y_6105_, v___x_6153_);
v___x_6155_ = lean_box(0);
if (v_isShared_6124_ == 0)
{
lean_ctor_set(v___x_6123_, 0, v___x_6155_);
v___x_6157_ = v___x_6123_;
goto v_reusejp_6156_;
}
else
{
lean_object* v_reuseFailAlloc_6158_; 
v_reuseFailAlloc_6158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6158_, 0, v___x_6155_);
v___x_6157_ = v_reuseFailAlloc_6158_;
goto v_reusejp_6156_;
}
v_reusejp_6156_:
{
return v___x_6157_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_6111_);
return v___x_6120_;
}
}
else
{
lean_object* v_a_6167_; lean_object* v___x_6169_; uint8_t v_isShared_6170_; uint8_t v_isSharedCheck_6174_; 
lean_dec(v_a_6101_);
lean_dec(v___x_6082_);
lean_dec(v_a_6081_);
lean_dec(v_enumName_6080_);
v_a_6167_ = lean_ctor_get(v___x_6108_, 0);
v_isSharedCheck_6174_ = !lean_is_exclusive(v___x_6108_);
if (v_isSharedCheck_6174_ == 0)
{
v___x_6169_ = v___x_6108_;
v_isShared_6170_ = v_isSharedCheck_6174_;
goto v_resetjp_6168_;
}
else
{
lean_inc(v_a_6167_);
lean_dec(v___x_6108_);
v___x_6169_ = lean_box(0);
v_isShared_6170_ = v_isSharedCheck_6174_;
goto v_resetjp_6168_;
}
v_resetjp_6168_:
{
lean_object* v___x_6172_; 
if (v_isShared_6170_ == 0)
{
v___x_6172_ = v___x_6169_;
goto v_reusejp_6171_;
}
else
{
lean_object* v_reuseFailAlloc_6173_; 
v_reuseFailAlloc_6173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6173_, 0, v_a_6167_);
v___x_6172_ = v_reuseFailAlloc_6173_;
goto v_reusejp_6171_;
}
v_reusejp_6171_:
{
return v___x_6172_;
}
}
}
}
}
else
{
lean_object* v_a_6215_; lean_object* v___x_6217_; uint8_t v_isShared_6218_; uint8_t v_isSharedCheck_6222_; 
lean_dec_ref(v___x_6096_);
lean_dec_ref(v_h_6085_);
lean_dec_ref(v___x_6084_);
lean_dec(v___x_6082_);
lean_dec(v_a_6081_);
lean_dec(v_enumName_6080_);
lean_dec_ref(v_b_6077_);
lean_dec_ref(v_x_6076_);
lean_dec_ref(v_P_6075_);
v_a_6215_ = lean_ctor_get(v___x_6100_, 0);
v_isSharedCheck_6222_ = !lean_is_exclusive(v___x_6100_);
if (v_isSharedCheck_6222_ == 0)
{
v___x_6217_ = v___x_6100_;
v_isShared_6218_ = v_isSharedCheck_6222_;
goto v_resetjp_6216_;
}
else
{
lean_inc(v_a_6215_);
lean_dec(v___x_6100_);
v___x_6217_ = lean_box(0);
v_isShared_6218_ = v_isSharedCheck_6222_;
goto v_resetjp_6216_;
}
v_resetjp_6216_:
{
lean_object* v___x_6220_; 
if (v_isShared_6218_ == 0)
{
v___x_6220_ = v___x_6217_;
goto v_reusejp_6219_;
}
else
{
lean_object* v_reuseFailAlloc_6221_; 
v_reuseFailAlloc_6221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6221_, 0, v_a_6215_);
v___x_6220_ = v_reuseFailAlloc_6221_;
goto v_reusejp_6219_;
}
v_reusejp_6219_:
{
return v___x_6220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___boxed(lean_object* v_P_6223_, lean_object* v_x_6224_, lean_object* v_b_6225_, lean_object* v___x_6226_, lean_object* v___x_6227_, lean_object* v_enumName_6228_, lean_object* v_a_6229_, lean_object* v___x_6230_, lean_object* v_val_6231_, lean_object* v___x_6232_, lean_object* v_h_6233_, lean_object* v___y_6234_, lean_object* v___y_6235_, lean_object* v___y_6236_, lean_object* v___y_6237_, lean_object* v___y_6238_){
_start:
{
uint8_t v___x_4297__boxed_6239_; lean_object* v_res_6240_; 
v___x_4297__boxed_6239_ = lean_unbox(v___x_6227_);
v_res_6240_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1(v_P_6223_, v_x_6224_, v_b_6225_, v___x_6226_, v___x_4297__boxed_6239_, v_enumName_6228_, v_a_6229_, v___x_6230_, v_val_6231_, v___x_6232_, v_h_6233_, v___y_6234_, v___y_6235_, v___y_6236_, v___y_6237_);
lean_dec(v___y_6237_);
lean_dec_ref(v___y_6236_);
lean_dec(v___y_6235_);
lean_dec_ref(v___y_6234_);
lean_dec_ref(v_val_6231_);
return v_res_6240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__2(lean_object* v_x_6241_, lean_object* v_P_6242_, lean_object* v___x_6243_, uint8_t v___x_6244_, lean_object* v_enumName_6245_, lean_object* v_a_6246_, lean_object* v___x_6247_, lean_object* v_val_6248_, lean_object* v___x_6249_, lean_object* v_b_6250_, lean_object* v___y_6251_, lean_object* v___y_6252_, lean_object* v___y_6253_, lean_object* v___y_6254_){
_start:
{
lean_object* v___x_6256_; 
lean_inc_ref(v_b_6250_);
lean_inc_ref(v_x_6241_);
v___x_6256_ = l_Lean_Meta_mkEq(v_x_6241_, v_b_6250_, v___y_6251_, v___y_6252_, v___y_6253_, v___y_6254_);
if (lean_obj_tag(v___x_6256_) == 0)
{
lean_object* v_a_6257_; lean_object* v___x_6258_; lean_object* v___f_6259_; lean_object* v___x_6260_; lean_object* v___x_6261_; 
v_a_6257_ = lean_ctor_get(v___x_6256_, 0);
lean_inc(v_a_6257_);
lean_dec_ref_known(v___x_6256_, 1);
v___x_6258_ = lean_box(v___x_6244_);
v___f_6259_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___boxed), 16, 10);
lean_closure_set(v___f_6259_, 0, v_P_6242_);
lean_closure_set(v___f_6259_, 1, v_x_6241_);
lean_closure_set(v___f_6259_, 2, v_b_6250_);
lean_closure_set(v___f_6259_, 3, v___x_6243_);
lean_closure_set(v___f_6259_, 4, v___x_6258_);
lean_closure_set(v___f_6259_, 5, v_enumName_6245_);
lean_closure_set(v___f_6259_, 6, v_a_6246_);
lean_closure_set(v___f_6259_, 7, v___x_6247_);
lean_closure_set(v___f_6259_, 8, v_val_6248_);
lean_closure_set(v___f_6259_, 9, v___x_6249_);
v___x_6260_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__13));
v___x_6261_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_6260_, v_a_6257_, v___f_6259_, v___y_6251_, v___y_6252_, v___y_6253_, v___y_6254_);
return v___x_6261_;
}
else
{
lean_object* v_a_6262_; lean_object* v___x_6264_; uint8_t v_isShared_6265_; uint8_t v_isSharedCheck_6269_; 
lean_dec_ref(v_b_6250_);
lean_dec_ref(v___x_6249_);
lean_dec_ref(v_val_6248_);
lean_dec(v___x_6247_);
lean_dec(v_a_6246_);
lean_dec(v_enumName_6245_);
lean_dec_ref(v___x_6243_);
lean_dec_ref(v_P_6242_);
lean_dec_ref(v_x_6241_);
v_a_6262_ = lean_ctor_get(v___x_6256_, 0);
v_isSharedCheck_6269_ = !lean_is_exclusive(v___x_6256_);
if (v_isSharedCheck_6269_ == 0)
{
v___x_6264_ = v___x_6256_;
v_isShared_6265_ = v_isSharedCheck_6269_;
goto v_resetjp_6263_;
}
else
{
lean_inc(v_a_6262_);
lean_dec(v___x_6256_);
v___x_6264_ = lean_box(0);
v_isShared_6265_ = v_isSharedCheck_6269_;
goto v_resetjp_6263_;
}
v_resetjp_6263_:
{
lean_object* v___x_6267_; 
if (v_isShared_6265_ == 0)
{
v___x_6267_ = v___x_6264_;
goto v_reusejp_6266_;
}
else
{
lean_object* v_reuseFailAlloc_6268_; 
v_reuseFailAlloc_6268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6268_, 0, v_a_6262_);
v___x_6267_ = v_reuseFailAlloc_6268_;
goto v_reusejp_6266_;
}
v_reusejp_6266_:
{
return v___x_6267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__2___boxed(lean_object* v_x_6270_, lean_object* v_P_6271_, lean_object* v___x_6272_, lean_object* v___x_6273_, lean_object* v_enumName_6274_, lean_object* v_a_6275_, lean_object* v___x_6276_, lean_object* v_val_6277_, lean_object* v___x_6278_, lean_object* v_b_6279_, lean_object* v___y_6280_, lean_object* v___y_6281_, lean_object* v___y_6282_, lean_object* v___y_6283_, lean_object* v___y_6284_){
_start:
{
uint8_t v___x_4591__boxed_6285_; lean_object* v_res_6286_; 
v___x_4591__boxed_6285_ = lean_unbox(v___x_6273_);
v_res_6286_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__2(v_x_6270_, v_P_6271_, v___x_6272_, v___x_4591__boxed_6285_, v_enumName_6274_, v_a_6275_, v___x_6276_, v_val_6277_, v___x_6278_, v_b_6279_, v___y_6280_, v___y_6281_, v___y_6282_, v___y_6283_);
lean_dec(v___y_6283_);
lean_dec_ref(v___y_6282_);
lean_dec(v___y_6281_);
lean_dec_ref(v___y_6280_);
return v_res_6286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0(lean_object* v_P_6287_, lean_object* v_x_6288_, lean_object* v___x_6289_, lean_object* v_enumName_6290_, lean_object* v_a_6291_, lean_object* v___x_6292_, lean_object* v_val_6293_, lean_object* v___x_6294_, lean_object* v_name_6295_, uint8_t v_bi_6296_, lean_object* v_type_6297_, uint8_t v_kind_6298_, lean_object* v___y_6299_, lean_object* v___y_6300_, lean_object* v___y_6301_, lean_object* v___y_6302_){
_start:
{
uint8_t v___x_6304_; lean_object* v___x_6305_; lean_object* v___f_6306_; lean_object* v___x_6307_; 
v___x_6304_ = 1;
v___x_6305_ = lean_box(v___x_6304_);
v___f_6306_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__2___boxed), 15, 9);
lean_closure_set(v___f_6306_, 0, v_x_6288_);
lean_closure_set(v___f_6306_, 1, v_P_6287_);
lean_closure_set(v___f_6306_, 2, v___x_6289_);
lean_closure_set(v___f_6306_, 3, v___x_6305_);
lean_closure_set(v___f_6306_, 4, v_enumName_6290_);
lean_closure_set(v___f_6306_, 5, v_a_6291_);
lean_closure_set(v___f_6306_, 6, v___x_6292_);
lean_closure_set(v___f_6306_, 7, v_val_6293_);
lean_closure_set(v___f_6306_, 8, v___x_6294_);
v___x_6307_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_6295_, v_bi_6296_, v_type_6297_, v___f_6306_, v_kind_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_);
if (lean_obj_tag(v___x_6307_) == 0)
{
lean_object* v_a_6308_; lean_object* v___x_6310_; uint8_t v_isShared_6311_; uint8_t v_isSharedCheck_6315_; 
v_a_6308_ = lean_ctor_get(v___x_6307_, 0);
v_isSharedCheck_6315_ = !lean_is_exclusive(v___x_6307_);
if (v_isSharedCheck_6315_ == 0)
{
v___x_6310_ = v___x_6307_;
v_isShared_6311_ = v_isSharedCheck_6315_;
goto v_resetjp_6309_;
}
else
{
lean_inc(v_a_6308_);
lean_dec(v___x_6307_);
v___x_6310_ = lean_box(0);
v_isShared_6311_ = v_isSharedCheck_6315_;
goto v_resetjp_6309_;
}
v_resetjp_6309_:
{
lean_object* v___x_6313_; 
if (v_isShared_6311_ == 0)
{
v___x_6313_ = v___x_6310_;
goto v_reusejp_6312_;
}
else
{
lean_object* v_reuseFailAlloc_6314_; 
v_reuseFailAlloc_6314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6314_, 0, v_a_6308_);
v___x_6313_ = v_reuseFailAlloc_6314_;
goto v_reusejp_6312_;
}
v_reusejp_6312_:
{
return v___x_6313_;
}
}
}
else
{
lean_object* v_a_6316_; lean_object* v___x_6318_; uint8_t v_isShared_6319_; uint8_t v_isSharedCheck_6323_; 
v_a_6316_ = lean_ctor_get(v___x_6307_, 0);
v_isSharedCheck_6323_ = !lean_is_exclusive(v___x_6307_);
if (v_isSharedCheck_6323_ == 0)
{
v___x_6318_ = v___x_6307_;
v_isShared_6319_ = v_isSharedCheck_6323_;
goto v_resetjp_6317_;
}
else
{
lean_inc(v_a_6316_);
lean_dec(v___x_6307_);
v___x_6318_ = lean_box(0);
v_isShared_6319_ = v_isSharedCheck_6323_;
goto v_resetjp_6317_;
}
v_resetjp_6317_:
{
lean_object* v___x_6321_; 
if (v_isShared_6319_ == 0)
{
v___x_6321_ = v___x_6318_;
goto v_reusejp_6320_;
}
else
{
lean_object* v_reuseFailAlloc_6322_; 
v_reuseFailAlloc_6322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6322_, 0, v_a_6316_);
v___x_6321_ = v_reuseFailAlloc_6322_;
goto v_reusejp_6320_;
}
v_reusejp_6320_:
{
return v___x_6321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___boxed(lean_object** _args){
lean_object* v_P_6324_ = _args[0];
lean_object* v_x_6325_ = _args[1];
lean_object* v___x_6326_ = _args[2];
lean_object* v_enumName_6327_ = _args[3];
lean_object* v_a_6328_ = _args[4];
lean_object* v___x_6329_ = _args[5];
lean_object* v_val_6330_ = _args[6];
lean_object* v___x_6331_ = _args[7];
lean_object* v_name_6332_ = _args[8];
lean_object* v_bi_6333_ = _args[9];
lean_object* v_type_6334_ = _args[10];
lean_object* v_kind_6335_ = _args[11];
lean_object* v___y_6336_ = _args[12];
lean_object* v___y_6337_ = _args[13];
lean_object* v___y_6338_ = _args[14];
lean_object* v___y_6339_ = _args[15];
lean_object* v___y_6340_ = _args[16];
_start:
{
uint8_t v_bi_boxed_6341_; uint8_t v_kind_boxed_6342_; lean_object* v_res_6343_; 
v_bi_boxed_6341_ = lean_unbox(v_bi_6333_);
v_kind_boxed_6342_ = lean_unbox(v_kind_6335_);
v_res_6343_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0(v_P_6324_, v_x_6325_, v___x_6326_, v_enumName_6327_, v_a_6328_, v___x_6329_, v_val_6330_, v___x_6331_, v_name_6332_, v_bi_boxed_6341_, v_type_6334_, v_kind_boxed_6342_, v___y_6336_, v___y_6337_, v___y_6338_, v___y_6339_);
lean_dec(v___y_6339_);
lean_dec_ref(v___y_6338_);
lean_dec(v___y_6337_);
lean_dec_ref(v___y_6336_);
return v_res_6343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__1___lam__0(lean_object* v_P_6344_, lean_object* v___x_6345_, lean_object* v_enumName_6346_, lean_object* v_a_6347_, lean_object* v___x_6348_, lean_object* v_val_6349_, lean_object* v___x_6350_, uint8_t v___x_6351_, lean_object* v___x_6352_, lean_object* v_b_6353_, lean_object* v___y_6354_, lean_object* v___y_6355_, lean_object* v___y_6356_, lean_object* v___y_6357_){
_start:
{
lean_object* v___x_6359_; uint8_t v___x_6360_; lean_object* v___x_6361_; 
v___x_6359_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__1___closed__1));
v___x_6360_ = 0;
v___x_6361_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0(v_P_6344_, v_b_6353_, v___x_6345_, v_enumName_6346_, v_a_6347_, v___x_6348_, v_val_6349_, v___x_6350_, v___x_6359_, v___x_6351_, v___x_6352_, v___x_6360_, v___y_6354_, v___y_6355_, v___y_6356_, v___y_6357_);
return v___x_6361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__1___lam__0___boxed(lean_object* v_P_6362_, lean_object* v___x_6363_, lean_object* v_enumName_6364_, lean_object* v_a_6365_, lean_object* v___x_6366_, lean_object* v_val_6367_, lean_object* v___x_6368_, lean_object* v___x_6369_, lean_object* v___x_6370_, lean_object* v_b_6371_, lean_object* v___y_6372_, lean_object* v___y_6373_, lean_object* v___y_6374_, lean_object* v___y_6375_, lean_object* v___y_6376_){
_start:
{
uint8_t v___x_4730__boxed_6377_; lean_object* v_res_6378_; 
v___x_4730__boxed_6377_ = lean_unbox(v___x_6369_);
v_res_6378_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__1___lam__0(v_P_6362_, v___x_6363_, v_enumName_6364_, v_a_6365_, v___x_6366_, v_val_6367_, v___x_6368_, v___x_4730__boxed_6377_, v___x_6370_, v_b_6371_, v___y_6372_, v___y_6373_, v___y_6374_, v___y_6375_);
lean_dec(v___y_6375_);
lean_dec_ref(v___y_6374_);
lean_dec(v___y_6373_);
lean_dec_ref(v___y_6372_);
return v_res_6378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__1(lean_object* v_P_6379_, lean_object* v___x_6380_, lean_object* v_enumName_6381_, lean_object* v_a_6382_, lean_object* v___x_6383_, lean_object* v_val_6384_, lean_object* v___x_6385_, lean_object* v___x_6386_, lean_object* v_name_6387_, uint8_t v_bi_6388_, lean_object* v_type_6389_, uint8_t v_kind_6390_, lean_object* v___y_6391_, lean_object* v___y_6392_, lean_object* v___y_6393_, lean_object* v___y_6394_){
_start:
{
uint8_t v___x_6396_; lean_object* v___x_6397_; lean_object* v___f_6398_; lean_object* v___x_6399_; 
v___x_6396_ = 1;
v___x_6397_ = lean_box(v___x_6396_);
v___f_6398_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__1___lam__0___boxed), 15, 9);
lean_closure_set(v___f_6398_, 0, v_P_6379_);
lean_closure_set(v___f_6398_, 1, v___x_6380_);
lean_closure_set(v___f_6398_, 2, v_enumName_6381_);
lean_closure_set(v___f_6398_, 3, v_a_6382_);
lean_closure_set(v___f_6398_, 4, v___x_6383_);
lean_closure_set(v___f_6398_, 5, v_val_6384_);
lean_closure_set(v___f_6398_, 6, v___x_6385_);
lean_closure_set(v___f_6398_, 7, v___x_6397_);
lean_closure_set(v___f_6398_, 8, v___x_6386_);
v___x_6399_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_6387_, v_bi_6388_, v_type_6389_, v___f_6398_, v_kind_6390_, v___y_6391_, v___y_6392_, v___y_6393_, v___y_6394_);
if (lean_obj_tag(v___x_6399_) == 0)
{
lean_object* v_a_6400_; lean_object* v___x_6402_; uint8_t v_isShared_6403_; uint8_t v_isSharedCheck_6407_; 
v_a_6400_ = lean_ctor_get(v___x_6399_, 0);
v_isSharedCheck_6407_ = !lean_is_exclusive(v___x_6399_);
if (v_isSharedCheck_6407_ == 0)
{
v___x_6402_ = v___x_6399_;
v_isShared_6403_ = v_isSharedCheck_6407_;
goto v_resetjp_6401_;
}
else
{
lean_inc(v_a_6400_);
lean_dec(v___x_6399_);
v___x_6402_ = lean_box(0);
v_isShared_6403_ = v_isSharedCheck_6407_;
goto v_resetjp_6401_;
}
v_resetjp_6401_:
{
lean_object* v___x_6405_; 
if (v_isShared_6403_ == 0)
{
v___x_6405_ = v___x_6402_;
goto v_reusejp_6404_;
}
else
{
lean_object* v_reuseFailAlloc_6406_; 
v_reuseFailAlloc_6406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6406_, 0, v_a_6400_);
v___x_6405_ = v_reuseFailAlloc_6406_;
goto v_reusejp_6404_;
}
v_reusejp_6404_:
{
return v___x_6405_;
}
}
}
else
{
lean_object* v_a_6408_; lean_object* v___x_6410_; uint8_t v_isShared_6411_; uint8_t v_isSharedCheck_6415_; 
v_a_6408_ = lean_ctor_get(v___x_6399_, 0);
v_isSharedCheck_6415_ = !lean_is_exclusive(v___x_6399_);
if (v_isSharedCheck_6415_ == 0)
{
v___x_6410_ = v___x_6399_;
v_isShared_6411_ = v_isSharedCheck_6415_;
goto v_resetjp_6409_;
}
else
{
lean_inc(v_a_6408_);
lean_dec(v___x_6399_);
v___x_6410_ = lean_box(0);
v_isShared_6411_ = v_isSharedCheck_6415_;
goto v_resetjp_6409_;
}
v_resetjp_6409_:
{
lean_object* v___x_6413_; 
if (v_isShared_6411_ == 0)
{
v___x_6413_ = v___x_6410_;
goto v_reusejp_6412_;
}
else
{
lean_object* v_reuseFailAlloc_6414_; 
v_reuseFailAlloc_6414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6414_, 0, v_a_6408_);
v___x_6413_ = v_reuseFailAlloc_6414_;
goto v_reusejp_6412_;
}
v_reusejp_6412_:
{
return v___x_6413_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__1___boxed(lean_object** _args){
lean_object* v_P_6416_ = _args[0];
lean_object* v___x_6417_ = _args[1];
lean_object* v_enumName_6418_ = _args[2];
lean_object* v_a_6419_ = _args[3];
lean_object* v___x_6420_ = _args[4];
lean_object* v_val_6421_ = _args[5];
lean_object* v___x_6422_ = _args[6];
lean_object* v___x_6423_ = _args[7];
lean_object* v_name_6424_ = _args[8];
lean_object* v_bi_6425_ = _args[9];
lean_object* v_type_6426_ = _args[10];
lean_object* v_kind_6427_ = _args[11];
lean_object* v___y_6428_ = _args[12];
lean_object* v___y_6429_ = _args[13];
lean_object* v___y_6430_ = _args[14];
lean_object* v___y_6431_ = _args[15];
lean_object* v___y_6432_ = _args[16];
_start:
{
uint8_t v_bi_boxed_6433_; uint8_t v_kind_boxed_6434_; lean_object* v_res_6435_; 
v_bi_boxed_6433_ = lean_unbox(v_bi_6425_);
v_kind_boxed_6434_ = lean_unbox(v_kind_6427_);
v_res_6435_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__1(v_P_6416_, v___x_6417_, v_enumName_6418_, v_a_6419_, v___x_6420_, v_val_6421_, v___x_6422_, v___x_6423_, v_name_6424_, v_bi_boxed_6433_, v_type_6426_, v_kind_boxed_6434_, v___y_6428_, v___y_6429_, v___y_6430_, v___y_6431_);
lean_dec(v___y_6431_);
lean_dec_ref(v___y_6430_);
lean_dec(v___y_6429_);
lean_dec_ref(v___y_6428_);
return v_res_6435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__2___lam__0(lean_object* v___x_6436_, lean_object* v_enumName_6437_, lean_object* v_a_6438_, lean_object* v___x_6439_, lean_object* v_val_6440_, lean_object* v___x_6441_, lean_object* v___x_6442_, uint8_t v___x_6443_, lean_object* v_b_6444_, lean_object* v___y_6445_, lean_object* v___y_6446_, lean_object* v___y_6447_, lean_object* v___y_6448_){
_start:
{
lean_object* v___x_6450_; uint8_t v___x_6451_; lean_object* v___x_6452_; 
v___x_6450_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__2___closed__1));
v___x_6451_ = 0;
lean_inc_ref(v___x_6442_);
v___x_6452_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__1(v_b_6444_, v___x_6436_, v_enumName_6437_, v_a_6438_, v___x_6439_, v_val_6440_, v___x_6441_, v___x_6442_, v___x_6450_, v___x_6443_, v___x_6442_, v___x_6451_, v___y_6445_, v___y_6446_, v___y_6447_, v___y_6448_);
return v___x_6452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__2___lam__0___boxed(lean_object* v___x_6453_, lean_object* v_enumName_6454_, lean_object* v_a_6455_, lean_object* v___x_6456_, lean_object* v_val_6457_, lean_object* v___x_6458_, lean_object* v___x_6459_, lean_object* v___x_6460_, lean_object* v_b_6461_, lean_object* v___y_6462_, lean_object* v___y_6463_, lean_object* v___y_6464_, lean_object* v___y_6465_, lean_object* v___y_6466_){
_start:
{
uint8_t v___x_4850__boxed_6467_; lean_object* v_res_6468_; 
v___x_4850__boxed_6467_ = lean_unbox(v___x_6460_);
v_res_6468_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__2___lam__0(v___x_6453_, v_enumName_6454_, v_a_6455_, v___x_6456_, v_val_6457_, v___x_6458_, v___x_6459_, v___x_4850__boxed_6467_, v_b_6461_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_);
lean_dec(v___y_6465_);
lean_dec_ref(v___y_6464_);
lean_dec(v___y_6463_);
lean_dec_ref(v___y_6462_);
return v_res_6468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__2(lean_object* v___x_6469_, lean_object* v_enumName_6470_, lean_object* v_a_6471_, lean_object* v___x_6472_, lean_object* v_val_6473_, lean_object* v___x_6474_, lean_object* v___x_6475_, lean_object* v_name_6476_, uint8_t v_bi_6477_, lean_object* v_type_6478_, uint8_t v_kind_6479_, lean_object* v___y_6480_, lean_object* v___y_6481_, lean_object* v___y_6482_, lean_object* v___y_6483_){
_start:
{
uint8_t v___x_6485_; lean_object* v___x_6486_; lean_object* v___f_6487_; lean_object* v___x_6488_; 
v___x_6485_ = 1;
v___x_6486_ = lean_box(v___x_6485_);
v___f_6487_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__2___lam__0___boxed), 14, 8);
lean_closure_set(v___f_6487_, 0, v___x_6469_);
lean_closure_set(v___f_6487_, 1, v_enumName_6470_);
lean_closure_set(v___f_6487_, 2, v_a_6471_);
lean_closure_set(v___f_6487_, 3, v___x_6472_);
lean_closure_set(v___f_6487_, 4, v_val_6473_);
lean_closure_set(v___f_6487_, 5, v___x_6474_);
lean_closure_set(v___f_6487_, 6, v___x_6475_);
lean_closure_set(v___f_6487_, 7, v___x_6486_);
v___x_6488_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_6476_, v_bi_6477_, v_type_6478_, v___f_6487_, v_kind_6479_, v___y_6480_, v___y_6481_, v___y_6482_, v___y_6483_);
if (lean_obj_tag(v___x_6488_) == 0)
{
lean_object* v_a_6489_; lean_object* v___x_6491_; uint8_t v_isShared_6492_; uint8_t v_isSharedCheck_6496_; 
v_a_6489_ = lean_ctor_get(v___x_6488_, 0);
v_isSharedCheck_6496_ = !lean_is_exclusive(v___x_6488_);
if (v_isSharedCheck_6496_ == 0)
{
v___x_6491_ = v___x_6488_;
v_isShared_6492_ = v_isSharedCheck_6496_;
goto v_resetjp_6490_;
}
else
{
lean_inc(v_a_6489_);
lean_dec(v___x_6488_);
v___x_6491_ = lean_box(0);
v_isShared_6492_ = v_isSharedCheck_6496_;
goto v_resetjp_6490_;
}
v_resetjp_6490_:
{
lean_object* v___x_6494_; 
if (v_isShared_6492_ == 0)
{
v___x_6494_ = v___x_6491_;
goto v_reusejp_6493_;
}
else
{
lean_object* v_reuseFailAlloc_6495_; 
v_reuseFailAlloc_6495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6495_, 0, v_a_6489_);
v___x_6494_ = v_reuseFailAlloc_6495_;
goto v_reusejp_6493_;
}
v_reusejp_6493_:
{
return v___x_6494_;
}
}
}
else
{
lean_object* v_a_6497_; lean_object* v___x_6499_; uint8_t v_isShared_6500_; uint8_t v_isSharedCheck_6504_; 
v_a_6497_ = lean_ctor_get(v___x_6488_, 0);
v_isSharedCheck_6504_ = !lean_is_exclusive(v___x_6488_);
if (v_isSharedCheck_6504_ == 0)
{
v___x_6499_ = v___x_6488_;
v_isShared_6500_ = v_isSharedCheck_6504_;
goto v_resetjp_6498_;
}
else
{
lean_inc(v_a_6497_);
lean_dec(v___x_6488_);
v___x_6499_ = lean_box(0);
v_isShared_6500_ = v_isSharedCheck_6504_;
goto v_resetjp_6498_;
}
v_resetjp_6498_:
{
lean_object* v___x_6502_; 
if (v_isShared_6500_ == 0)
{
v___x_6502_ = v___x_6499_;
goto v_reusejp_6501_;
}
else
{
lean_object* v_reuseFailAlloc_6503_; 
v_reuseFailAlloc_6503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6503_, 0, v_a_6497_);
v___x_6502_ = v_reuseFailAlloc_6503_;
goto v_reusejp_6501_;
}
v_reusejp_6501_:
{
return v___x_6502_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__2___boxed(lean_object* v___x_6505_, lean_object* v_enumName_6506_, lean_object* v_a_6507_, lean_object* v___x_6508_, lean_object* v_val_6509_, lean_object* v___x_6510_, lean_object* v___x_6511_, lean_object* v_name_6512_, lean_object* v_bi_6513_, lean_object* v_type_6514_, lean_object* v_kind_6515_, lean_object* v___y_6516_, lean_object* v___y_6517_, lean_object* v___y_6518_, lean_object* v___y_6519_, lean_object* v___y_6520_){
_start:
{
uint8_t v_bi_boxed_6521_; uint8_t v_kind_boxed_6522_; lean_object* v_res_6523_; 
v_bi_boxed_6521_ = lean_unbox(v_bi_6513_);
v_kind_boxed_6522_ = lean_unbox(v_kind_6515_);
v_res_6523_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__2(v___x_6505_, v_enumName_6506_, v_a_6507_, v___x_6508_, v_val_6509_, v___x_6510_, v___x_6511_, v_name_6512_, v_bi_boxed_6521_, v_type_6514_, v_kind_boxed_6522_, v___y_6516_, v___y_6517_, v___y_6518_, v___y_6519_);
lean_dec(v___y_6519_);
lean_dec_ref(v___y_6518_);
lean_dec(v___y_6517_);
lean_dec_ref(v___y_6516_);
return v_res_6523_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion___closed__1(void){
_start:
{
lean_object* v___x_6525_; lean_object* v___x_6526_; lean_object* v___x_6527_; lean_object* v___x_6528_; lean_object* v___x_6529_; lean_object* v___x_6530_; 
v___x_6525_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__6));
v___x_6526_ = lean_unsigned_to_nat(63u);
v___x_6527_ = lean_unsigned_to_nat(405u);
v___x_6528_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion___closed__0));
v___x_6529_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__2));
v___x_6530_ = l_mkPanicMessageWithDecl(v___x_6529_, v___x_6528_, v___x_6527_, v___x_6526_, v___x_6525_);
return v___x_6530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion(lean_object* v_enumName_6531_, lean_object* v_a_6532_, lean_object* v_a_6533_, lean_object* v_a_6534_, lean_object* v_a_6535_){
_start:
{
lean_object* v___x_6537_; 
lean_inc(v_enumName_6531_);
v___x_6537_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(v_enumName_6531_, v_a_6532_, v_a_6533_, v_a_6534_, v_a_6535_);
if (lean_obj_tag(v___x_6537_) == 0)
{
lean_object* v_a_6538_; 
v_a_6538_ = lean_ctor_get(v___x_6537_, 0);
lean_inc(v_a_6538_);
lean_dec_ref_known(v___x_6537_, 1);
if (lean_obj_tag(v_a_6538_) == 5)
{
lean_object* v_val_6539_; lean_object* v___x_6540_; lean_object* v___x_6541_; 
v_val_6539_ = lean_ctor_get(v_a_6538_, 0);
lean_inc_ref(v_val_6539_);
lean_dec_ref_known(v_a_6538_, 1);
v___x_6540_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___closed__1));
v___x_6541_ = l_Lean_Core_mkFreshUserName(v___x_6540_, v_a_6534_, v_a_6535_);
if (lean_obj_tag(v___x_6541_) == 0)
{
lean_object* v_toConstantVal_6542_; lean_object* v_a_6543_; lean_object* v_levelParams_6544_; lean_object* v___x_6545_; lean_object* v___x_6546_; lean_object* v___x_6547_; lean_object* v___x_6548_; lean_object* v___x_6549_; lean_object* v___x_6550_; lean_object* v___x_6551_; lean_object* v___x_6552_; lean_object* v___x_6553_; lean_object* v___x_6554_; lean_object* v___x_6555_; lean_object* v___x_6556_; uint8_t v___x_6557_; uint8_t v___x_6558_; lean_object* v___x_6559_; 
v_toConstantVal_6542_ = lean_ctor_get(v_val_6539_, 0);
v_a_6543_ = lean_ctor_get(v___x_6541_, 0);
lean_inc_n(v_a_6543_, 2);
lean_dec_ref_known(v___x_6541_, 1);
v_levelParams_6544_ = lean_ctor_get(v_toConstantVal_6542_, 1);
lean_inc_n(v_levelParams_6544_, 2);
v___x_6545_ = lean_box(0);
v___x_6546_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__2(v_levelParams_6544_, v___x_6545_);
lean_inc_n(v___x_6546_, 2);
lean_inc_n(v_enumName_6531_, 3);
v___x_6547_ = l_Lean_mkConst(v_enumName_6531_, v___x_6546_);
v___x_6548_ = l_Lean_mkLevelParam(v_a_6543_);
lean_inc(v___x_6548_);
v___x_6549_ = l_Lean_mkSort(v___x_6548_);
v___x_6550_ = l_Lean_mkCtorIdxName(v_enumName_6531_);
v___x_6551_ = l_Lean_mkConst(v___x_6550_, v___x_6546_);
v___x_6552_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionTypeName___closed__0));
v___x_6553_ = l_Lean_Name_str___override(v_enumName_6531_, v___x_6552_);
v___x_6554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6554_, 0, v___x_6548_);
lean_ctor_set(v___x_6554_, 1, v___x_6546_);
v___x_6555_ = l_Lean_mkConst(v___x_6553_, v___x_6554_);
v___x_6556_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__1));
v___x_6557_ = 1;
v___x_6558_ = 0;
v___x_6559_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__2(v___x_6555_, v_enumName_6531_, v_a_6543_, v_levelParams_6544_, v_val_6539_, v___x_6551_, v___x_6547_, v___x_6556_, v___x_6557_, v___x_6549_, v___x_6558_, v_a_6532_, v_a_6533_, v_a_6534_, v_a_6535_);
return v___x_6559_;
}
else
{
lean_object* v_a_6560_; lean_object* v___x_6562_; uint8_t v_isShared_6563_; uint8_t v_isSharedCheck_6567_; 
lean_dec_ref(v_val_6539_);
lean_dec(v_enumName_6531_);
v_a_6560_ = lean_ctor_get(v___x_6541_, 0);
v_isSharedCheck_6567_ = !lean_is_exclusive(v___x_6541_);
if (v_isSharedCheck_6567_ == 0)
{
v___x_6562_ = v___x_6541_;
v_isShared_6563_ = v_isSharedCheck_6567_;
goto v_resetjp_6561_;
}
else
{
lean_inc(v_a_6560_);
lean_dec(v___x_6541_);
v___x_6562_ = lean_box(0);
v_isShared_6563_ = v_isSharedCheck_6567_;
goto v_resetjp_6561_;
}
v_resetjp_6561_:
{
lean_object* v___x_6565_; 
if (v_isShared_6563_ == 0)
{
v___x_6565_ = v___x_6562_;
goto v_reusejp_6564_;
}
else
{
lean_object* v_reuseFailAlloc_6566_; 
v_reuseFailAlloc_6566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6566_, 0, v_a_6560_);
v___x_6565_ = v_reuseFailAlloc_6566_;
goto v_reusejp_6564_;
}
v_reusejp_6564_:
{
return v___x_6565_;
}
}
}
}
else
{
lean_object* v___x_6568_; lean_object* v___x_6569_; 
lean_dec(v_a_6538_);
lean_dec(v_enumName_6531_);
v___x_6568_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion___closed__1, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion___closed__1_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion___closed__1);
v___x_6569_ = l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8(v___x_6568_, v_a_6532_, v_a_6533_, v_a_6534_, v_a_6535_);
return v___x_6569_;
}
}
else
{
lean_object* v_a_6570_; lean_object* v___x_6572_; uint8_t v_isShared_6573_; uint8_t v_isSharedCheck_6577_; 
lean_dec(v_enumName_6531_);
v_a_6570_ = lean_ctor_get(v___x_6537_, 0);
v_isSharedCheck_6577_ = !lean_is_exclusive(v___x_6537_);
if (v_isSharedCheck_6577_ == 0)
{
v___x_6572_ = v___x_6537_;
v_isShared_6573_ = v_isSharedCheck_6577_;
goto v_resetjp_6571_;
}
else
{
lean_inc(v_a_6570_);
lean_dec(v___x_6537_);
v___x_6572_ = lean_box(0);
v_isShared_6573_ = v_isSharedCheck_6577_;
goto v_resetjp_6571_;
}
v_resetjp_6571_:
{
lean_object* v___x_6575_; 
if (v_isShared_6573_ == 0)
{
v___x_6575_ = v___x_6572_;
goto v_reusejp_6574_;
}
else
{
lean_object* v_reuseFailAlloc_6576_; 
v_reuseFailAlloc_6576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6576_, 0, v_a_6570_);
v___x_6575_ = v_reuseFailAlloc_6576_;
goto v_reusejp_6574_;
}
v_reusejp_6574_:
{
return v___x_6575_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion___boxed(lean_object* v_enumName_6578_, lean_object* v_a_6579_, lean_object* v_a_6580_, lean_object* v_a_6581_, lean_object* v_a_6582_, lean_object* v_a_6583_){
_start:
{
lean_object* v_res_6584_; 
v_res_6584_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion(v_enumName_6578_, v_a_6579_, v_a_6580_, v_a_6581_, v_a_6582_);
lean_dec(v_a_6582_);
lean_dec_ref(v_a_6581_);
lean_dec(v_a_6580_);
lean_dec_ref(v_a_6579_);
return v_res_6584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum(lean_object* v_enumName_6585_, lean_object* v_a_6586_, lean_object* v_a_6587_, lean_object* v_a_6588_, lean_object* v_a_6589_){
_start:
{
lean_object* v___x_6591_; lean_object* v_env_6592_; lean_object* v___x_6593_; uint8_t v___x_6594_; uint8_t v___x_6595_; 
v___x_6591_ = lean_st_ref_get(v_a_6589_);
v_env_6592_ = lean_ctor_get(v___x_6591_, 0);
lean_inc_ref(v_env_6592_);
lean_dec(v___x_6591_);
v___x_6593_ = ((lean_object*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__2));
v___x_6594_ = 1;
v___x_6595_ = l_Lean_Environment_contains(v_env_6592_, v___x_6593_, v___x_6594_);
if (v___x_6595_ == 0)
{
lean_object* v___x_6596_; 
v___x_6596_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCore(v_enumName_6585_, v_a_6586_, v_a_6587_, v_a_6588_, v_a_6589_);
return v___x_6596_;
}
else
{
lean_object* v___x_6597_; 
lean_inc(v_enumName_6585_);
v___x_6597_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType(v_enumName_6585_, v_a_6586_, v_a_6587_, v_a_6588_, v_a_6589_);
if (lean_obj_tag(v___x_6597_) == 0)
{
lean_object* v___x_6598_; 
lean_dec_ref_known(v___x_6597_, 1);
v___x_6598_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion(v_enumName_6585_, v_a_6586_, v_a_6587_, v_a_6588_, v_a_6589_);
return v___x_6598_;
}
else
{
lean_dec(v_enumName_6585_);
return v___x_6597_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum___boxed(lean_object* v_enumName_6599_, lean_object* v_a_6600_, lean_object* v_a_6601_, lean_object* v_a_6602_, lean_object* v_a_6603_, lean_object* v_a_6604_){
_start:
{
lean_object* v_res_6605_; 
v_res_6605_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum(v_enumName_6599_, v_a_6600_, v_a_6601_, v_a_6602_, v_a_6603_);
lean_dec(v_a_6603_);
lean_dec_ref(v_a_6602_);
lean_dec(v_a_6601_);
lean_dec_ref(v_a_6600_);
return v_res_6605_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_6606_; lean_object* v___x_6607_; lean_object* v___x_6608_; 
v___x_6606_ = lean_unsigned_to_nat(32u);
v___x_6607_ = lean_mk_empty_array_with_capacity(v___x_6606_);
v___x_6608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6608_, 0, v___x_6607_);
return v___x_6608_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_6609_; lean_object* v___x_6610_; lean_object* v___x_6611_; lean_object* v___x_6612_; lean_object* v___x_6613_; lean_object* v___x_6614_; 
v___x_6609_ = ((size_t)5ULL);
v___x_6610_ = lean_unsigned_to_nat(0u);
v___x_6611_ = lean_unsigned_to_nat(32u);
v___x_6612_ = lean_mk_empty_array_with_capacity(v___x_6611_);
v___x_6613_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg___closed__0);
v___x_6614_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6614_, 0, v___x_6613_);
lean_ctor_set(v___x_6614_, 1, v___x_6612_);
lean_ctor_set(v___x_6614_, 2, v___x_6610_);
lean_ctor_set(v___x_6614_, 3, v___x_6610_);
lean_ctor_set_usize(v___x_6614_, 4, v___x_6609_);
return v___x_6614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg(lean_object* v___y_6615_){
_start:
{
lean_object* v___x_6617_; lean_object* v_traceState_6618_; lean_object* v_traces_6619_; lean_object* v___x_6620_; lean_object* v_traceState_6621_; lean_object* v_env_6622_; lean_object* v_nextMacroScope_6623_; lean_object* v_ngen_6624_; lean_object* v_auxDeclNGen_6625_; lean_object* v_cache_6626_; lean_object* v_messages_6627_; lean_object* v_infoState_6628_; lean_object* v_snapshotTasks_6629_; lean_object* v___x_6631_; uint8_t v_isShared_6632_; uint8_t v_isSharedCheck_6648_; 
v___x_6617_ = lean_st_ref_get(v___y_6615_);
v_traceState_6618_ = lean_ctor_get(v___x_6617_, 4);
lean_inc_ref(v_traceState_6618_);
lean_dec(v___x_6617_);
v_traces_6619_ = lean_ctor_get(v_traceState_6618_, 0);
lean_inc_ref(v_traces_6619_);
lean_dec_ref(v_traceState_6618_);
v___x_6620_ = lean_st_ref_take(v___y_6615_);
v_traceState_6621_ = lean_ctor_get(v___x_6620_, 4);
v_env_6622_ = lean_ctor_get(v___x_6620_, 0);
v_nextMacroScope_6623_ = lean_ctor_get(v___x_6620_, 1);
v_ngen_6624_ = lean_ctor_get(v___x_6620_, 2);
v_auxDeclNGen_6625_ = lean_ctor_get(v___x_6620_, 3);
v_cache_6626_ = lean_ctor_get(v___x_6620_, 5);
v_messages_6627_ = lean_ctor_get(v___x_6620_, 6);
v_infoState_6628_ = lean_ctor_get(v___x_6620_, 7);
v_snapshotTasks_6629_ = lean_ctor_get(v___x_6620_, 8);
v_isSharedCheck_6648_ = !lean_is_exclusive(v___x_6620_);
if (v_isSharedCheck_6648_ == 0)
{
v___x_6631_ = v___x_6620_;
v_isShared_6632_ = v_isSharedCheck_6648_;
goto v_resetjp_6630_;
}
else
{
lean_inc(v_snapshotTasks_6629_);
lean_inc(v_infoState_6628_);
lean_inc(v_messages_6627_);
lean_inc(v_cache_6626_);
lean_inc(v_traceState_6621_);
lean_inc(v_auxDeclNGen_6625_);
lean_inc(v_ngen_6624_);
lean_inc(v_nextMacroScope_6623_);
lean_inc(v_env_6622_);
lean_dec(v___x_6620_);
v___x_6631_ = lean_box(0);
v_isShared_6632_ = v_isSharedCheck_6648_;
goto v_resetjp_6630_;
}
v_resetjp_6630_:
{
uint64_t v_tid_6633_; lean_object* v___x_6635_; uint8_t v_isShared_6636_; uint8_t v_isSharedCheck_6646_; 
v_tid_6633_ = lean_ctor_get_uint64(v_traceState_6621_, sizeof(void*)*1);
v_isSharedCheck_6646_ = !lean_is_exclusive(v_traceState_6621_);
if (v_isSharedCheck_6646_ == 0)
{
lean_object* v_unused_6647_; 
v_unused_6647_ = lean_ctor_get(v_traceState_6621_, 0);
lean_dec(v_unused_6647_);
v___x_6635_ = v_traceState_6621_;
v_isShared_6636_ = v_isSharedCheck_6646_;
goto v_resetjp_6634_;
}
else
{
lean_dec(v_traceState_6621_);
v___x_6635_ = lean_box(0);
v_isShared_6636_ = v_isSharedCheck_6646_;
goto v_resetjp_6634_;
}
v_resetjp_6634_:
{
lean_object* v___x_6637_; lean_object* v___x_6639_; 
v___x_6637_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg___closed__1);
if (v_isShared_6636_ == 0)
{
lean_ctor_set(v___x_6635_, 0, v___x_6637_);
v___x_6639_ = v___x_6635_;
goto v_reusejp_6638_;
}
else
{
lean_object* v_reuseFailAlloc_6645_; 
v_reuseFailAlloc_6645_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6645_, 0, v___x_6637_);
lean_ctor_set_uint64(v_reuseFailAlloc_6645_, sizeof(void*)*1, v_tid_6633_);
v___x_6639_ = v_reuseFailAlloc_6645_;
goto v_reusejp_6638_;
}
v_reusejp_6638_:
{
lean_object* v___x_6641_; 
if (v_isShared_6632_ == 0)
{
lean_ctor_set(v___x_6631_, 4, v___x_6639_);
v___x_6641_ = v___x_6631_;
goto v_reusejp_6640_;
}
else
{
lean_object* v_reuseFailAlloc_6644_; 
v_reuseFailAlloc_6644_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6644_, 0, v_env_6622_);
lean_ctor_set(v_reuseFailAlloc_6644_, 1, v_nextMacroScope_6623_);
lean_ctor_set(v_reuseFailAlloc_6644_, 2, v_ngen_6624_);
lean_ctor_set(v_reuseFailAlloc_6644_, 3, v_auxDeclNGen_6625_);
lean_ctor_set(v_reuseFailAlloc_6644_, 4, v___x_6639_);
lean_ctor_set(v_reuseFailAlloc_6644_, 5, v_cache_6626_);
lean_ctor_set(v_reuseFailAlloc_6644_, 6, v_messages_6627_);
lean_ctor_set(v_reuseFailAlloc_6644_, 7, v_infoState_6628_);
lean_ctor_set(v_reuseFailAlloc_6644_, 8, v_snapshotTasks_6629_);
v___x_6641_ = v_reuseFailAlloc_6644_;
goto v_reusejp_6640_;
}
v_reusejp_6640_:
{
lean_object* v___x_6642_; lean_object* v___x_6643_; 
v___x_6642_ = lean_st_ref_put(v___y_6615_, v___x_6641_);
v___x_6643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6643_, 0, v_traces_6619_);
return v___x_6643_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg___boxed(lean_object* v___y_6649_, lean_object* v___y_6650_){
_start:
{
lean_object* v_res_6651_; 
v_res_6651_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg(v___y_6649_);
lean_dec(v___y_6649_);
return v_res_6651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1(lean_object* v___y_6652_, lean_object* v___y_6653_, lean_object* v___y_6654_, lean_object* v___y_6655_){
_start:
{
lean_object* v___x_6657_; 
v___x_6657_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg(v___y_6655_);
return v___x_6657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___boxed(lean_object* v___y_6658_, lean_object* v___y_6659_, lean_object* v___y_6660_, lean_object* v___y_6661_, lean_object* v___y_6662_){
_start:
{
lean_object* v_res_6663_; 
v_res_6663_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1(v___y_6658_, v___y_6659_, v___y_6660_, v___y_6661_);
lean_dec(v___y_6661_);
lean_dec_ref(v___y_6660_);
lean_dec(v___y_6659_);
lean_dec_ref(v___y_6658_);
return v_res_6663_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNoConfusion___lam__0(lean_object* v_declName_6664_, lean_object* v_x_6665_, lean_object* v___y_6666_, lean_object* v___y_6667_, lean_object* v___y_6668_, lean_object* v___y_6669_){
_start:
{
lean_object* v___x_6671_; lean_object* v___x_6672_; 
v___x_6671_ = l_Lean_MessageData_ofName(v_declName_6664_);
v___x_6672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6672_, 0, v___x_6671_);
return v___x_6672_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNoConfusion___lam__0___boxed(lean_object* v_declName_6673_, lean_object* v_x_6674_, lean_object* v___y_6675_, lean_object* v___y_6676_, lean_object* v___y_6677_, lean_object* v___y_6678_, lean_object* v___y_6679_){
_start:
{
lean_object* v_res_6680_; 
v_res_6680_ = l_Lean_mkNoConfusion___lam__0(v_declName_6673_, v_x_6674_, v___y_6675_, v___y_6676_, v___y_6677_, v___y_6678_);
lean_dec(v___y_6678_);
lean_dec_ref(v___y_6677_);
lean_dec(v___y_6676_);
lean_dec_ref(v___y_6675_);
lean_dec_ref(v_x_6674_);
return v_res_6680_;
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0_spec__0(uint8_t v___x_6681_, lean_object* v_x_6682_, lean_object* v___y_6683_, lean_object* v___y_6684_, lean_object* v___y_6685_, lean_object* v___y_6686_){
_start:
{
if (lean_obj_tag(v_x_6682_) == 0)
{
uint8_t v___x_6688_; lean_object* v___x_6689_; lean_object* v___x_6690_; 
v___x_6688_ = 1;
v___x_6689_ = lean_box(v___x_6688_);
v___x_6690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6690_, 0, v___x_6689_);
return v___x_6690_;
}
else
{
lean_object* v_head_6691_; lean_object* v_tail_6692_; lean_object* v___x_6693_; 
v_head_6691_ = lean_ctor_get(v_x_6682_, 0);
lean_inc(v_head_6691_);
v_tail_6692_ = lean_ctor_get(v_x_6682_, 1);
lean_inc(v_tail_6692_);
lean_dec_ref_known(v_x_6682_, 2);
v___x_6693_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(v_head_6691_, v___y_6683_, v___y_6684_, v___y_6685_, v___y_6686_);
if (lean_obj_tag(v___x_6693_) == 0)
{
lean_object* v_a_6694_; lean_object* v___x_6696_; uint8_t v_isShared_6697_; uint8_t v_isSharedCheck_6714_; 
v_a_6694_ = lean_ctor_get(v___x_6693_, 0);
v_isSharedCheck_6714_ = !lean_is_exclusive(v___x_6693_);
if (v_isSharedCheck_6714_ == 0)
{
v___x_6696_ = v___x_6693_;
v_isShared_6697_ = v_isSharedCheck_6714_;
goto v_resetjp_6695_;
}
else
{
lean_inc(v_a_6694_);
lean_dec(v___x_6693_);
v___x_6696_ = lean_box(0);
v_isShared_6697_ = v_isSharedCheck_6714_;
goto v_resetjp_6695_;
}
v_resetjp_6695_:
{
lean_object* v___y_6699_; uint8_t v_a_6700_; 
if (lean_obj_tag(v_a_6694_) == 6)
{
lean_object* v_val_6702_; lean_object* v_numFields_6703_; lean_object* v___x_6704_; uint8_t v___x_6705_; lean_object* v___x_6706_; lean_object* v___x_6708_; 
v_val_6702_ = lean_ctor_get(v_a_6694_, 0);
lean_inc_ref(v_val_6702_);
lean_dec_ref_known(v_a_6694_, 1);
v_numFields_6703_ = lean_ctor_get(v_val_6702_, 4);
lean_inc(v_numFields_6703_);
lean_dec_ref(v_val_6702_);
v___x_6704_ = lean_unsigned_to_nat(0u);
v___x_6705_ = lean_nat_dec_eq(v_numFields_6703_, v___x_6704_);
lean_dec(v_numFields_6703_);
v___x_6706_ = lean_box(v___x_6705_);
if (v_isShared_6697_ == 0)
{
lean_ctor_set(v___x_6696_, 0, v___x_6706_);
v___x_6708_ = v___x_6696_;
goto v_reusejp_6707_;
}
else
{
lean_object* v_reuseFailAlloc_6709_; 
v_reuseFailAlloc_6709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6709_, 0, v___x_6706_);
v___x_6708_ = v_reuseFailAlloc_6709_;
goto v_reusejp_6707_;
}
v_reusejp_6707_:
{
v___y_6699_ = v___x_6708_;
v_a_6700_ = v___x_6705_;
goto v___jp_6698_;
}
}
else
{
lean_object* v___x_6710_; lean_object* v___x_6712_; 
lean_dec(v_a_6694_);
v___x_6710_ = lean_box(v___x_6681_);
if (v_isShared_6697_ == 0)
{
lean_ctor_set(v___x_6696_, 0, v___x_6710_);
v___x_6712_ = v___x_6696_;
goto v_reusejp_6711_;
}
else
{
lean_object* v_reuseFailAlloc_6713_; 
v_reuseFailAlloc_6713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6713_, 0, v___x_6710_);
v___x_6712_ = v_reuseFailAlloc_6713_;
goto v_reusejp_6711_;
}
v_reusejp_6711_:
{
v___y_6699_ = v___x_6712_;
v_a_6700_ = v___x_6681_;
goto v___jp_6698_;
}
}
v___jp_6698_:
{
if (v_a_6700_ == 0)
{
lean_dec(v_tail_6692_);
return v___y_6699_;
}
else
{
lean_dec_ref(v___y_6699_);
v_x_6682_ = v_tail_6692_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_6715_; lean_object* v___x_6717_; uint8_t v_isShared_6718_; uint8_t v_isSharedCheck_6722_; 
lean_dec(v_tail_6692_);
v_a_6715_ = lean_ctor_get(v___x_6693_, 0);
v_isSharedCheck_6722_ = !lean_is_exclusive(v___x_6693_);
if (v_isSharedCheck_6722_ == 0)
{
v___x_6717_ = v___x_6693_;
v_isShared_6718_ = v_isSharedCheck_6722_;
goto v_resetjp_6716_;
}
else
{
lean_inc(v_a_6715_);
lean_dec(v___x_6693_);
v___x_6717_ = lean_box(0);
v_isShared_6718_ = v_isSharedCheck_6722_;
goto v_resetjp_6716_;
}
v_resetjp_6716_:
{
lean_object* v___x_6720_; 
if (v_isShared_6718_ == 0)
{
v___x_6720_ = v___x_6717_;
goto v_reusejp_6719_;
}
else
{
lean_object* v_reuseFailAlloc_6721_; 
v_reuseFailAlloc_6721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6721_, 0, v_a_6715_);
v___x_6720_ = v_reuseFailAlloc_6721_;
goto v_reusejp_6719_;
}
v_reusejp_6719_:
{
return v___x_6720_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0_spec__0___boxed(lean_object* v___x_6723_, lean_object* v_x_6724_, lean_object* v___y_6725_, lean_object* v___y_6726_, lean_object* v___y_6727_, lean_object* v___y_6728_, lean_object* v___y_6729_){
_start:
{
uint8_t v___x_8250__boxed_6730_; lean_object* v_res_6731_; 
v___x_8250__boxed_6730_ = lean_unbox(v___x_6723_);
v_res_6731_ = l_List_allM___at___00Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0_spec__0(v___x_8250__boxed_6730_, v_x_6724_, v___y_6725_, v___y_6726_, v___y_6727_, v___y_6728_);
lean_dec(v___y_6728_);
lean_dec_ref(v___y_6727_);
lean_dec(v___y_6726_);
lean_dec_ref(v___y_6725_);
return v_res_6731_;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0(lean_object* v_declName_6732_, lean_object* v___y_6733_, lean_object* v___y_6734_, lean_object* v___y_6735_, lean_object* v___y_6736_){
_start:
{
lean_object* v___x_6738_; 
v___x_6738_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(v_declName_6732_, v___y_6733_, v___y_6734_, v___y_6735_, v___y_6736_);
if (lean_obj_tag(v___x_6738_) == 0)
{
lean_object* v_a_6739_; lean_object* v___x_6741_; uint8_t v_isShared_6742_; uint8_t v_isSharedCheck_6794_; 
v_a_6739_ = lean_ctor_get(v___x_6738_, 0);
v_isSharedCheck_6794_ = !lean_is_exclusive(v___x_6738_);
if (v_isSharedCheck_6794_ == 0)
{
v___x_6741_ = v___x_6738_;
v_isShared_6742_ = v_isSharedCheck_6794_;
goto v_resetjp_6740_;
}
else
{
lean_inc(v_a_6739_);
lean_dec(v___x_6738_);
v___x_6741_ = lean_box(0);
v_isShared_6742_ = v_isSharedCheck_6794_;
goto v_resetjp_6740_;
}
v_resetjp_6740_:
{
if (lean_obj_tag(v_a_6739_) == 5)
{
lean_object* v_val_6743_; lean_object* v_toConstantVal_6744_; lean_object* v_numParams_6745_; lean_object* v_numIndices_6746_; lean_object* v_ctors_6747_; uint8_t v_isRec_6748_; uint8_t v_isUnsafe_6749_; lean_object* v_type_6750_; uint8_t v___x_6751_; 
v_val_6743_ = lean_ctor_get(v_a_6739_, 0);
lean_inc_ref(v_val_6743_);
lean_dec_ref_known(v_a_6739_, 1);
v_toConstantVal_6744_ = lean_ctor_get(v_val_6743_, 0);
v_numParams_6745_ = lean_ctor_get(v_val_6743_, 1);
lean_inc(v_numParams_6745_);
v_numIndices_6746_ = lean_ctor_get(v_val_6743_, 2);
lean_inc(v_numIndices_6746_);
v_ctors_6747_ = lean_ctor_get(v_val_6743_, 4);
lean_inc(v_ctors_6747_);
v_isRec_6748_ = lean_ctor_get_uint8(v_val_6743_, sizeof(void*)*6);
v_isUnsafe_6749_ = lean_ctor_get_uint8(v_val_6743_, sizeof(void*)*6 + 1);
v_type_6750_ = lean_ctor_get(v_toConstantVal_6744_, 2);
v___x_6751_ = l_Lean_Expr_isProp(v_type_6750_);
if (v___x_6751_ == 0)
{
lean_object* v___x_6752_; lean_object* v___x_6753_; uint8_t v___x_6754_; 
v___x_6752_ = l_Lean_InductiveVal_numTypeFormers(v_val_6743_);
lean_dec_ref(v_val_6743_);
v___x_6753_ = lean_unsigned_to_nat(1u);
v___x_6754_ = lean_nat_dec_eq(v___x_6752_, v___x_6753_);
lean_dec(v___x_6752_);
if (v___x_6754_ == 0)
{
lean_object* v___x_6755_; lean_object* v___x_6757_; 
lean_dec(v_ctors_6747_);
lean_dec(v_numIndices_6746_);
lean_dec(v_numParams_6745_);
v___x_6755_ = lean_box(v___x_6754_);
if (v_isShared_6742_ == 0)
{
lean_ctor_set(v___x_6741_, 0, v___x_6755_);
v___x_6757_ = v___x_6741_;
goto v_reusejp_6756_;
}
else
{
lean_object* v_reuseFailAlloc_6758_; 
v_reuseFailAlloc_6758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6758_, 0, v___x_6755_);
v___x_6757_ = v_reuseFailAlloc_6758_;
goto v_reusejp_6756_;
}
v_reusejp_6756_:
{
return v___x_6757_;
}
}
else
{
lean_object* v___x_6759_; uint8_t v___x_6760_; 
v___x_6759_ = lean_unsigned_to_nat(0u);
v___x_6760_ = lean_nat_dec_eq(v_numIndices_6746_, v___x_6759_);
lean_dec(v_numIndices_6746_);
if (v___x_6760_ == 0)
{
lean_object* v___x_6761_; lean_object* v___x_6763_; 
lean_dec(v_ctors_6747_);
lean_dec(v_numParams_6745_);
v___x_6761_ = lean_box(v___x_6760_);
if (v_isShared_6742_ == 0)
{
lean_ctor_set(v___x_6741_, 0, v___x_6761_);
v___x_6763_ = v___x_6741_;
goto v_reusejp_6762_;
}
else
{
lean_object* v_reuseFailAlloc_6764_; 
v_reuseFailAlloc_6764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6764_, 0, v___x_6761_);
v___x_6763_ = v_reuseFailAlloc_6764_;
goto v_reusejp_6762_;
}
v_reusejp_6762_:
{
return v___x_6763_;
}
}
else
{
uint8_t v___x_6765_; 
v___x_6765_ = lean_nat_dec_eq(v_numParams_6745_, v___x_6759_);
lean_dec(v_numParams_6745_);
if (v___x_6765_ == 0)
{
lean_object* v___x_6766_; lean_object* v___x_6768_; 
lean_dec(v_ctors_6747_);
v___x_6766_ = lean_box(v___x_6765_);
if (v_isShared_6742_ == 0)
{
lean_ctor_set(v___x_6741_, 0, v___x_6766_);
v___x_6768_ = v___x_6741_;
goto v_reusejp_6767_;
}
else
{
lean_object* v_reuseFailAlloc_6769_; 
v_reuseFailAlloc_6769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6769_, 0, v___x_6766_);
v___x_6768_ = v_reuseFailAlloc_6769_;
goto v_reusejp_6767_;
}
v_reusejp_6767_:
{
return v___x_6768_;
}
}
else
{
uint8_t v___x_6770_; 
v___x_6770_ = l_List_isEmpty___redArg(v_ctors_6747_);
if (v___x_6770_ == 0)
{
if (v_isRec_6748_ == 0)
{
if (v_isUnsafe_6749_ == 0)
{
lean_object* v___x_6771_; 
lean_del_object(v___x_6741_);
v___x_6771_ = l_List_allM___at___00Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0_spec__0(v_isUnsafe_6749_, v_ctors_6747_, v___y_6733_, v___y_6734_, v___y_6735_, v___y_6736_);
return v___x_6771_;
}
else
{
lean_object* v___x_6772_; lean_object* v___x_6774_; 
lean_dec(v_ctors_6747_);
v___x_6772_ = lean_box(v_isRec_6748_);
if (v_isShared_6742_ == 0)
{
lean_ctor_set(v___x_6741_, 0, v___x_6772_);
v___x_6774_ = v___x_6741_;
goto v_reusejp_6773_;
}
else
{
lean_object* v_reuseFailAlloc_6775_; 
v_reuseFailAlloc_6775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6775_, 0, v___x_6772_);
v___x_6774_ = v_reuseFailAlloc_6775_;
goto v_reusejp_6773_;
}
v_reusejp_6773_:
{
return v___x_6774_;
}
}
}
else
{
lean_object* v___x_6776_; lean_object* v___x_6778_; 
lean_dec(v_ctors_6747_);
v___x_6776_ = lean_box(v___x_6770_);
if (v_isShared_6742_ == 0)
{
lean_ctor_set(v___x_6741_, 0, v___x_6776_);
v___x_6778_ = v___x_6741_;
goto v_reusejp_6777_;
}
else
{
lean_object* v_reuseFailAlloc_6779_; 
v_reuseFailAlloc_6779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6779_, 0, v___x_6776_);
v___x_6778_ = v_reuseFailAlloc_6779_;
goto v_reusejp_6777_;
}
v_reusejp_6777_:
{
return v___x_6778_;
}
}
}
else
{
lean_object* v___x_6780_; lean_object* v___x_6782_; 
lean_dec(v_ctors_6747_);
v___x_6780_ = lean_box(v___x_6751_);
if (v_isShared_6742_ == 0)
{
lean_ctor_set(v___x_6741_, 0, v___x_6780_);
v___x_6782_ = v___x_6741_;
goto v_reusejp_6781_;
}
else
{
lean_object* v_reuseFailAlloc_6783_; 
v_reuseFailAlloc_6783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6783_, 0, v___x_6780_);
v___x_6782_ = v_reuseFailAlloc_6783_;
goto v_reusejp_6781_;
}
v_reusejp_6781_:
{
return v___x_6782_;
}
}
}
}
}
}
else
{
uint8_t v___x_6784_; lean_object* v___x_6785_; lean_object* v___x_6787_; 
lean_dec(v_ctors_6747_);
lean_dec(v_numIndices_6746_);
lean_dec(v_numParams_6745_);
lean_dec_ref(v_val_6743_);
v___x_6784_ = 0;
v___x_6785_ = lean_box(v___x_6784_);
if (v_isShared_6742_ == 0)
{
lean_ctor_set(v___x_6741_, 0, v___x_6785_);
v___x_6787_ = v___x_6741_;
goto v_reusejp_6786_;
}
else
{
lean_object* v_reuseFailAlloc_6788_; 
v_reuseFailAlloc_6788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6788_, 0, v___x_6785_);
v___x_6787_ = v_reuseFailAlloc_6788_;
goto v_reusejp_6786_;
}
v_reusejp_6786_:
{
return v___x_6787_;
}
}
}
else
{
uint8_t v___x_6789_; lean_object* v___x_6790_; lean_object* v___x_6792_; 
lean_dec(v_a_6739_);
v___x_6789_ = 0;
v___x_6790_ = lean_box(v___x_6789_);
if (v_isShared_6742_ == 0)
{
lean_ctor_set(v___x_6741_, 0, v___x_6790_);
v___x_6792_ = v___x_6741_;
goto v_reusejp_6791_;
}
else
{
lean_object* v_reuseFailAlloc_6793_; 
v_reuseFailAlloc_6793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6793_, 0, v___x_6790_);
v___x_6792_ = v_reuseFailAlloc_6793_;
goto v_reusejp_6791_;
}
v_reusejp_6791_:
{
return v___x_6792_;
}
}
}
}
else
{
lean_object* v_a_6795_; lean_object* v___x_6797_; uint8_t v_isShared_6798_; uint8_t v_isSharedCheck_6802_; 
v_a_6795_ = lean_ctor_get(v___x_6738_, 0);
v_isSharedCheck_6802_ = !lean_is_exclusive(v___x_6738_);
if (v_isSharedCheck_6802_ == 0)
{
v___x_6797_ = v___x_6738_;
v_isShared_6798_ = v_isSharedCheck_6802_;
goto v_resetjp_6796_;
}
else
{
lean_inc(v_a_6795_);
lean_dec(v___x_6738_);
v___x_6797_ = lean_box(0);
v_isShared_6798_ = v_isSharedCheck_6802_;
goto v_resetjp_6796_;
}
v_resetjp_6796_:
{
lean_object* v___x_6800_; 
if (v_isShared_6798_ == 0)
{
v___x_6800_ = v___x_6797_;
goto v_reusejp_6799_;
}
else
{
lean_object* v_reuseFailAlloc_6801_; 
v_reuseFailAlloc_6801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6801_, 0, v_a_6795_);
v___x_6800_ = v_reuseFailAlloc_6801_;
goto v_reusejp_6799_;
}
v_reusejp_6799_:
{
return v___x_6800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0___boxed(lean_object* v_declName_6803_, lean_object* v___y_6804_, lean_object* v___y_6805_, lean_object* v___y_6806_, lean_object* v___y_6807_, lean_object* v___y_6808_){
_start:
{
lean_object* v_res_6809_; 
v_res_6809_ = l_Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0(v_declName_6803_, v___y_6804_, v___y_6805_, v___y_6806_, v___y_6807_);
lean_dec(v___y_6807_);
lean_dec_ref(v___y_6806_);
lean_dec(v___y_6805_);
lean_dec_ref(v___y_6804_);
return v_res_6809_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__4___redArg(lean_object* v_x_6810_){
_start:
{
if (lean_obj_tag(v_x_6810_) == 0)
{
lean_object* v_a_6812_; lean_object* v___x_6814_; uint8_t v_isShared_6815_; uint8_t v_isSharedCheck_6819_; 
v_a_6812_ = lean_ctor_get(v_x_6810_, 0);
v_isSharedCheck_6819_ = !lean_is_exclusive(v_x_6810_);
if (v_isSharedCheck_6819_ == 0)
{
v___x_6814_ = v_x_6810_;
v_isShared_6815_ = v_isSharedCheck_6819_;
goto v_resetjp_6813_;
}
else
{
lean_inc(v_a_6812_);
lean_dec(v_x_6810_);
v___x_6814_ = lean_box(0);
v_isShared_6815_ = v_isSharedCheck_6819_;
goto v_resetjp_6813_;
}
v_resetjp_6813_:
{
lean_object* v___x_6817_; 
if (v_isShared_6815_ == 0)
{
lean_ctor_set_tag(v___x_6814_, 1);
v___x_6817_ = v___x_6814_;
goto v_reusejp_6816_;
}
else
{
lean_object* v_reuseFailAlloc_6818_; 
v_reuseFailAlloc_6818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6818_, 0, v_a_6812_);
v___x_6817_ = v_reuseFailAlloc_6818_;
goto v_reusejp_6816_;
}
v_reusejp_6816_:
{
return v___x_6817_;
}
}
}
else
{
lean_object* v_a_6820_; lean_object* v___x_6822_; uint8_t v_isShared_6823_; uint8_t v_isSharedCheck_6827_; 
v_a_6820_ = lean_ctor_get(v_x_6810_, 0);
v_isSharedCheck_6827_ = !lean_is_exclusive(v_x_6810_);
if (v_isSharedCheck_6827_ == 0)
{
v___x_6822_ = v_x_6810_;
v_isShared_6823_ = v_isSharedCheck_6827_;
goto v_resetjp_6821_;
}
else
{
lean_inc(v_a_6820_);
lean_dec(v_x_6810_);
v___x_6822_ = lean_box(0);
v_isShared_6823_ = v_isSharedCheck_6827_;
goto v_resetjp_6821_;
}
v_resetjp_6821_:
{
lean_object* v___x_6825_; 
if (v_isShared_6823_ == 0)
{
lean_ctor_set_tag(v___x_6822_, 0);
v___x_6825_ = v___x_6822_;
goto v_reusejp_6824_;
}
else
{
lean_object* v_reuseFailAlloc_6826_; 
v_reuseFailAlloc_6826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6826_, 0, v_a_6820_);
v___x_6825_ = v_reuseFailAlloc_6826_;
goto v_reusejp_6824_;
}
v_reusejp_6824_:
{
return v___x_6825_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__4___redArg___boxed(lean_object* v_x_6828_, lean_object* v___y_6829_){
_start:
{
lean_object* v_res_6830_; 
v_res_6830_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__4___redArg(v_x_6828_);
return v_res_6830_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__5(lean_object* v_e_6831_){
_start:
{
if (lean_obj_tag(v_e_6831_) == 0)
{
uint8_t v___x_6832_; 
v___x_6832_ = 2;
return v___x_6832_;
}
else
{
uint8_t v___x_6833_; 
v___x_6833_ = 0;
return v___x_6833_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__5___boxed(lean_object* v_e_6834_){
_start:
{
uint8_t v_res_6835_; lean_object* v_r_6836_; 
v_res_6835_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__5(v_e_6834_);
lean_dec_ref(v_e_6834_);
v_r_6836_ = lean_box(v_res_6835_);
return v_r_6836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__3_spec__4(size_t v_sz_6837_, size_t v_i_6838_, lean_object* v_bs_6839_){
_start:
{
uint8_t v___x_6840_; 
v___x_6840_ = lean_usize_dec_lt(v_i_6838_, v_sz_6837_);
if (v___x_6840_ == 0)
{
return v_bs_6839_;
}
else
{
lean_object* v_v_6841_; lean_object* v_msg_6842_; lean_object* v___x_6843_; lean_object* v_bs_x27_6844_; size_t v___x_6845_; size_t v___x_6846_; lean_object* v___x_6847_; 
v_v_6841_ = lean_array_uget_borrowed(v_bs_6839_, v_i_6838_);
v_msg_6842_ = lean_ctor_get(v_v_6841_, 1);
lean_inc_ref(v_msg_6842_);
v___x_6843_ = lean_unsigned_to_nat(0u);
v_bs_x27_6844_ = lean_array_uset(v_bs_6839_, v_i_6838_, v___x_6843_);
v___x_6845_ = ((size_t)1ULL);
v___x_6846_ = lean_usize_add(v_i_6838_, v___x_6845_);
v___x_6847_ = lean_array_uset(v_bs_x27_6844_, v_i_6838_, v_msg_6842_);
v_i_6838_ = v___x_6846_;
v_bs_6839_ = v___x_6847_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__3_spec__4___boxed(lean_object* v_sz_6849_, lean_object* v_i_6850_, lean_object* v_bs_6851_){
_start:
{
size_t v_sz_boxed_6852_; size_t v_i_boxed_6853_; lean_object* v_res_6854_; 
v_sz_boxed_6852_ = lean_unbox_usize(v_sz_6849_);
lean_dec(v_sz_6849_);
v_i_boxed_6853_ = lean_unbox_usize(v_i_6850_);
lean_dec(v_i_6850_);
v_res_6854_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__3_spec__4(v_sz_boxed_6852_, v_i_boxed_6853_, v_bs_6851_);
return v_res_6854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__3(lean_object* v_oldTraces_6855_, lean_object* v_data_6856_, lean_object* v_ref_6857_, lean_object* v_msg_6858_, lean_object* v___y_6859_, lean_object* v___y_6860_, lean_object* v___y_6861_, lean_object* v___y_6862_){
_start:
{
lean_object* v_fileName_6864_; lean_object* v_fileMap_6865_; lean_object* v_options_6866_; lean_object* v_currRecDepth_6867_; lean_object* v_maxRecDepth_6868_; lean_object* v_ref_6869_; lean_object* v_currNamespace_6870_; lean_object* v_openDecls_6871_; lean_object* v_initHeartbeats_6872_; lean_object* v_maxHeartbeats_6873_; lean_object* v_quotContext_6874_; lean_object* v_currMacroScope_6875_; uint8_t v_diag_6876_; lean_object* v_cancelTk_x3f_6877_; uint8_t v_suppressElabErrors_6878_; lean_object* v_inheritedTraceOptions_6879_; lean_object* v___x_6880_; lean_object* v_traceState_6881_; lean_object* v_traces_6882_; lean_object* v_ref_6883_; lean_object* v___x_6884_; lean_object* v___x_6885_; size_t v_sz_6886_; size_t v___x_6887_; lean_object* v___x_6888_; lean_object* v_msg_6889_; lean_object* v___x_6890_; lean_object* v_a_6891_; lean_object* v___x_6893_; uint8_t v_isShared_6894_; uint8_t v_isSharedCheck_6928_; 
v_fileName_6864_ = lean_ctor_get(v___y_6861_, 0);
v_fileMap_6865_ = lean_ctor_get(v___y_6861_, 1);
v_options_6866_ = lean_ctor_get(v___y_6861_, 2);
v_currRecDepth_6867_ = lean_ctor_get(v___y_6861_, 3);
v_maxRecDepth_6868_ = lean_ctor_get(v___y_6861_, 4);
v_ref_6869_ = lean_ctor_get(v___y_6861_, 5);
v_currNamespace_6870_ = lean_ctor_get(v___y_6861_, 6);
v_openDecls_6871_ = lean_ctor_get(v___y_6861_, 7);
v_initHeartbeats_6872_ = lean_ctor_get(v___y_6861_, 8);
v_maxHeartbeats_6873_ = lean_ctor_get(v___y_6861_, 9);
v_quotContext_6874_ = lean_ctor_get(v___y_6861_, 10);
v_currMacroScope_6875_ = lean_ctor_get(v___y_6861_, 11);
v_diag_6876_ = lean_ctor_get_uint8(v___y_6861_, sizeof(void*)*14);
v_cancelTk_x3f_6877_ = lean_ctor_get(v___y_6861_, 12);
v_suppressElabErrors_6878_ = lean_ctor_get_uint8(v___y_6861_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_6879_ = lean_ctor_get(v___y_6861_, 13);
v___x_6880_ = lean_st_ref_get(v___y_6862_);
v_traceState_6881_ = lean_ctor_get(v___x_6880_, 4);
lean_inc_ref(v_traceState_6881_);
lean_dec(v___x_6880_);
v_traces_6882_ = lean_ctor_get(v_traceState_6881_, 0);
lean_inc_ref(v_traces_6882_);
lean_dec_ref(v_traceState_6881_);
v_ref_6883_ = l_Lean_replaceRef(v_ref_6857_, v_ref_6869_);
lean_inc_ref(v_inheritedTraceOptions_6879_);
lean_inc(v_cancelTk_x3f_6877_);
lean_inc(v_currMacroScope_6875_);
lean_inc(v_quotContext_6874_);
lean_inc(v_maxHeartbeats_6873_);
lean_inc(v_initHeartbeats_6872_);
lean_inc(v_openDecls_6871_);
lean_inc(v_currNamespace_6870_);
lean_inc(v_maxRecDepth_6868_);
lean_inc(v_currRecDepth_6867_);
lean_inc_ref(v_options_6866_);
lean_inc_ref(v_fileMap_6865_);
lean_inc_ref(v_fileName_6864_);
v___x_6884_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_6884_, 0, v_fileName_6864_);
lean_ctor_set(v___x_6884_, 1, v_fileMap_6865_);
lean_ctor_set(v___x_6884_, 2, v_options_6866_);
lean_ctor_set(v___x_6884_, 3, v_currRecDepth_6867_);
lean_ctor_set(v___x_6884_, 4, v_maxRecDepth_6868_);
lean_ctor_set(v___x_6884_, 5, v_ref_6883_);
lean_ctor_set(v___x_6884_, 6, v_currNamespace_6870_);
lean_ctor_set(v___x_6884_, 7, v_openDecls_6871_);
lean_ctor_set(v___x_6884_, 8, v_initHeartbeats_6872_);
lean_ctor_set(v___x_6884_, 9, v_maxHeartbeats_6873_);
lean_ctor_set(v___x_6884_, 10, v_quotContext_6874_);
lean_ctor_set(v___x_6884_, 11, v_currMacroScope_6875_);
lean_ctor_set(v___x_6884_, 12, v_cancelTk_x3f_6877_);
lean_ctor_set(v___x_6884_, 13, v_inheritedTraceOptions_6879_);
lean_ctor_set_uint8(v___x_6884_, sizeof(void*)*14, v_diag_6876_);
lean_ctor_set_uint8(v___x_6884_, sizeof(void*)*14 + 1, v_suppressElabErrors_6878_);
v___x_6885_ = l_Lean_PersistentArray_toArray___redArg(v_traces_6882_);
lean_dec_ref(v_traces_6882_);
v_sz_6886_ = lean_array_size(v___x_6885_);
v___x_6887_ = ((size_t)0ULL);
v___x_6888_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__3_spec__4(v_sz_6886_, v___x_6887_, v___x_6885_);
v_msg_6889_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_6889_, 0, v_data_6856_);
lean_ctor_set(v_msg_6889_, 1, v_msg_6858_);
lean_ctor_set(v_msg_6889_, 2, v___x_6888_);
v___x_6890_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0_spec__4(v_msg_6889_, v___y_6859_, v___y_6860_, v___x_6884_, v___y_6862_);
lean_dec_ref_known(v___x_6884_, 14);
v_a_6891_ = lean_ctor_get(v___x_6890_, 0);
v_isSharedCheck_6928_ = !lean_is_exclusive(v___x_6890_);
if (v_isSharedCheck_6928_ == 0)
{
v___x_6893_ = v___x_6890_;
v_isShared_6894_ = v_isSharedCheck_6928_;
goto v_resetjp_6892_;
}
else
{
lean_inc(v_a_6891_);
lean_dec(v___x_6890_);
v___x_6893_ = lean_box(0);
v_isShared_6894_ = v_isSharedCheck_6928_;
goto v_resetjp_6892_;
}
v_resetjp_6892_:
{
lean_object* v___x_6895_; lean_object* v_traceState_6896_; lean_object* v_env_6897_; lean_object* v_nextMacroScope_6898_; lean_object* v_ngen_6899_; lean_object* v_auxDeclNGen_6900_; lean_object* v_cache_6901_; lean_object* v_messages_6902_; lean_object* v_infoState_6903_; lean_object* v_snapshotTasks_6904_; lean_object* v___x_6906_; uint8_t v_isShared_6907_; uint8_t v_isSharedCheck_6927_; 
v___x_6895_ = lean_st_ref_take(v___y_6862_);
v_traceState_6896_ = lean_ctor_get(v___x_6895_, 4);
v_env_6897_ = lean_ctor_get(v___x_6895_, 0);
v_nextMacroScope_6898_ = lean_ctor_get(v___x_6895_, 1);
v_ngen_6899_ = lean_ctor_get(v___x_6895_, 2);
v_auxDeclNGen_6900_ = lean_ctor_get(v___x_6895_, 3);
v_cache_6901_ = lean_ctor_get(v___x_6895_, 5);
v_messages_6902_ = lean_ctor_get(v___x_6895_, 6);
v_infoState_6903_ = lean_ctor_get(v___x_6895_, 7);
v_snapshotTasks_6904_ = lean_ctor_get(v___x_6895_, 8);
v_isSharedCheck_6927_ = !lean_is_exclusive(v___x_6895_);
if (v_isSharedCheck_6927_ == 0)
{
v___x_6906_ = v___x_6895_;
v_isShared_6907_ = v_isSharedCheck_6927_;
goto v_resetjp_6905_;
}
else
{
lean_inc(v_snapshotTasks_6904_);
lean_inc(v_infoState_6903_);
lean_inc(v_messages_6902_);
lean_inc(v_cache_6901_);
lean_inc(v_traceState_6896_);
lean_inc(v_auxDeclNGen_6900_);
lean_inc(v_ngen_6899_);
lean_inc(v_nextMacroScope_6898_);
lean_inc(v_env_6897_);
lean_dec(v___x_6895_);
v___x_6906_ = lean_box(0);
v_isShared_6907_ = v_isSharedCheck_6927_;
goto v_resetjp_6905_;
}
v_resetjp_6905_:
{
uint64_t v_tid_6908_; lean_object* v___x_6910_; uint8_t v_isShared_6911_; uint8_t v_isSharedCheck_6925_; 
v_tid_6908_ = lean_ctor_get_uint64(v_traceState_6896_, sizeof(void*)*1);
v_isSharedCheck_6925_ = !lean_is_exclusive(v_traceState_6896_);
if (v_isSharedCheck_6925_ == 0)
{
lean_object* v_unused_6926_; 
v_unused_6926_ = lean_ctor_get(v_traceState_6896_, 0);
lean_dec(v_unused_6926_);
v___x_6910_ = v_traceState_6896_;
v_isShared_6911_ = v_isSharedCheck_6925_;
goto v_resetjp_6909_;
}
else
{
lean_dec(v_traceState_6896_);
v___x_6910_ = lean_box(0);
v_isShared_6911_ = v_isSharedCheck_6925_;
goto v_resetjp_6909_;
}
v_resetjp_6909_:
{
lean_object* v___x_6912_; lean_object* v___x_6913_; lean_object* v___x_6915_; 
v___x_6912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6912_, 0, v_ref_6857_);
lean_ctor_set(v___x_6912_, 1, v_a_6891_);
v___x_6913_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_6855_, v___x_6912_);
if (v_isShared_6911_ == 0)
{
lean_ctor_set(v___x_6910_, 0, v___x_6913_);
v___x_6915_ = v___x_6910_;
goto v_reusejp_6914_;
}
else
{
lean_object* v_reuseFailAlloc_6924_; 
v_reuseFailAlloc_6924_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6924_, 0, v___x_6913_);
lean_ctor_set_uint64(v_reuseFailAlloc_6924_, sizeof(void*)*1, v_tid_6908_);
v___x_6915_ = v_reuseFailAlloc_6924_;
goto v_reusejp_6914_;
}
v_reusejp_6914_:
{
lean_object* v___x_6917_; 
if (v_isShared_6907_ == 0)
{
lean_ctor_set(v___x_6906_, 4, v___x_6915_);
v___x_6917_ = v___x_6906_;
goto v_reusejp_6916_;
}
else
{
lean_object* v_reuseFailAlloc_6923_; 
v_reuseFailAlloc_6923_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6923_, 0, v_env_6897_);
lean_ctor_set(v_reuseFailAlloc_6923_, 1, v_nextMacroScope_6898_);
lean_ctor_set(v_reuseFailAlloc_6923_, 2, v_ngen_6899_);
lean_ctor_set(v_reuseFailAlloc_6923_, 3, v_auxDeclNGen_6900_);
lean_ctor_set(v_reuseFailAlloc_6923_, 4, v___x_6915_);
lean_ctor_set(v_reuseFailAlloc_6923_, 5, v_cache_6901_);
lean_ctor_set(v_reuseFailAlloc_6923_, 6, v_messages_6902_);
lean_ctor_set(v_reuseFailAlloc_6923_, 7, v_infoState_6903_);
lean_ctor_set(v_reuseFailAlloc_6923_, 8, v_snapshotTasks_6904_);
v___x_6917_ = v_reuseFailAlloc_6923_;
goto v_reusejp_6916_;
}
v_reusejp_6916_:
{
lean_object* v___x_6918_; lean_object* v___x_6919_; lean_object* v___x_6921_; 
v___x_6918_ = lean_st_ref_put(v___y_6862_, v___x_6917_);
v___x_6919_ = lean_box(0);
if (v_isShared_6894_ == 0)
{
lean_ctor_set(v___x_6893_, 0, v___x_6919_);
v___x_6921_ = v___x_6893_;
goto v_reusejp_6920_;
}
else
{
lean_object* v_reuseFailAlloc_6922_; 
v_reuseFailAlloc_6922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6922_, 0, v___x_6919_);
v___x_6921_ = v_reuseFailAlloc_6922_;
goto v_reusejp_6920_;
}
v_reusejp_6920_:
{
return v___x_6921_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__3___boxed(lean_object* v_oldTraces_6929_, lean_object* v_data_6930_, lean_object* v_ref_6931_, lean_object* v_msg_6932_, lean_object* v___y_6933_, lean_object* v___y_6934_, lean_object* v___y_6935_, lean_object* v___y_6936_, lean_object* v___y_6937_){
_start:
{
lean_object* v_res_6938_; 
v_res_6938_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__3(v_oldTraces_6929_, v_data_6930_, v_ref_6931_, v_msg_6932_, v___y_6933_, v___y_6934_, v___y_6935_, v___y_6936_);
lean_dec(v___y_6936_);
lean_dec_ref(v___y_6935_);
lean_dec(v___y_6934_);
lean_dec_ref(v___y_6933_);
return v_res_6938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__6(lean_object* v_opts_6939_, lean_object* v_opt_6940_){
_start:
{
lean_object* v_name_6941_; lean_object* v_defValue_6942_; lean_object* v_map_6943_; lean_object* v___x_6944_; 
v_name_6941_ = lean_ctor_get(v_opt_6940_, 0);
v_defValue_6942_ = lean_ctor_get(v_opt_6940_, 1);
v_map_6943_ = lean_ctor_get(v_opts_6939_, 0);
v___x_6944_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6943_, v_name_6941_);
if (lean_obj_tag(v___x_6944_) == 0)
{
lean_inc(v_defValue_6942_);
return v_defValue_6942_;
}
else
{
lean_object* v_val_6945_; 
v_val_6945_ = lean_ctor_get(v___x_6944_, 0);
lean_inc(v_val_6945_);
lean_dec_ref_known(v___x_6944_, 1);
if (lean_obj_tag(v_val_6945_) == 3)
{
lean_object* v_v_6946_; 
v_v_6946_ = lean_ctor_get(v_val_6945_, 0);
lean_inc(v_v_6946_);
lean_dec_ref_known(v_val_6945_, 1);
return v_v_6946_;
}
else
{
lean_dec(v_val_6945_);
lean_inc(v_defValue_6942_);
return v_defValue_6942_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__6___boxed(lean_object* v_opts_6947_, lean_object* v_opt_6948_){
_start:
{
lean_object* v_res_6949_; 
v_res_6949_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__6(v_opts_6947_, v_opt_6948_);
lean_dec_ref(v_opt_6948_);
lean_dec_ref(v_opts_6947_);
return v_res_6949_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__1(void){
_start:
{
lean_object* v___x_6951_; lean_object* v___x_6952_; 
v___x_6951_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__0));
v___x_6952_ = l_Lean_stringToMessageData(v___x_6951_);
return v___x_6952_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__2(void){
_start:
{
lean_object* v___x_6953_; double v___x_6954_; 
v___x_6953_ = lean_unsigned_to_nat(1000u);
v___x_6954_ = lean_float_of_nat(v___x_6953_);
return v___x_6954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2(lean_object* v_cls_6955_, uint8_t v_collapsed_6956_, lean_object* v_tag_6957_, lean_object* v_opts_6958_, uint8_t v_clsEnabled_6959_, lean_object* v_oldTraces_6960_, lean_object* v_msg_6961_, lean_object* v_resStartStop_6962_, lean_object* v___y_6963_, lean_object* v___y_6964_, lean_object* v___y_6965_, lean_object* v___y_6966_){
_start:
{
lean_object* v_fst_6968_; lean_object* v_snd_6969_; lean_object* v___y_6971_; lean_object* v___y_6972_; lean_object* v_data_6973_; lean_object* v_fst_6976_; lean_object* v_snd_6977_; lean_object* v___x_6978_; uint8_t v___x_6979_; lean_object* v___y_6981_; lean_object* v_a_6982_; uint8_t v___y_6997_; double v___y_7028_; 
v_fst_6968_ = lean_ctor_get(v_resStartStop_6962_, 0);
lean_inc(v_fst_6968_);
v_snd_6969_ = lean_ctor_get(v_resStartStop_6962_, 1);
lean_inc(v_snd_6969_);
lean_dec_ref(v_resStartStop_6962_);
v_fst_6976_ = lean_ctor_get(v_snd_6969_, 0);
lean_inc(v_fst_6976_);
v_snd_6977_ = lean_ctor_get(v_snd_6969_, 1);
lean_inc(v_snd_6977_);
lean_dec(v_snd_6969_);
v___x_6978_ = l_Lean_trace_profiler;
v___x_6979_ = l_Lean_Option_get___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__0(v_opts_6958_, v___x_6978_);
if (v___x_6979_ == 0)
{
v___y_6997_ = v___x_6979_;
goto v___jp_6996_;
}
else
{
lean_object* v___x_7033_; uint8_t v___x_7034_; 
v___x_7033_ = l_Lean_trace_profiler_useHeartbeats;
v___x_7034_ = l_Lean_Option_get___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__0(v_opts_6958_, v___x_7033_);
if (v___x_7034_ == 0)
{
lean_object* v___x_7035_; lean_object* v___x_7036_; double v___x_7037_; double v___x_7038_; double v___x_7039_; 
v___x_7035_ = l_Lean_trace_profiler_threshold;
v___x_7036_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__6(v_opts_6958_, v___x_7035_);
v___x_7037_ = lean_float_of_nat(v___x_7036_);
v___x_7038_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__2);
v___x_7039_ = lean_float_div(v___x_7037_, v___x_7038_);
v___y_7028_ = v___x_7039_;
goto v___jp_7027_;
}
else
{
lean_object* v___x_7040_; lean_object* v___x_7041_; double v___x_7042_; 
v___x_7040_ = l_Lean_trace_profiler_threshold;
v___x_7041_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__6(v_opts_6958_, v___x_7040_);
v___x_7042_ = lean_float_of_nat(v___x_7041_);
v___y_7028_ = v___x_7042_;
goto v___jp_7027_;
}
}
v___jp_6970_:
{
lean_object* v___x_6974_; 
lean_inc(v___y_6972_);
v___x_6974_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__3(v_oldTraces_6960_, v_data_6973_, v___y_6972_, v___y_6971_, v___y_6963_, v___y_6964_, v___y_6965_, v___y_6966_);
if (lean_obj_tag(v___x_6974_) == 0)
{
lean_object* v___x_6975_; 
lean_dec_ref_known(v___x_6974_, 1);
v___x_6975_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__4___redArg(v_fst_6968_);
return v___x_6975_;
}
else
{
lean_dec(v_fst_6968_);
return v___x_6974_;
}
}
v___jp_6980_:
{
uint8_t v_result_6983_; lean_object* v___x_6984_; lean_object* v___x_6985_; double v___x_6986_; lean_object* v_data_6987_; 
v_result_6983_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__5(v_fst_6968_);
v___x_6984_ = lean_box(v_result_6983_);
v___x_6985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6985_, 0, v___x_6984_);
v___x_6986_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__0);
lean_inc_ref(v_tag_6957_);
lean_inc_ref(v___x_6985_);
lean_inc(v_cls_6955_);
v_data_6987_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6987_, 0, v_cls_6955_);
lean_ctor_set(v_data_6987_, 1, v___x_6985_);
lean_ctor_set(v_data_6987_, 2, v_tag_6957_);
lean_ctor_set_float(v_data_6987_, sizeof(void*)*3, v___x_6986_);
lean_ctor_set_float(v_data_6987_, sizeof(void*)*3 + 8, v___x_6986_);
lean_ctor_set_uint8(v_data_6987_, sizeof(void*)*3 + 16, v_collapsed_6956_);
if (v___x_6979_ == 0)
{
lean_dec_ref_known(v___x_6985_, 1);
lean_dec(v_snd_6977_);
lean_dec(v_fst_6976_);
lean_dec_ref(v_tag_6957_);
lean_dec(v_cls_6955_);
v___y_6971_ = v_a_6982_;
v___y_6972_ = v___y_6981_;
v_data_6973_ = v_data_6987_;
goto v___jp_6970_;
}
else
{
lean_object* v_data_6988_; double v___x_6989_; double v___x_6990_; 
lean_dec_ref_known(v_data_6987_, 3);
v_data_6988_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6988_, 0, v_cls_6955_);
lean_ctor_set(v_data_6988_, 1, v___x_6985_);
lean_ctor_set(v_data_6988_, 2, v_tag_6957_);
v___x_6989_ = lean_unbox_float(v_fst_6976_);
lean_dec(v_fst_6976_);
lean_ctor_set_float(v_data_6988_, sizeof(void*)*3, v___x_6989_);
v___x_6990_ = lean_unbox_float(v_snd_6977_);
lean_dec(v_snd_6977_);
lean_ctor_set_float(v_data_6988_, sizeof(void*)*3 + 8, v___x_6990_);
lean_ctor_set_uint8(v_data_6988_, sizeof(void*)*3 + 16, v_collapsed_6956_);
v___y_6971_ = v_a_6982_;
v___y_6972_ = v___y_6981_;
v_data_6973_ = v_data_6988_;
goto v___jp_6970_;
}
}
v___jp_6991_:
{
lean_object* v_ref_6992_; lean_object* v___x_6993_; 
v_ref_6992_ = lean_ctor_get(v___y_6965_, 5);
lean_inc(v___y_6966_);
lean_inc_ref(v___y_6965_);
lean_inc(v___y_6964_);
lean_inc_ref(v___y_6963_);
lean_inc(v_fst_6968_);
v___x_6993_ = lean_apply_6(v_msg_6961_, v_fst_6968_, v___y_6963_, v___y_6964_, v___y_6965_, v___y_6966_, lean_box(0));
if (lean_obj_tag(v___x_6993_) == 0)
{
lean_object* v_a_6994_; 
v_a_6994_ = lean_ctor_get(v___x_6993_, 0);
lean_inc(v_a_6994_);
lean_dec_ref_known(v___x_6993_, 1);
v___y_6981_ = v_ref_6992_;
v_a_6982_ = v_a_6994_;
goto v___jp_6980_;
}
else
{
lean_object* v___x_6995_; 
lean_dec_ref_known(v___x_6993_, 1);
v___x_6995_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__1);
v___y_6981_ = v_ref_6992_;
v_a_6982_ = v___x_6995_;
goto v___jp_6980_;
}
}
v___jp_6996_:
{
if (v_clsEnabled_6959_ == 0)
{
if (v___y_6997_ == 0)
{
lean_object* v___x_6998_; lean_object* v_traceState_6999_; lean_object* v_env_7000_; lean_object* v_nextMacroScope_7001_; lean_object* v_ngen_7002_; lean_object* v_auxDeclNGen_7003_; lean_object* v_cache_7004_; lean_object* v_messages_7005_; lean_object* v_infoState_7006_; lean_object* v_snapshotTasks_7007_; lean_object* v___x_7009_; uint8_t v_isShared_7010_; uint8_t v_isSharedCheck_7026_; 
lean_dec(v_snd_6977_);
lean_dec(v_fst_6976_);
lean_dec_ref(v_msg_6961_);
lean_dec_ref(v_tag_6957_);
lean_dec(v_cls_6955_);
v___x_6998_ = lean_st_ref_take(v___y_6966_);
v_traceState_6999_ = lean_ctor_get(v___x_6998_, 4);
v_env_7000_ = lean_ctor_get(v___x_6998_, 0);
v_nextMacroScope_7001_ = lean_ctor_get(v___x_6998_, 1);
v_ngen_7002_ = lean_ctor_get(v___x_6998_, 2);
v_auxDeclNGen_7003_ = lean_ctor_get(v___x_6998_, 3);
v_cache_7004_ = lean_ctor_get(v___x_6998_, 5);
v_messages_7005_ = lean_ctor_get(v___x_6998_, 6);
v_infoState_7006_ = lean_ctor_get(v___x_6998_, 7);
v_snapshotTasks_7007_ = lean_ctor_get(v___x_6998_, 8);
v_isSharedCheck_7026_ = !lean_is_exclusive(v___x_6998_);
if (v_isSharedCheck_7026_ == 0)
{
v___x_7009_ = v___x_6998_;
v_isShared_7010_ = v_isSharedCheck_7026_;
goto v_resetjp_7008_;
}
else
{
lean_inc(v_snapshotTasks_7007_);
lean_inc(v_infoState_7006_);
lean_inc(v_messages_7005_);
lean_inc(v_cache_7004_);
lean_inc(v_traceState_6999_);
lean_inc(v_auxDeclNGen_7003_);
lean_inc(v_ngen_7002_);
lean_inc(v_nextMacroScope_7001_);
lean_inc(v_env_7000_);
lean_dec(v___x_6998_);
v___x_7009_ = lean_box(0);
v_isShared_7010_ = v_isSharedCheck_7026_;
goto v_resetjp_7008_;
}
v_resetjp_7008_:
{
uint64_t v_tid_7011_; lean_object* v_traces_7012_; lean_object* v___x_7014_; uint8_t v_isShared_7015_; uint8_t v_isSharedCheck_7025_; 
v_tid_7011_ = lean_ctor_get_uint64(v_traceState_6999_, sizeof(void*)*1);
v_traces_7012_ = lean_ctor_get(v_traceState_6999_, 0);
v_isSharedCheck_7025_ = !lean_is_exclusive(v_traceState_6999_);
if (v_isSharedCheck_7025_ == 0)
{
v___x_7014_ = v_traceState_6999_;
v_isShared_7015_ = v_isSharedCheck_7025_;
goto v_resetjp_7013_;
}
else
{
lean_inc(v_traces_7012_);
lean_dec(v_traceState_6999_);
v___x_7014_ = lean_box(0);
v_isShared_7015_ = v_isSharedCheck_7025_;
goto v_resetjp_7013_;
}
v_resetjp_7013_:
{
lean_object* v___x_7016_; lean_object* v___x_7018_; 
v___x_7016_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_6960_, v_traces_7012_);
lean_dec_ref(v_traces_7012_);
if (v_isShared_7015_ == 0)
{
lean_ctor_set(v___x_7014_, 0, v___x_7016_);
v___x_7018_ = v___x_7014_;
goto v_reusejp_7017_;
}
else
{
lean_object* v_reuseFailAlloc_7024_; 
v_reuseFailAlloc_7024_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_7024_, 0, v___x_7016_);
lean_ctor_set_uint64(v_reuseFailAlloc_7024_, sizeof(void*)*1, v_tid_7011_);
v___x_7018_ = v_reuseFailAlloc_7024_;
goto v_reusejp_7017_;
}
v_reusejp_7017_:
{
lean_object* v___x_7020_; 
if (v_isShared_7010_ == 0)
{
lean_ctor_set(v___x_7009_, 4, v___x_7018_);
v___x_7020_ = v___x_7009_;
goto v_reusejp_7019_;
}
else
{
lean_object* v_reuseFailAlloc_7023_; 
v_reuseFailAlloc_7023_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_7023_, 0, v_env_7000_);
lean_ctor_set(v_reuseFailAlloc_7023_, 1, v_nextMacroScope_7001_);
lean_ctor_set(v_reuseFailAlloc_7023_, 2, v_ngen_7002_);
lean_ctor_set(v_reuseFailAlloc_7023_, 3, v_auxDeclNGen_7003_);
lean_ctor_set(v_reuseFailAlloc_7023_, 4, v___x_7018_);
lean_ctor_set(v_reuseFailAlloc_7023_, 5, v_cache_7004_);
lean_ctor_set(v_reuseFailAlloc_7023_, 6, v_messages_7005_);
lean_ctor_set(v_reuseFailAlloc_7023_, 7, v_infoState_7006_);
lean_ctor_set(v_reuseFailAlloc_7023_, 8, v_snapshotTasks_7007_);
v___x_7020_ = v_reuseFailAlloc_7023_;
goto v_reusejp_7019_;
}
v_reusejp_7019_:
{
lean_object* v___x_7021_; lean_object* v___x_7022_; 
v___x_7021_ = lean_st_ref_put(v___y_6966_, v___x_7020_);
v___x_7022_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__4___redArg(v_fst_6968_);
return v___x_7022_;
}
}
}
}
}
else
{
goto v___jp_6991_;
}
}
else
{
goto v___jp_6991_;
}
}
v___jp_7027_:
{
double v___x_7029_; double v___x_7030_; double v___x_7031_; uint8_t v___x_7032_; 
v___x_7029_ = lean_unbox_float(v_snd_6977_);
v___x_7030_ = lean_unbox_float(v_fst_6976_);
v___x_7031_ = lean_float_sub(v___x_7029_, v___x_7030_);
v___x_7032_ = lean_float_decLt(v___y_7028_, v___x_7031_);
v___y_6997_ = v___x_7032_;
goto v___jp_6996_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___boxed(lean_object* v_cls_7043_, lean_object* v_collapsed_7044_, lean_object* v_tag_7045_, lean_object* v_opts_7046_, lean_object* v_clsEnabled_7047_, lean_object* v_oldTraces_7048_, lean_object* v_msg_7049_, lean_object* v_resStartStop_7050_, lean_object* v___y_7051_, lean_object* v___y_7052_, lean_object* v___y_7053_, lean_object* v___y_7054_, lean_object* v___y_7055_){
_start:
{
uint8_t v_collapsed_boxed_7056_; uint8_t v_clsEnabled_boxed_7057_; lean_object* v_res_7058_; 
v_collapsed_boxed_7056_ = lean_unbox(v_collapsed_7044_);
v_clsEnabled_boxed_7057_ = lean_unbox(v_clsEnabled_7047_);
v_res_7058_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2(v_cls_7043_, v_collapsed_boxed_7056_, v_tag_7045_, v_opts_7046_, v_clsEnabled_boxed_7057_, v_oldTraces_7048_, v_msg_7049_, v_resStartStop_7050_, v___y_7051_, v___y_7052_, v___y_7053_, v___y_7054_);
lean_dec(v___y_7054_);
lean_dec_ref(v___y_7053_);
lean_dec(v___y_7052_);
lean_dec_ref(v___y_7051_);
lean_dec_ref(v_opts_7046_);
return v_res_7058_;
}
}
static double _init_l_Lean_mkNoConfusion___closed__0(void){
_start:
{
lean_object* v___x_7059_; double v___x_7060_; 
v___x_7059_ = lean_unsigned_to_nat(1000000000u);
v___x_7060_ = lean_float_of_nat(v___x_7059_);
return v___x_7060_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNoConfusion(lean_object* v_declName_7061_, lean_object* v_a_7062_, lean_object* v_a_7063_, lean_object* v_a_7064_, lean_object* v_a_7065_){
_start:
{
lean_object* v_options_7067_; uint8_t v_hasTrace_7068_; 
v_options_7067_ = lean_ctor_get(v_a_7064_, 2);
v_hasTrace_7068_ = lean_ctor_get_uint8(v_options_7067_, sizeof(void*)*1);
if (v_hasTrace_7068_ == 0)
{
lean_object* v___x_7069_; 
lean_inc(v_declName_7061_);
v___x_7069_ = l_Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0(v_declName_7061_, v_a_7062_, v_a_7063_, v_a_7064_, v_a_7065_);
if (lean_obj_tag(v___x_7069_) == 0)
{
lean_object* v_a_7070_; uint8_t v___x_7071_; 
v_a_7070_ = lean_ctor_get(v___x_7069_, 0);
lean_inc(v_a_7070_);
lean_dec_ref_known(v___x_7069_, 1);
v___x_7071_ = lean_unbox(v_a_7070_);
lean_dec(v_a_7070_);
if (v___x_7071_ == 0)
{
lean_object* v___x_7072_; 
v___x_7072_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCore(v_declName_7061_, v_a_7062_, v_a_7063_, v_a_7064_, v_a_7065_);
return v___x_7072_;
}
else
{
lean_object* v___x_7073_; 
v___x_7073_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum(v_declName_7061_, v_a_7062_, v_a_7063_, v_a_7064_, v_a_7065_);
return v___x_7073_;
}
}
else
{
lean_object* v_a_7074_; lean_object* v___x_7076_; uint8_t v_isShared_7077_; uint8_t v_isSharedCheck_7081_; 
lean_dec(v_declName_7061_);
v_a_7074_ = lean_ctor_get(v___x_7069_, 0);
v_isSharedCheck_7081_ = !lean_is_exclusive(v___x_7069_);
if (v_isSharedCheck_7081_ == 0)
{
v___x_7076_ = v___x_7069_;
v_isShared_7077_ = v_isSharedCheck_7081_;
goto v_resetjp_7075_;
}
else
{
lean_inc(v_a_7074_);
lean_dec(v___x_7069_);
v___x_7076_ = lean_box(0);
v_isShared_7077_ = v_isSharedCheck_7081_;
goto v_resetjp_7075_;
}
v_resetjp_7075_:
{
lean_object* v___x_7079_; 
if (v_isShared_7077_ == 0)
{
v___x_7079_ = v___x_7076_;
goto v_reusejp_7078_;
}
else
{
lean_object* v_reuseFailAlloc_7080_; 
v_reuseFailAlloc_7080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7080_, 0, v_a_7074_);
v___x_7079_ = v_reuseFailAlloc_7080_;
goto v_reusejp_7078_;
}
v_reusejp_7078_:
{
return v___x_7079_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_7082_; lean_object* v___f_7083_; lean_object* v___x_7084_; lean_object* v___x_7085_; lean_object* v___x_7086_; uint8_t v___x_7087_; lean_object* v___y_7089_; lean_object* v___y_7090_; lean_object* v_a_7091_; lean_object* v___y_7104_; lean_object* v___y_7105_; lean_object* v_a_7106_; lean_object* v___y_7109_; lean_object* v___y_7110_; lean_object* v___y_7111_; lean_object* v___y_7122_; lean_object* v___y_7123_; lean_object* v_a_7124_; lean_object* v___y_7134_; lean_object* v___y_7135_; lean_object* v_a_7136_; lean_object* v___y_7139_; lean_object* v___y_7140_; lean_object* v___y_7141_; 
v_inheritedTraceOptions_7082_ = lean_ctor_get(v_a_7064_, 13);
lean_inc(v_declName_7061_);
v___f_7083_ = lean_alloc_closure((void*)(l_Lean_mkNoConfusion___lam__0___boxed), 7, 1);
lean_closure_set(v___f_7083_, 0, v_declName_7061_);
v___x_7084_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___closed__1));
v___x_7085_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__1));
v___x_7086_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__2, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__2_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__2);
v___x_7087_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_7082_, v_options_7067_, v___x_7086_);
if (v___x_7087_ == 0)
{
lean_object* v___x_7170_; uint8_t v___x_7171_; 
v___x_7170_ = l_Lean_trace_profiler;
v___x_7171_ = l_Lean_Option_get___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__0(v_options_7067_, v___x_7170_);
if (v___x_7171_ == 0)
{
lean_object* v___x_7172_; 
lean_dec_ref(v___f_7083_);
lean_inc(v_declName_7061_);
v___x_7172_ = l_Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0(v_declName_7061_, v_a_7062_, v_a_7063_, v_a_7064_, v_a_7065_);
if (lean_obj_tag(v___x_7172_) == 0)
{
lean_object* v_a_7173_; uint8_t v___x_7174_; 
v_a_7173_ = lean_ctor_get(v___x_7172_, 0);
lean_inc(v_a_7173_);
lean_dec_ref_known(v___x_7172_, 1);
v___x_7174_ = lean_unbox(v_a_7173_);
lean_dec(v_a_7173_);
if (v___x_7174_ == 0)
{
lean_object* v___x_7175_; 
v___x_7175_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCore(v_declName_7061_, v_a_7062_, v_a_7063_, v_a_7064_, v_a_7065_);
return v___x_7175_;
}
else
{
lean_object* v___x_7176_; 
v___x_7176_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum(v_declName_7061_, v_a_7062_, v_a_7063_, v_a_7064_, v_a_7065_);
return v___x_7176_;
}
}
else
{
lean_object* v_a_7177_; lean_object* v___x_7179_; uint8_t v_isShared_7180_; uint8_t v_isSharedCheck_7184_; 
lean_dec(v_declName_7061_);
v_a_7177_ = lean_ctor_get(v___x_7172_, 0);
v_isSharedCheck_7184_ = !lean_is_exclusive(v___x_7172_);
if (v_isSharedCheck_7184_ == 0)
{
v___x_7179_ = v___x_7172_;
v_isShared_7180_ = v_isSharedCheck_7184_;
goto v_resetjp_7178_;
}
else
{
lean_inc(v_a_7177_);
lean_dec(v___x_7172_);
v___x_7179_ = lean_box(0);
v_isShared_7180_ = v_isSharedCheck_7184_;
goto v_resetjp_7178_;
}
v_resetjp_7178_:
{
lean_object* v___x_7182_; 
if (v_isShared_7180_ == 0)
{
v___x_7182_ = v___x_7179_;
goto v_reusejp_7181_;
}
else
{
lean_object* v_reuseFailAlloc_7183_; 
v_reuseFailAlloc_7183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7183_, 0, v_a_7177_);
v___x_7182_ = v_reuseFailAlloc_7183_;
goto v_reusejp_7181_;
}
v_reusejp_7181_:
{
return v___x_7182_;
}
}
}
}
else
{
goto v___jp_7151_;
}
}
else
{
goto v___jp_7151_;
}
v___jp_7088_:
{
lean_object* v___x_7092_; double v___x_7093_; double v___x_7094_; double v___x_7095_; double v___x_7096_; double v___x_7097_; lean_object* v___x_7098_; lean_object* v___x_7099_; lean_object* v___x_7100_; lean_object* v___x_7101_; lean_object* v___x_7102_; 
v___x_7092_ = lean_io_mono_nanos_now();
v___x_7093_ = lean_float_of_nat(v___y_7089_);
v___x_7094_ = lean_float_once(&l_Lean_mkNoConfusion___closed__0, &l_Lean_mkNoConfusion___closed__0_once, _init_l_Lean_mkNoConfusion___closed__0);
v___x_7095_ = lean_float_div(v___x_7093_, v___x_7094_);
v___x_7096_ = lean_float_of_nat(v___x_7092_);
v___x_7097_ = lean_float_div(v___x_7096_, v___x_7094_);
v___x_7098_ = lean_box_float(v___x_7095_);
v___x_7099_ = lean_box_float(v___x_7097_);
v___x_7100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7100_, 0, v___x_7098_);
lean_ctor_set(v___x_7100_, 1, v___x_7099_);
v___x_7101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7101_, 0, v_a_7091_);
lean_ctor_set(v___x_7101_, 1, v___x_7100_);
v___x_7102_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2(v___x_7084_, v_hasTrace_7068_, v___x_7085_, v_options_7067_, v___x_7087_, v___y_7090_, v___f_7083_, v___x_7101_, v_a_7062_, v_a_7063_, v_a_7064_, v_a_7065_);
return v___x_7102_;
}
v___jp_7103_:
{
lean_object* v___x_7107_; 
v___x_7107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7107_, 0, v_a_7106_);
v___y_7089_ = v___y_7104_;
v___y_7090_ = v___y_7105_;
v_a_7091_ = v___x_7107_;
goto v___jp_7088_;
}
v___jp_7108_:
{
if (lean_obj_tag(v___y_7111_) == 0)
{
lean_object* v_a_7112_; lean_object* v___x_7114_; uint8_t v_isShared_7115_; uint8_t v_isSharedCheck_7119_; 
v_a_7112_ = lean_ctor_get(v___y_7111_, 0);
v_isSharedCheck_7119_ = !lean_is_exclusive(v___y_7111_);
if (v_isSharedCheck_7119_ == 0)
{
v___x_7114_ = v___y_7111_;
v_isShared_7115_ = v_isSharedCheck_7119_;
goto v_resetjp_7113_;
}
else
{
lean_inc(v_a_7112_);
lean_dec(v___y_7111_);
v___x_7114_ = lean_box(0);
v_isShared_7115_ = v_isSharedCheck_7119_;
goto v_resetjp_7113_;
}
v_resetjp_7113_:
{
lean_object* v___x_7117_; 
if (v_isShared_7115_ == 0)
{
lean_ctor_set_tag(v___x_7114_, 1);
v___x_7117_ = v___x_7114_;
goto v_reusejp_7116_;
}
else
{
lean_object* v_reuseFailAlloc_7118_; 
v_reuseFailAlloc_7118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7118_, 0, v_a_7112_);
v___x_7117_ = v_reuseFailAlloc_7118_;
goto v_reusejp_7116_;
}
v_reusejp_7116_:
{
v___y_7089_ = v___y_7109_;
v___y_7090_ = v___y_7110_;
v_a_7091_ = v___x_7117_;
goto v___jp_7088_;
}
}
}
else
{
lean_object* v_a_7120_; 
v_a_7120_ = lean_ctor_get(v___y_7111_, 0);
lean_inc(v_a_7120_);
lean_dec_ref_known(v___y_7111_, 1);
v___y_7104_ = v___y_7109_;
v___y_7105_ = v___y_7110_;
v_a_7106_ = v_a_7120_;
goto v___jp_7103_;
}
}
v___jp_7121_:
{
lean_object* v___x_7125_; double v___x_7126_; double v___x_7127_; lean_object* v___x_7128_; lean_object* v___x_7129_; lean_object* v___x_7130_; lean_object* v___x_7131_; lean_object* v___x_7132_; 
v___x_7125_ = lean_io_get_num_heartbeats();
v___x_7126_ = lean_float_of_nat(v___y_7122_);
v___x_7127_ = lean_float_of_nat(v___x_7125_);
v___x_7128_ = lean_box_float(v___x_7126_);
v___x_7129_ = lean_box_float(v___x_7127_);
v___x_7130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7130_, 0, v___x_7128_);
lean_ctor_set(v___x_7130_, 1, v___x_7129_);
v___x_7131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7131_, 0, v_a_7124_);
lean_ctor_set(v___x_7131_, 1, v___x_7130_);
v___x_7132_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2(v___x_7084_, v_hasTrace_7068_, v___x_7085_, v_options_7067_, v___x_7087_, v___y_7123_, v___f_7083_, v___x_7131_, v_a_7062_, v_a_7063_, v_a_7064_, v_a_7065_);
return v___x_7132_;
}
v___jp_7133_:
{
lean_object* v___x_7137_; 
v___x_7137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7137_, 0, v_a_7136_);
v___y_7122_ = v___y_7134_;
v___y_7123_ = v___y_7135_;
v_a_7124_ = v___x_7137_;
goto v___jp_7121_;
}
v___jp_7138_:
{
if (lean_obj_tag(v___y_7141_) == 0)
{
lean_object* v_a_7142_; lean_object* v___x_7144_; uint8_t v_isShared_7145_; uint8_t v_isSharedCheck_7149_; 
v_a_7142_ = lean_ctor_get(v___y_7141_, 0);
v_isSharedCheck_7149_ = !lean_is_exclusive(v___y_7141_);
if (v_isSharedCheck_7149_ == 0)
{
v___x_7144_ = v___y_7141_;
v_isShared_7145_ = v_isSharedCheck_7149_;
goto v_resetjp_7143_;
}
else
{
lean_inc(v_a_7142_);
lean_dec(v___y_7141_);
v___x_7144_ = lean_box(0);
v_isShared_7145_ = v_isSharedCheck_7149_;
goto v_resetjp_7143_;
}
v_resetjp_7143_:
{
lean_object* v___x_7147_; 
if (v_isShared_7145_ == 0)
{
lean_ctor_set_tag(v___x_7144_, 1);
v___x_7147_ = v___x_7144_;
goto v_reusejp_7146_;
}
else
{
lean_object* v_reuseFailAlloc_7148_; 
v_reuseFailAlloc_7148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7148_, 0, v_a_7142_);
v___x_7147_ = v_reuseFailAlloc_7148_;
goto v_reusejp_7146_;
}
v_reusejp_7146_:
{
v___y_7122_ = v___y_7139_;
v___y_7123_ = v___y_7140_;
v_a_7124_ = v___x_7147_;
goto v___jp_7121_;
}
}
}
else
{
lean_object* v_a_7150_; 
v_a_7150_ = lean_ctor_get(v___y_7141_, 0);
lean_inc(v_a_7150_);
lean_dec_ref_known(v___y_7141_, 1);
v___y_7134_ = v___y_7139_;
v___y_7135_ = v___y_7140_;
v_a_7136_ = v_a_7150_;
goto v___jp_7133_;
}
}
v___jp_7151_:
{
lean_object* v___x_7152_; lean_object* v_a_7153_; lean_object* v___x_7154_; uint8_t v___x_7155_; 
v___x_7152_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg(v_a_7065_);
v_a_7153_ = lean_ctor_get(v___x_7152_, 0);
lean_inc(v_a_7153_);
lean_dec_ref(v___x_7152_);
v___x_7154_ = l_Lean_trace_profiler_useHeartbeats;
v___x_7155_ = l_Lean_Option_get___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__0(v_options_7067_, v___x_7154_);
if (v___x_7155_ == 0)
{
lean_object* v___x_7156_; lean_object* v___x_7157_; 
v___x_7156_ = lean_io_mono_nanos_now();
lean_inc(v_declName_7061_);
v___x_7157_ = l_Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0(v_declName_7061_, v_a_7062_, v_a_7063_, v_a_7064_, v_a_7065_);
if (lean_obj_tag(v___x_7157_) == 0)
{
lean_object* v_a_7158_; uint8_t v___x_7159_; 
v_a_7158_ = lean_ctor_get(v___x_7157_, 0);
lean_inc(v_a_7158_);
lean_dec_ref_known(v___x_7157_, 1);
v___x_7159_ = lean_unbox(v_a_7158_);
lean_dec(v_a_7158_);
if (v___x_7159_ == 0)
{
lean_object* v___x_7160_; 
v___x_7160_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCore(v_declName_7061_, v_a_7062_, v_a_7063_, v_a_7064_, v_a_7065_);
v___y_7109_ = v___x_7156_;
v___y_7110_ = v_a_7153_;
v___y_7111_ = v___x_7160_;
goto v___jp_7108_;
}
else
{
lean_object* v___x_7161_; 
v___x_7161_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum(v_declName_7061_, v_a_7062_, v_a_7063_, v_a_7064_, v_a_7065_);
v___y_7109_ = v___x_7156_;
v___y_7110_ = v_a_7153_;
v___y_7111_ = v___x_7161_;
goto v___jp_7108_;
}
}
else
{
lean_object* v_a_7162_; 
lean_dec(v_declName_7061_);
v_a_7162_ = lean_ctor_get(v___x_7157_, 0);
lean_inc(v_a_7162_);
lean_dec_ref_known(v___x_7157_, 1);
v___y_7104_ = v___x_7156_;
v___y_7105_ = v_a_7153_;
v_a_7106_ = v_a_7162_;
goto v___jp_7103_;
}
}
else
{
lean_object* v___x_7163_; lean_object* v___x_7164_; 
v___x_7163_ = lean_io_get_num_heartbeats();
lean_inc(v_declName_7061_);
v___x_7164_ = l_Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0(v_declName_7061_, v_a_7062_, v_a_7063_, v_a_7064_, v_a_7065_);
if (lean_obj_tag(v___x_7164_) == 0)
{
lean_object* v_a_7165_; uint8_t v___x_7166_; 
v_a_7165_ = lean_ctor_get(v___x_7164_, 0);
lean_inc(v_a_7165_);
lean_dec_ref_known(v___x_7164_, 1);
v___x_7166_ = lean_unbox(v_a_7165_);
lean_dec(v_a_7165_);
if (v___x_7166_ == 0)
{
lean_object* v___x_7167_; 
v___x_7167_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCore(v_declName_7061_, v_a_7062_, v_a_7063_, v_a_7064_, v_a_7065_);
v___y_7139_ = v___x_7163_;
v___y_7140_ = v_a_7153_;
v___y_7141_ = v___x_7167_;
goto v___jp_7138_;
}
else
{
lean_object* v___x_7168_; 
v___x_7168_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum(v_declName_7061_, v_a_7062_, v_a_7063_, v_a_7064_, v_a_7065_);
v___y_7139_ = v___x_7163_;
v___y_7140_ = v_a_7153_;
v___y_7141_ = v___x_7168_;
goto v___jp_7138_;
}
}
else
{
lean_object* v_a_7169_; 
lean_dec(v_declName_7061_);
v_a_7169_ = lean_ctor_get(v___x_7164_, 0);
lean_inc(v_a_7169_);
lean_dec_ref_known(v___x_7164_, 1);
v___y_7134_ = v___x_7163_;
v___y_7135_ = v_a_7153_;
v_a_7136_ = v_a_7169_;
goto v___jp_7133_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkNoConfusion___boxed(lean_object* v_declName_7185_, lean_object* v_a_7186_, lean_object* v_a_7187_, lean_object* v_a_7188_, lean_object* v_a_7189_, lean_object* v_a_7190_){
_start:
{
lean_object* v_res_7191_; 
v_res_7191_ = l_Lean_mkNoConfusion(v_declName_7185_, v_a_7186_, v_a_7187_, v_a_7188_, v_a_7189_);
lean_dec(v_a_7189_);
lean_dec_ref(v_a_7188_);
lean_dec(v_a_7187_);
lean_dec_ref(v_a_7186_);
return v_res_7191_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__4(lean_object* v_00_u03b1_7192_, lean_object* v_x_7193_, lean_object* v___y_7194_, lean_object* v___y_7195_, lean_object* v___y_7196_, lean_object* v___y_7197_){
_start:
{
lean_object* v___x_7199_; 
v___x_7199_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__4___redArg(v_x_7193_);
return v___x_7199_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__4___boxed(lean_object* v_00_u03b1_7200_, lean_object* v_x_7201_, lean_object* v___y_7202_, lean_object* v___y_7203_, lean_object* v___y_7204_, lean_object* v___y_7205_, lean_object* v___y_7206_){
_start:
{
lean_object* v_res_7207_; 
v_res_7207_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__4(v_00_u03b1_7200_, v_x_7201_, v___y_7202_, v___y_7203_, v___y_7204_, v___y_7205_);
lean_dec(v___y_7205_);
lean_dec_ref(v___y_7204_);
lean_dec(v___y_7203_);
lean_dec_ref(v___y_7202_);
return v_res_7207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_7243_; uint8_t v___x_7244_; lean_object* v___x_7245_; lean_object* v___x_7246_; 
v___x_7243_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___closed__1));
v___x_7244_ = 0;
v___x_7245_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2_));
v___x_7246_ = l_Lean_registerTraceClass(v___x_7243_, v___x_7244_, v___x_7245_);
return v___x_7246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2____boxed(lean_object* v_a_7247_){
_start:
{
lean_object* v_res_7248_; 
v_res_7248_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2_();
return v_res_7248_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_AddDecl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CompletionName(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorElim(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Subst(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Constructions_NoConfusion(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CompletionName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CtorElim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Subst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_backward_linearNoConfusionType = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_backward_linearNoConfusionType);
lean_dec_ref(res);
res = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Constructions_NoConfusion(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_AddDecl(uint8_t builtin);
lean_object* initialize_Lean_Meta_CompletionName(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_CtorElim(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Subst(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Constructions_NoConfusion(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CompletionName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_CtorElim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Subst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_NoConfusion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Constructions_NoConfusion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Constructions_NoConfusion(builtin);
}
#ifdef __cplusplus
}
#endif
